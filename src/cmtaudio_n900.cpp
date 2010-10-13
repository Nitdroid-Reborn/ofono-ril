/*
**
** Copyright (C) 2010 The NitDroid Project
** Copyright 2006, The Android Open Source Project
**
** Author: Alexey Roslyakov <alexey.roslyakov@newsycat.com>
**
** Licensed under the Apache License, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     http://www.apache.org/licenses/LICENSE-2.0
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
*/

#include <poll.h>
#include <errno.h>
#include <fcntl.h>

extern "C" {
#include "cmtspeech.h"
}

#include "cmtaudio.h"

#define LOG_TAG "CMTAUDIO"
#define vsyslog(level, format, ap) LOG_PRI_VA(level, LOG_TAG, format, ap);
#include <utils/Log.h>

namespace {

cmtspeech_t *cmtspeech;

}; // namespace anonymous

static void cmtspeechTraceHandler(int priority, const char *message, va_list args)
{
    vsyslog(ANDROID_LOG_DEBUG, message, args);
    vfprintf(stderr, message, args);
}

static void setScheduler(void)
{
    struct sched_param sched_param;
    if (sched_getparam(0, &sched_param) < 0) {
        printf("Scheduler getparam failed...\n");
        return;
    }
    sched_param.sched_priority = sched_get_priority_max(SCHED_RR);
    if (!sched_setscheduler(0, SCHED_RR, &sched_param)) {
        printf("Scheduler set to Round Robin with priority %i...\n", sched_param.sched_priority);
        fflush(stdout);
        return;
    }
    printf("!!!Scheduler set to Round Robin with priority %i FAILED!!!\n", sched_param.sched_priority);
}

/*****************************************************************************/

static void trackCallback(int event, void* user, void *info)
{
    //using namespace android;
}

/*****************************************************************************/

/*
 * cmtspeech-related part
 */
static void handleCmtspeechData()
{
    cmtspeech_buffer_t *dlbuf, *ulbuf;
    int res = cmtspeech_dl_buffer_acquire(cmtspeech, &dlbuf);
    if (res == 0) {
        LOGD("Received a DL packet (%u bytes).\n", dlbuf->count);
        if (cmtspeech_protocol_state(cmtspeech) ==
            CMTSPEECH_STATE_ACTIVE_DLUL) {
            res = cmtspeech_ul_buffer_acquire(cmtspeech, &ulbuf);
            if (res == 0) {
                if (ulbuf->pcount >= dlbuf->pcount) {
                    LOGD("Looping DL packet to UL (%u payload bytes).\n", dlbuf->pcount);
                    memcpy(ulbuf->payload, dlbuf->payload, dlbuf->pcount);
                }
                cmtspeech_ul_buffer_release(cmtspeech, ulbuf);
            }
        }
        res = cmtspeech_dl_buffer_release(cmtspeech, dlbuf);
    }
}

static int handleCmtspeechControl()
{
    cmtspeech_event_t cmtevent;
    int state_tr = CMTSPEECH_TR_INVALID;

    cmtspeech_read_event(cmtspeech, &cmtevent);
    LOGD("read cmtspeech event %d.\n", cmtevent.msg_type);

    state_tr = cmtspeech_event_to_state_transition(cmtspeech, &cmtevent);

    switch(state_tr)
    {
        case CMTSPEECH_TR_INVALID:
            LOGE("ERROR: invalid state transition\n");
            break;

        case CMTSPEECH_TR_1_CONNECTED:
        case CMTSPEECH_TR_2_DISCONNECTED:
        case CMTSPEECH_TR_3_DL_START:
        case CMTSPEECH_TR_4_DLUL_STOP:
        case CMTSPEECH_TR_5_PARAM_UPDATE:
            /* no-op */
            break;

        case CMTSPEECH_TR_6_TIMING_UPDATE:
        case CMTSPEECH_TR_7_TIMING_UPDATE:
            LOGD("WARNING: modem UL timing update ignored\n");

        case CMTSPEECH_TR_10_RESET:
        case CMTSPEECH_TR_11_UL_STOP:
        case CMTSPEECH_TR_12_UL_START:
            /* no-op */
            break;

        default:
            break;
    }

    return 0;
}

static void* mainThread(void *arg)
{
    const int cmt = 0;
    const int count = 1;
    struct pollfd fds[count];
    int pollres;

    setScheduler();

    fds[cmt].fd = cmtspeech_descriptor(cmtspeech);
    fds[cmt].events = POLLIN;

    while(true) {
        pollres = poll(fds, count, -1);

        if (pollres > 0) {
            if (fds[cmt].revents) {
                int flags = 0;
                int res = cmtspeech_check_pending(cmtspeech, &flags);

                if (res > 0) {

                    if (flags & CMTSPEECH_EVENT_DL_DATA)
                        handleCmtspeechData();

                    if (flags & CMTSPEECH_EVENT_CONTROL)
                        handleCmtspeechControl();

                }
                else {
                    LOGW("Weird: cmtspeech_check_pending res=0");
                }
            }
            else {
                LOGE("Weird: !fds[cmt].revents");
                return 0;
            }
        }
        else if (pollres < 0) {
            LOGE("poll failed: %s", strerror(errno));
        }
    }

    return 0;
}

/*****************************************************************************/

/*
 * Interface for RIL (defined in cmtaudio.h)
 */

void cmtAudioInit()
{
    LOGW("cmtAudioInit");

    // cmtspeech initialization
    cmtspeech_init();
    cmtspeech_trace_toggle(CMTSPEECH_TRACE_ERROR, true);
    cmtspeech_trace_toggle(CMTSPEECH_TRACE_INFO, true);
    cmtspeech_trace_toggle(CMTSPEECH_TRACE_STATE_CHANGE, true);
    cmtspeech_trace_toggle(CMTSPEECH_TRACE_IO, true);
    cmtspeech_trace_toggle(CMTSPEECH_TRACE_DEBUG, true);
    cmtspeech_set_trace_handler(cmtspeechTraceHandler);

    // create cmtspeech instance
    cmtspeech = cmtspeech_open();
    LOGD("cmtspeech_open returned: %p", cmtspeech);

    if (!cmtspeech) {
        LOGE("cmtspeech_open failed: %s", strerror(errno));
        return;
    }

    // create cmtaudio thread
    pthread_t thr;
    pthread_attr_t attr;

    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
    if (pthread_create(&thr, &attr, mainThread, 0) != 0) {
        LOGE("pthread_create failed: %s", strerror(errno));
        cmtspeech_close(cmtspeech);
    }
}

void cmtAudioSetMute(int mute)
{
    LOGD("setMute: %d", mute);
}

void cmtAudioSetActive(int active)
{
    LOGD("setActive: %d", active);
    if (cmtspeech) {
        static bool oldState = false;
        bool newState = !!active;
        if (newState != oldState) {
            cmtspeech_state_change_call_status(cmtspeech, newState);
            oldState = newState;
        }
        else {
            LOGE("newState==oldState, ignoring state transition");
        }
    }
}
