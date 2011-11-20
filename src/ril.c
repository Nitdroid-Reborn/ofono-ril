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

#include <telephony/ril.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <pthread.h>
#include <alloca.h>
#include <getopt.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <cutils/sockets.h>
#include <termios.h>

#include <netutils/ifc.h>

#define LOG_TAG "RIL"
#include <utils/Log.h>

#include <glib/gthread.h>
#include <dbus/dbus-glib.h>
#include <dbus/dbus-gobject.h>

#include "marshaller.h"
#include "cmtaudio.h"

#define G_VALUE_INITIALIZATOR {0,{{0}, {0}} }

typedef enum {
    SIM_ABSENT = 0,
    SIM_NOT_READY = 1,
    SIM_READY = 2, /* SIM_READY means the radio state is RADIO_STATE_SIM_READY */
    SIM_PIN = 3,
    SIM_PUK = 4,
    SIM_NETWORK_PERSONALIZATION = 5
} SIM_Status;

static GHashTable* iface_get_properties(DBusGProxy *proxy);

static void onRequest (int request, void *data, size_t datalen, RIL_Token t);
static RIL_RadioState currentState();
static int onSupports (int requestCode);
static void onCancel (RIL_Token t);
static const char *getVersion();
static int isRadioOn();
static int getCardStatus(RIL_CardStatus_v6 **pp_card_status);
static void freeCardStatus(RIL_CardStatus_v6 *p_card_status);

extern const char * requestToString(int request);

/*** Static Variables ***/
static const RIL_RadioFunctions s_callbacks = {
    RIL_VERSION,
    onRequest,
    currentState,
    onSupports,
    onCancel,
    getVersion
};

typedef struct {
    DBusGProxy      *obj;
    RIL_Call        rilCall;
    RIL_Call        *rilCallPtr;
    char            number[30];
    char            name[30];
    char            objPath[50];
} ORIL_Call;

static const gchar EMPTY[] = "";
static const gchar MODEM[] = "/isimodem";
static const gchar OFONO_SERVICE[] = "org.ofono";
static const gchar OFONO_IFACE_CALL[] = "org.ofono.VoiceCall";
static const gchar OFONO_IFACE_CALLMAN[] = "org.ofono.VoiceCallManager";
static const gchar OFONO_IFACE_SIMMANAGER[] = "org.ofono.SimManager";
static const gchar OFONO_IFACE_NETREG[] = "org.ofono.NetworkRegistration";
static const gchar OFONO_IFACE_NETOP[] = "org.ofono.NetworkOperator";
static const gchar OFONO_IFACE_SMSMAN[] = "org.ofono.MessageManager";
static const gchar OFONO_IFACE_CONNMAN[] = "org.ofono.ConnectionManager";
static const gchar OFONO_IFACE_PDC[] = "org.ofono.ConnectionContext";
static const gchar OFONO_IFACE_SUPSRV[] = "org.ofono.SupplementaryServices";
static const gchar OFONO_IFACE_RADIOSETTINGS[] = "org.ofono.RadioSettings";
static const gchar OFONO_IFACE_AUDIOSETTINGS[] = "org.ofono.AudioSettings";
static const gchar OFONO_SIGNAL_PROPERTY_CHANGED[] = "PropertyChanged";
static const gchar OFONO_SIGNAL_DISCONNECT_REASON[] = "DisconnectReason";
static const gchar OFONO_SIGNAL_IMMEDIATE_MESSAGE[] = "ImmediateMessage";
static const gchar OFONO_SIGNAL_INCOMING_MESSAGE[] = "IncomingMessage";
static const gchar OFONO_SIGNAL_CALL_ADDED[] = "CallAdded";
static const gchar OFONO_SIGNAL_CALL_REMOVED[] = "CallRemoved";
static const gchar OFONO_SIGNAL_REQUEST_RECEIVED[] = "RequestReceived";

static GSList *voiceCalls;
static GMainLoop *loop;
static DBusGConnection *connection;
static GType type_a_oa_sv, type_oa_sv, type_a_sv;
static DBusGProxy *manager, *modem, *vcm, *sim, *netreg, *radiosettings;
static DBusGProxy *sms, *connman, *pdc, *supsrv, *audioSettings;
static int goingOnline = 0;
static gboolean screenState = TRUE;
static int lastCallFailCause;
static char simIMSI[16], modemIMEI[16], modemRev[50];
static SIM_Status simStatus = SIM_NOT_READY;

/* Network Registratior */
static int netregStatus = 0, netregTech = 0, netregMode = 0; // Not registered, Unknown tech
static unsigned int netregLAC, netregCID, netregStrength;

static char netregOperator[32]; // big enought?
static char netregMCC[4], netregMNC[4];

/* DataConnectionManager */
static gboolean connmanAttached = FALSE;
// XXX not thread safe?
static char ipDataCall[16];
static const char gprsIfName[] = "gprs0";
// we always use only one context for PDC: primarycontext1
static const char *responseDataCall[3] = { "1", gprsIfName, ipDataCall };
static RIL_Token dataCallToken, poweredToken, imeiToken, modemRevToken;
static gboolean pdcActive = FALSE;
static gboolean roamingAllowed = FALSE;

static const struct RIL_Env *s_rilenv;

#define RIL_onRequestComplete(t, e, response, responselen) s_rilenv->OnRequestComplete(t,e, response, responselen)
#define RIL_onUnsolicitedResponse(a,b,c) s_rilenv->OnUnsolicitedResponse(a,b,c)
#define RIL_requestTimedCallback(a,b,c) s_rilenv->RequestTimedCallback(a,b,c)

static RIL_RadioState sState = RADIO_STATE_UNAVAILABLE;

static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t s_state_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t s_state_cond = PTHREAD_COND_INITIALIZER;

/* trigger change to this with s_state_cond */
static int s_closed = 0;

static const struct timeval TIMEVAL_SIMPOLL = {1,0};
static const struct timeval TIMEVAL_CALLSTATEPOLL = {0,500000};
static const struct timeval TIMEVAL_0 = {0,0};

static void pollSIMState (void *param);
static void setRadioState(RIL_RadioState newState);

static void hash_entry_gvalue_print(const gchar *key, GValue *val, gpointer userdata)
{
    char *str = g_strdup_value_contents(val);
    LOGD("[\"%s\"] = %s", key, str);
    free(str);
}

static RIL_CallState ofonoStateToRILState(const gchar *state)
{
    if (!g_strcmp0(state, "active")) return RIL_CALL_ACTIVE;
    if (!g_strcmp0(state, "held")) return RIL_CALL_HOLDING;
    if (!g_strcmp0(state, "dialing")) return RIL_CALL_DIALING;
    if (!g_strcmp0(state, "alerting")) return RIL_CALL_ALERTING;
    if (!g_strcmp0(state, "incoming")) return RIL_CALL_INCOMING;
    if (!g_strcmp0(state, "waiting")) return RIL_CALL_WAITING;

    LOGE("Bad callstate: %s", state);
    return (RIL_CallState) 0xffffffff;
}

/** do post- SIM ready initialization */
static void onSIMReady()
{
#if 0
    at_send_command_singleline("AT+CSMS=1", "+CSMS:", NULL);
    /*
     * Always send SMS messages directly to the TE
     *
     * mode = 1 // discard when link is reserved (link should never be
     *             reserved)
     * mt = 2   // most messages routed to TE
     * bm = 2   // new cell BM's routed to TE
     * ds = 1   // Status reports routed to TE
     * bfr = 1  // flush buffer
     */
    at_send_command("AT+CNMI=1,2,2,1,1", NULL);
#endif
}

static int objSetProperty(DBusGProxy *obj, const gchar *prop, GValue *value)
{
    GError *error = NULL;
    if (obj) {
        if ( !dbus_g_proxy_call(obj, "SetProperty", &error,
                                G_TYPE_STRING, prop,
                                G_TYPE_VALUE, value,
                                G_TYPE_INVALID,
                                G_TYPE_INVALID) )
        {
            LOGE("%s->SetProperty(%s) to %p failed: %s",
                 dbus_g_proxy_get_bus_name(obj),
                 prop, value, error->message);
        }
    }
    return error != NULL;
}

/* Toggle radio on and off (for "airplane" mode) */
static void requestRadioPower(void *data, size_t datalen, RIL_Token t)
{
    int onOff;
    int err;

    assert (datalen >= sizeof(int *));
    onOff = ((int *)data)[0];
    LOGD("requestRadioPower: %d", onOff);

    GValue value = G_VALUE_INITIALIZATOR;
    g_value_init(&value, G_TYPE_BOOLEAN);
    if (onOff == 0 /*&& sState != RADIO_STATE_OFF*/) {
        g_value_set_boolean(&value, FALSE);
        objSetProperty(modem, "Powered", &value);
        setRadioState(RADIO_STATE_OFF);
        RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
    } else if (onOff > 0 /*&& sState == RADIO_STATE_OFF*/) {

        // dirty hack to exit from airplane mode
        // relies on init.<device>.rc ability restart ofono
        // after rild process was crashed
        static int wasPowered = 0;
        if (wasPowered++)
            exit(0);

        g_value_set_boolean(&value, TRUE);
        objSetProperty(modem, "Powered", &value);
        poweredToken = t;
    }
}

static void requestDataCallList(RIL_Token *t)
{
    if (!t) {
        RIL_onUnsolicitedResponse(RIL_UNSOL_DATA_CALL_LIST_CHANGED,
                                  NULL, 0);
        return;
    }
    RIL_onRequestComplete(*t, RIL_E_GENERIC_FAILURE, NULL, 0);
}

static void requestQueryNetworkSelectionMode(
    void *data, size_t datalen, RIL_Token t)
{
    RIL_onRequestComplete(t, RIL_E_SUCCESS, &netregMode, sizeof(int));
}

static void requestQueryAvailableNetworks(
    void * data, size_t datalen, RIL_Token t)
{
    GError *error = NULL;
    unsigned int i=0;
    GHashTable* opParams;
    DBusGProxy * proxy;

    if (!netreg) {
        LOGE("Netreg proxy doesn't exist");
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }
    LOGD("proxy manager - ok");

    GPtrArray *ops = 0;
    /* Timeout after 15 minutes because Operator Scan takes looooooong */
    if (!dbus_g_proxy_call_with_timeout(netreg, "Scan", 15*60000, &error, G_TYPE_INVALID,
                                        type_a_oa_sv, &ops,
                                        G_TYPE_INVALID))
    {
        LOGE(".GetOperators failed: %s", error->message);
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }

    if (!ops || !ops->len) {
        LOGE("ops->len is empty.");
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }

    LOGD("Got an operator array : len %d", ops->len);
    char * response[ops->len*4];
    for(i=0; i < ops->len; i++){
        opParams = (GHashTable *)g_value_get_boxed(g_value_array_get_nth(ops->pdata[i], 1)); 
        GValue *name = (GValue *) g_hash_table_lookup(opParams, "Name");
        GValue *status = (GValue *) g_hash_table_lookup(opParams, "Status");
        GValue *mcc = (GValue *) g_hash_table_lookup(opParams, "MobileCountryCode");
        GValue *mnc = (GValue *) g_hash_table_lookup(opParams, "MobileNetworkCode");

        LOGD("Operator : %s, name %s", 
             (char *)g_value_get_boxed(g_value_array_get_nth(ops->pdata[i], 0)), 
             (char *)g_value_peek_pointer(name));

        char * mccmnc = NULL;
        asprintf(&mccmnc, "%s%s", 
                 (char *)g_value_peek_pointer(mcc),
                 (char *)g_value_peek_pointer(mnc));

        response[i*4] = strdup(g_value_peek_pointer(name)); 
        response[i*4 + 1] = strdup(g_value_peek_pointer(name));
        response[i*4 + 2] = mccmnc;
        response[i*4 + 3] = strdup(g_value_peek_pointer(status));
    }

    g_ptr_array_free(ops, TRUE);

    RIL_onRequestComplete(t, RIL_E_SUCCESS, response, sizeof(response));
}

static void requestRegisterNetwork(
    void * data, size_t datalen, RIL_Token t)
{
    char * mccmnc = data;
    char  objPath[50];
    GError * error = NULL;
    DBusGProxy * proxy;

    snprintf(objPath, sizeof(objPath), "%s/operator/%s", MODEM,mccmnc);
    LOGD("Object path : %s",objPath);

    proxy = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, objPath, OFONO_IFACE_NETOP);
    if (!proxy) {
        LOGE("Failed to create Manager proxy object");
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }

    if (!dbus_g_proxy_call(proxy, "Register", &error, G_TYPE_INVALID,
                           G_TYPE_INVALID))
    {
        LOGE(".Register failed: %s", error->message);
        RIL_onRequestComplete(t, RIL_E_ILLEGAL_SIM_OR_ME, NULL, 0);
        return;
    }
    
    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);

}


static void requestGetPreferredNetworkType(
    void * data, size_t datalen, RIL_Token t){
    const gchar * preferred;
    int response;
    GError * error = NULL;

    if (!radiosettings) {
        LOGE("Radiosettings proxy doesn't exist");
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }

    GHashTable *dictProps = iface_get_properties(radiosettings);
    if (!dictProps) {
        LOGD("!dictProps");
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }

    GValue *valueSettings = (GValue*) g_hash_table_lookup(dictProps, "TechnologyPreference");
    if (!valueSettings) {
        LOGE("!valueSettings");
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }
    LOGD("valueSettings-ok");
    preferred = g_value_peek_pointer(valueSettings);

    if (!g_strcmp0(preferred, "any")) {
        /* We don't have support for cdma/evdo so it's gsm/wcdma in auto mode */
        response = 3;
    } else if (!g_strcmp0(preferred, "gsm")){
        response = 1; 
    } else if (!g_strcmp0(preferred, "umts")){
        response = 2; 
    } else if (!g_strcmp0(preferred, "lte")){
        /* RIL doesn't have an option for LTE yet */
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
    }
    RIL_onRequestComplete(t, RIL_E_SUCCESS, &response, sizeof(int));
}

static void requestSetPreferredNetworkType(
    void * data, size_t datalen, RIL_Token t){

    int requested = *((int *)data);
    const gchar * preferred;
    GError * error = NULL;

    if (!radiosettings) {
        LOGE("Radiosettings proxy object doesn't exist");
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }

    if (requested == 3 || requested == 0){
        preferred = g_strdup("any");
    } else if (requested == 1){
        preferred = g_strdup("gsm");
    } else if (requested == 2){
        preferred = g_strdup("umts");
    } else {
        RIL_onRequestComplete(t, RIL_E_MODE_NOT_SUPPORTED, NULL, 0);
        return;
    }

    GValue value = G_VALUE_INITIALIZATOR;
    g_value_init(&value, G_TYPE_STRING);
    g_value_set_static_string(&value, preferred);
    /* For some reason this works but sends back an error, just ignore it*/
    objSetProperty(radiosettings, "TechnologyPreference", &value);

    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
}


static void sendCallStateChanged(void *param)
{
    RIL_onUnsolicitedResponse (
        RIL_UNSOL_RESPONSE_CALL_STATE_CHANGED,
        NULL, 0);
}

static void sendNetworkStateChanged()
{
#if 0
    RIL_onUnsolicitedResponse(
        RIL_UNSOL_RESPONSE_NETWORK_STATE_CHANGED,
        NULL, 0);
#endif
}

static void requestAnswer(RIL_Token t)
{
    GError *error = NULL;
    GSList *l;
    int found = 0;

    pthread_mutex_lock(&lock);
    for (l = voiceCalls; l; l = l->next) {
        ORIL_Call *call = (ORIL_Call*) l->data;
        if (RIL_CALL_INCOMING == call->rilCall.state) {
            found = 1;
            if (!dbus_g_proxy_call(call->obj, "Answer", &error, G_TYPE_INVALID, G_TYPE_INVALID))
                LOGE("Call->Answer failed: %s", error->message);
            RIL_onUnsolicitedResponse(RIL_UNSOL_RESPONSE_CALL_STATE_CHANGED, 0, 0);
            break;
        }
    }
    pthread_mutex_unlock(&lock);

    if (!found)
        LOGW("Can't answer: call not found");

    /* success or failure is ignored by the upper layer here.
       it will call GET_CURRENT_CALLS and determine success that way */
    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
}

static GHashTable* iface_get_properties(DBusGProxy *proxy)
{
    GError *error = NULL;
    GHashTable *dict = 0;
    if (!dbus_g_proxy_call(proxy, "GetProperties", &error, G_TYPE_INVALID,
                           dbus_g_type_get_map("GHashTable", G_TYPE_STRING, G_TYPE_VALUE), &dict,
                           G_TYPE_INVALID))
    {
        LOGE(".GetProperties failed: %s", error->message);
        return 0;
    }

    return dict;
}

static void requestGetCurrentCalls(void *data, size_t datalen, RIL_Token t)
{
    int countCalls = 0;
    GSList *l;
    RIL_Call **pp_calls;

    LOGD("requestGetCurrentCalls");
    if (!vcm) {
        LOGE("!VCM");
        RIL_onRequestComplete(t, RIL_E_SUCCESS, 0, 0);
        return;
    }

    pthread_mutex_lock(&lock);
    pp_calls = (RIL_Call **)alloca(8 * sizeof(RIL_Call *));
    for (l = voiceCalls; l; l = l->next) {
        ORIL_Call *call = (ORIL_Call*) l->data;
        pp_calls[countCalls++] = &(call->rilCall);
        //validCalls++;
    }

    RIL_onRequestComplete(t, RIL_E_SUCCESS, pp_calls,
                          countCalls * sizeof (RIL_Call *));
    pthread_mutex_unlock(&lock);
    LOGD("countCalls: %d", countCalls);

    return;
}

static void requestDial(void *data, size_t datalen, RIL_Token t)
{
    RIL_Dial *p_dial;
    const gchar *clir;
    int ret;

    p_dial = (RIL_Dial *)data;

    switch (p_dial->clir) {
        case 1: clir = "enabled"; break;   /*invocation*/
        case 2: clir = "disabled"; break;  /*suppression*/
        default:
        case 0: clir = ""; break;   /*subscription default*/
    }

    GError *error = NULL;
    GValue *value = 0;
    if (!dbus_g_proxy_call(vcm, "Dial", &error,
                           G_TYPE_STRING, p_dial->address, G_TYPE_STRING, clir,
                           G_TYPE_INVALID, G_TYPE_VALUE, value, G_TYPE_INVALID))
    {
        LOGE("VCM.Dial(%s, %s) failed: %s",
             p_dial->address, clir, error->message);
    }

    /* success or failure is ignored by the upper layer here.
       it will call GET_CURRENT_CALLS and determine success that way */
    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
}

static void requestDTMF(void *data, size_t datalen, RIL_Token t)
{
    char tones[2];
    GError *error = NULL;
    RIL_Errno res = RIL_E_SUCCESS;

    if (!vcm) {
        RIL_onRequestComplete(t, RIL_E_RADIO_NOT_AVAILABLE, NULL, 0);
        return;
    }

    // "data" is a char * containing a single character with one of 12 values: 0-9,*,#
    tones[0] = *((char*)data);
    tones[1] = '\0';

    if (!dbus_g_proxy_call(vcm, "SendTones", &error,
                           G_TYPE_STRING, tones,
                           G_TYPE_INVALID, G_TYPE_INVALID)) {
        LOGE("VoiceCallManager.SendTones failed: %s", error->message);
        res = RIL_E_GENERIC_FAILURE;
    }

    RIL_onRequestComplete(t, res, NULL, 0);
}

static void requestWriteSmsToSim(void *data, size_t datalen, RIL_Token t)
{
#if 0
    RIL_SMS_WriteArgs *p_args;
    char *cmd;
    int length;
    int err;
    ATResponse *p_response = NULL;

    p_args = (RIL_SMS_WriteArgs *)data;

    length = strlen(p_args->pdu)/2;
    asprintf(&cmd, "AT+CMGW=%d,%d", length, p_args->status);

    err = at_send_command_sms(cmd, p_args->pdu, "+CMGW:", &p_response);

    if (err != 0 || p_response->success == 0) goto error;

    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
    at_response_free(p_response);

    return;
error:
#endif
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
}

/**
 * Hangup a call
 *
 * @line   calling line index, if 0 will hangup calls with state
 * @state  hangup calls with certain state (when line is 0)
 */
static void requestHangup(RIL_Token t, int line, int state)
{
    GSList *l;
    int found = 0;

    // 3GPP 22.030 6.5.5
    // "Releases a specific active call X"
    // ril.h: Hang up a specific line (like AT+CHLD=1x)

    pthread_mutex_lock(&lock);
    for (l = voiceCalls; l; l = l->next) {
        ORIL_Call *call = (ORIL_Call*) l->data;
        if (line == call->rilCall.index || (!line && (RIL_CallState) state == call->rilCall.state)) {
            found = 1;
            GError *error = NULL;
            if (!dbus_g_proxy_call(call->obj, "Hangup", &error, G_TYPE_INVALID, G_TYPE_INVALID))
                LOGE("VoiceCall.Hangup failed for line %d: %s", line, error->message);
            RIL_onUnsolicitedResponse(RIL_UNSOL_RESPONSE_CALL_STATE_CHANGED, 0, 0);
            break;
        }
    }
    pthread_mutex_unlock(&lock);

    if (!found)
        LOGW("requestHangup failed: line/state %d/%d not found", line, state);

    /* success or failure is ignored by the upper layer here.
       it will call GET_CURRENT_CALLS and determine success that way */
    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
}

static void requestSignalStrength(void *data, size_t datalen, RIL_Token t)
{
    RIL_SignalStrength_v6 st;
    memset(&st, sizeof(st), 0);

    int strength = (netregStrength*31)/100;
    if (strength == 0)
        strength = 99;

    if (t)
        RIL_onRequestComplete(t, RIL_E_SUCCESS, &st, sizeof(st));
    else
        RIL_onUnsolicitedResponse(RIL_UNSOL_SIGNAL_STRENGTH, &st, sizeof(st));
}

static void requestGPRSRegistrationState(void *data, size_t datalen, RIL_Token t)
{
    char *responseStr[4];
    memset(responseStr, sizeof(responseStr), 0);

    switch(netregStatus) {
        case 1:
        case 5:
            asprintf(&responseStr[0], "%d", connmanAttached ? 1 : 0);
            asprintf(&responseStr[1], "%x", netregLAC);
            asprintf(&responseStr[2], "%x", netregCID);
            asprintf(&responseStr[3], "%d", netregTech);
            LOGD("requestGPRSRegistrationState success");
            RIL_onRequestComplete(t, RIL_E_SUCCESS, responseStr, sizeof(responseStr));
            break;
        default:
            RIL_onRequestComplete(t, RIL_E_RADIO_NOT_AVAILABLE, NULL, 0);
    }
}

static void requestRegistrationState(void *data, size_t datalen, RIL_Token t)
{
    static char *responseStr[14];
    memset(responseStr, sizeof(responseStr), 0);

    if (netregStatus > 0) {
        asprintf(&responseStr[0], "%d", netregStatus);
        asprintf(&responseStr[1], "%x", netregLAC);
        asprintf(&responseStr[2], "%x", netregCID);
        asprintf(&responseStr[3], "%d", netregTech);
        LOGD("requestRegistrationState success");
        RIL_onRequestComplete(t, RIL_E_SUCCESS, responseStr, sizeof(responseStr));
        for (unsigned i = 0; i < sizeof(responseStr)/sizeof(char*); i++)
            if (responseStr[i]) free(responseStr[i]);
    }
    else
        RIL_onRequestComplete(t, RIL_E_RADIO_NOT_AVAILABLE, NULL, 0);
}

static void requestOperator(void *data, size_t datalen, RIL_Token t)
{
    char *response[3];
    char mccMnc[8];
    
    if (netregStatus > 0) {
        response[0] = netregOperator;
        response[1] = netregOperator;
        response[2] = mccMnc;
        snprintf(mccMnc, sizeof(mccMnc), "%s%s", netregMCC, netregMNC);
        RIL_onRequestComplete(t, RIL_E_SUCCESS, response, sizeof(response));
    }
    else
        RIL_onRequestComplete(t, RIL_E_RADIO_NOT_AVAILABLE, NULL, 0);
}

static void requestSendSMS(void *data, size_t datalen, RIL_Token t)
{
    if (!sms) {
        RIL_onRequestComplete(t, RIL_E_RADIO_NOT_AVAILABLE, NULL, 0);
        return;
    }

    const char *smsc = ((const char **)data)[0];
    const char *pdu = ((const char **)data)[1];
    LOGD("requestSendSMS, %s, %s", smsc, pdu);

    GError *error = NULL;
    GValue *value = 0;

    int res = dbus_g_proxy_call(sms, "SendPdu",
                                &error,
                                G_TYPE_STRING, pdu, G_TYPE_INVALID,
                                G_TYPE_VALUE, value, G_TYPE_INVALID);

    /* FIXME fill in messageRef and ackPDU */
    RIL_SMS_Response response;
    memset(&response, 0, sizeof(response));
    RIL_onRequestComplete(t, RIL_E_SUCCESS, &response, sizeof(response));
}

static void requestSetupDataCall(void *data, size_t datalen, RIL_Token t)
{
    if (!connmanAttached) {
        LOGW("requestSetupDataCall exit, connman is not in Attached state");
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }

    gboolean res = TRUE;
    const char *apn  = ((const char **)data)[2];
    const char *user = ((const char **)data)[3];
    const char *pswd = ((const char **)data)[4];
    LOGD("requestSetupDataCall, %s, %s, %s", apn, user, pswd);

    // APN
    {
        GValue value = G_VALUE_INITIALIZATOR;
        g_value_init(&value, G_TYPE_STRING);
        g_value_set_static_string(&value, apn);
        objSetProperty(pdc, "AccessPointName", &value);
    }

    // Username
    {
        GValue value = G_VALUE_INITIALIZATOR;
        g_value_init(&value, G_TYPE_STRING);
        g_value_set_static_string(&value, user);
        objSetProperty(pdc, "Username", &value);
    }

    // Password
    {
        GValue value = G_VALUE_INITIALIZATOR;
        g_value_init(&value, G_TYPE_STRING);
        g_value_set_static_string(&value, pswd);
        objSetProperty(pdc, "Password", &value);
    }

    // will be used later, after receiving PropertyChanged signal
    ipDataCall[0] = 0;
    dataCallToken = t;

    // Set Active property
    {
        GValue value = G_VALUE_INITIALIZATOR;
        g_value_init(&value, G_TYPE_BOOLEAN);
        g_value_set_boolean(&value, TRUE);
        objSetProperty(pdc, "Active", &value);
    }

    LOGW("Data connection setup: success");
    //RIL_onRequestComplete(t, RIL_E_SUCCESS, response, sizeof(response));
    //RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
}

static void requestDeactivateDataCall(void *data, size_t datalen, RIL_Token t)
{
    {
        GValue value = G_VALUE_INITIALIZATOR;
        g_value_init(&value, G_TYPE_BOOLEAN);
        g_value_set_boolean(&value, FALSE);
        objSetProperty(pdc, "Active", &value);
    }
    RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
}

static int setupIP()
{
    in_addr_t ip = inet_addr(responseDataCall[2]);
    if (ifc_set_addr(gprsIfName, ip)) {
        LOGE("Can't set IP address: %s", strerror(errno));
        return 0;
    }
    if (ifc_up(gprsIfName)) {
        LOGE("Can't UP network interface: %s", strerror(errno));
        return 0;
    }
    if (ifc_set_default_route(gprsIfName, ip)) {
        LOGE("Can't set default route: %s", strerror(errno));
        return 0;
    }
    return 1;
}

static void getIP()
{
    LOGD("getIP called");

    // Get IP address of new connection
    GHashTable *dictProps = iface_get_properties(pdc);
    if (!dictProps) {
        LOGD("!dictProps");
        goto error;
    }

    GValue *valueSettings = (GValue*) g_hash_table_lookup(dictProps, "Settings");
    if (!valueSettings) {
        LOGE("!valueSettings");
        goto error;
    }
    LOGD("valueSettings-ok");
    GHashTable *dictSettings = (GHashTable*) g_value_peek_pointer(valueSettings);
    GValue *value = (GValue *) g_hash_table_lookup(dictSettings, "Address");
    LOGD("Address: %p", value);
    if (value && g_value_peek_pointer(value)) {
        strncpy(ipDataCall, g_value_peek_pointer(value), sizeof(ipDataCall));
        LOGW("IP Address=%s", ipDataCall);

        if (ifc_init() != 0) {
            LOGE("ifc_init failed");
            goto error;
        }

        if (setupIP()) {
            RIL_onRequestComplete(dataCallToken, RIL_E_SUCCESS, responseDataCall, sizeof(responseDataCall));
            ifc_close();
            return;
        }
        ifc_close();
    }
    else
        LOGE("No IP Address in Properties:Settings");

error:
    LOGE("getIP: ERROR!!!");
    RIL_onRequestComplete(dataCallToken, RIL_E_GENERIC_FAILURE, NULL, 0);
}

static void requestSMSAcknowledge(void *data, size_t datalen, RIL_Token t)
{
#if 0
    int ackSuccess;
    int err;

    ackSuccess = ((int *)data)[0];

    if (ackSuccess == 1) {
        err = at_send_command("AT+CNMA=1", NULL);
    } else if (ackSuccess == 0)  {
        err = at_send_command("AT+CNMA=2", NULL);
    } else {
        LOGE("unsupported arg to RIL_REQUEST_SMS_ACKNOWLEDGE\n");
        goto error;
    }

    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
error:
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
#endif
    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
}

static void  requestSIM_IO(void *data, size_t datalen, RIL_Token t)
{
#if 0
    ATResponse *p_response = NULL;
    RIL_SIM_IO_Response sr;
    int err;
    char *cmd = NULL;
    RIL_SIM_IO *p_args;
    char *line;

    memset(&sr, 0, sizeof(sr));

    p_args = (RIL_SIM_IO *)data;

    /* FIXME handle pin2 */

    if (p_args->data == NULL) {
        asprintf(&cmd, "AT+CRSM=%d,%d,%d,%d,%d",
                 p_args->command, p_args->fileid,
                 p_args->p1, p_args->p2, p_args->p3);
    } else {
        asprintf(&cmd, "AT+CRSM=%d,%d,%d,%d,%d,%s",
                 p_args->command, p_args->fileid,
                 p_args->p1, p_args->p2, p_args->p3, p_args->data);
    }

    err = at_send_command_singleline(cmd, "+CRSM:", &p_response);

    if (err < 0 || p_response->success == 0) {
        goto error;
    }

    line = p_response->p_intermediates->line;

    err = at_tok_start(&line);
    if (err < 0) goto error;

    err = at_tok_nextint(&line, &(sr.sw1));
    if (err < 0) goto error;

    err = at_tok_nextint(&line, &(sr.sw2));
    if (err < 0) goto error;

    if (at_tok_hasmore(&line)) {
        err = at_tok_nextstr(&line, &(sr.simResponse));
        if (err < 0) goto error;
    }

    RIL_onRequestComplete(t, RIL_E_SUCCESS, &sr, sizeof(sr));
    at_response_free(p_response);
    free(cmd);

    return;
error:
#endif
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
}

static void  requestEnterSimPin(void*  data, size_t  datalen, RIL_Token  t)
{
#if 0
    ATResponse   *p_response = NULL;
    int           err;
    char*         cmd = NULL;
    const char**  strings = (const char**)data;;

    if ( datalen == sizeof(char*) ) {
        asprintf(&cmd, "AT+CPIN=%s", strings[0]);
    } else if ( datalen == 2*sizeof(char*) ) {
        asprintf(&cmd, "AT+CPIN=%s,%s", strings[0], strings[1]);
    } else
        goto error;

    err = at_send_command_singleline(cmd, "+CPIN:", &p_response);
    free(cmd);

    if (err < 0 || p_response->success == 0) {
  error:
        RIL_onRequestComplete(t, RIL_E_PASSWORD_INCORRECT, NULL, 0);
    } else {
        RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
    }
    at_response_free(p_response);
#endif
    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
}

static char getSupplementaryServicesState()
{
    char res = '0'; // fallback to USSD-Notify
    GHashTable *dictProps = iface_get_properties(supsrv);
    if (dictProps) {
        GValue *value = (GValue*) g_hash_table_lookup(dictProps, "State");
        if (value) {
            if (!strcmp(g_value_peek_pointer(value), "user-response"))
                res = '1';
        }
        g_hash_table_destroy(dictProps);
    }

    LOGD("srv_ussd_state: %c", res);
    return res;
}

static void  requestSendUSSD(void *data, size_t datalen, RIL_Token t)
{
    const char *ussdRequest = (char *)(data);

    if (!supsrv) {
        RIL_onRequestComplete(t, RIL_E_RADIO_NOT_AVAILABLE, NULL, 0);
        return;
    }

    // get current SupplementaryServices state
    char state = getSupplementaryServicesState();

    GError *error = NULL;
    char *request = 0;
    char *strValue = 0;
    int res;

    // If USSD session is active in USSD-Response state,
    // we use Respond method instead of Initiate
    if (state == '1') {
      res = dbus_g_proxy_call(supsrv, "Respond",
                              &error,
                              G_TYPE_STRING, ussdRequest, G_TYPE_INVALID,
                              G_TYPE_STRING, &strValue, G_TYPE_INVALID);
      if (!res) {
          LOGE("supsrv.Respond(%s) failed: %s",
               ussdRequest, error->message);
          RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
          return;
      }
    }
    else {
        GValue value = G_VALUE_INITIALIZATOR;
        res = dbus_g_proxy_call(supsrv, "Initiate",
                                &error,
                                G_TYPE_STRING, ussdRequest, G_TYPE_INVALID,
                                G_TYPE_STRING, &request,
                                G_TYPE_VALUE, &value, G_TYPE_INVALID);
        if (res) {
            strValue = g_strdup(g_value_get_string(&value));
            g_value_unset(&value);
        }
        else {
            LOGE("supsrv.Initiate(%s) failed: %s",
                 ussdRequest, error->message);
            RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
            return;
        }
    }

    if (strValue) {
        LOGD("USSD response from network: %s", strValue);
        RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);

        // Get SupplementaryServices state again
        char supSrvState[] = {0, 0};
        supSrvState[0] = getSupplementaryServicesState();

        char *unsResp[2];
        unsResp[0] = supSrvState;
        unsResp[1] = strValue;
        RIL_onUnsolicitedResponse(RIL_UNSOL_ON_USSD, unsResp, sizeof(unsResp));

        if (request) g_free(request);
        g_free(strValue);
    }
}

static void requestCancelUSSD(void * data, size_t datalen, RIL_Token t)
{
    RIL_Errno res = RIL_E_GENERIC_FAILURE;

    if (supsrv) {
        GError *error = NULL;
        if (!dbus_g_proxy_call(supsrv, "Cancel", &error,
                               G_TYPE_INVALID, G_TYPE_INVALID))
        {
            LOGE("supsrv.Cancel() failed: %s", error->message);
        }
        else {
            res = RIL_E_SUCCESS;
        }
    }

    RIL_onRequestComplete(t, res, NULL, 0);
}

static void requestGetRoamingPreference(void * data, size_t datalen, RIL_Token t)
{
    int response;
    if (roamingAllowed)
        response = 2;
    else
        response = 0;

    RIL_onRequestComplete(t, RIL_E_SUCCESS, &response, sizeof(int));
}

static void requestSetRoamingPreference(void * data, size_t datalen, RIL_Token t)
{
    int requested = *((int *)data);
    gboolean roaming;
    GError * error = NULL;

    if (!connman) {
        LOGE("Connman proxy object doesn't exist");
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }

    if(requested == 0 || requested == 1)
        roaming = FALSE;
    else
        roaming = TRUE;

    GValue value = G_VALUE_INITIALIZATOR;
    g_value_init(&value, G_TYPE_BOOLEAN);
    g_value_set_boolean(&value, roaming);

    if(objSetProperty(connman, "RoamingAllowed", &value)){
        RIL_onRequestComplete(t,RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }

    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);

}

static void requestBasebandVersion(void * data, size_t datalen, RIL_Token t)
{
    GHashTable* props;
    GValue* value;
    if (modemRev[0] == '\0') {
        /* We don't have the revision, lets save the token and reply when we have the version */
        modemRevToken = t;
    } 
}

static void setFastDormancy(gboolean state) {
    GError * error = NULL;

    if (!radiosettings) {
        LOGE("Radiosettings proxy object doesn't exist");
        return;
    }

    GValue value = G_VALUE_INITIALIZATOR;
    g_value_init(&value, G_TYPE_BOOLEAN);
    g_value_set_boolean(&value, state);

    if(objSetProperty(radiosettings, "FastDormancy", &value)){
        LOGE("Couldn't set fast dormancy");
        return;
    }

}

/*** Callback methods from the RIL library to us ***/

/**
 * Call from RIL to us to make a RIL_REQUEST
 *
 * Must be completed with a call to RIL_onRequestComplete()
 *
 * RIL_onRequestComplete() may be called from any thread, before or after
 * this function returns.
 *
 * Will always be called from the same thread, so returning here implies
 * that the radio is ready to process another command (whether or not
 * the previous command has completed).
 */
static void
onRequest (int request, void *data, size_t datalen, RIL_Token t)
{
    int err;

    LOGD("onRequest: %s", requestToString(request));

    /* Ignore all requests except RIL_REQUEST_GET_SIM_STATUS
     * when RADIO_STATE_UNAVAILABLE.
     */
    if (sState == RADIO_STATE_UNAVAILABLE
        && request != RIL_REQUEST_GET_SIM_STATUS
        ) {
        RIL_onRequestComplete(t, RIL_E_RADIO_NOT_AVAILABLE, NULL, 0);
        return;
    }

    /* Ignore all non-power requests when RADIO_STATE_OFF
     * (except RIL_REQUEST_GET_SIM_STATUS and RIL_REQUEST_GET_IMEI)
     */
    if (sState == RADIO_STATE_OFF
        && !(request == RIL_REQUEST_RADIO_POWER
             || request == RIL_REQUEST_GET_SIM_STATUS
             || request == RIL_REQUEST_GET_IMEI
             || request == RIL_REQUEST_GET_IMEISV
             || request == RIL_REQUEST_BASEBAND_VERSION)
        ) {
        RIL_onRequestComplete(t, RIL_E_RADIO_NOT_AVAILABLE, NULL, 0);
        return;
    }

    switch (request) {
        case RIL_REQUEST_GET_SIM_STATUS: {
            RIL_CardStatus_v6 *p_card_status;
            char *p_buffer;
            int buffer_size;

            int result = getCardStatus(&p_card_status);
            if (result == RIL_E_SUCCESS) {
                p_buffer = (char *)p_card_status;
                buffer_size = sizeof(*p_card_status);
            } else {
                p_buffer = NULL;
                buffer_size = 0;
            }
            RIL_onRequestComplete(t, result, p_buffer, buffer_size);
            freeCardStatus(p_card_status);
            break;
        }
        case RIL_REQUEST_GET_CURRENT_CALLS:
            requestGetCurrentCalls(data, datalen, t);
            break;
        case RIL_REQUEST_SET_MUTE:
            cmtAudioSetMute(*((int *)data));
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
        case RIL_REQUEST_DIAL:
            requestDial(data, datalen, t);
            break;
        case RIL_REQUEST_HANGUP:
            requestHangup(t, *((int *)data), -1);
            break;
        case RIL_REQUEST_HANGUP_WAITING_OR_BACKGROUND:
            // 3GPP 22.030 6.5.5
            // "Releases all held calls or sets User Determined User Busy
            //  (UDUB) for a waiting call."
            //at_send_command("AT+CHLD=0", NULL);
            requestHangup(t, 0, RIL_CALL_INCOMING); // FIXME
            break;
        case RIL_REQUEST_HANGUP_FOREGROUND_RESUME_BACKGROUND:
            // 3GPP 22.030 6.5.5
            // "Releases all active calls (if any exist) and accepts
            //  the other (held or waiting) call."
            //at_send_command("AT+CHLD=1", NULL);
            requestHangup(t, 0, RIL_CALL_ACTIVE); // FIXME
            break;
        case RIL_REQUEST_SWITCH_WAITING_OR_HOLDING_AND_ACTIVE:
            // 3GPP 22.030 6.5.5
            // "Places all active calls (if any exist) on hold and accepts
            //  the other (held or waiting) call."
            //at_send_command("AT+CHLD=2", NULL);

            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
        case RIL_REQUEST_ANSWER:
            requestAnswer(t);
            break;
        case RIL_REQUEST_CONFERENCE:
            // 3GPP 22.030 6.5.5
            // "Adds a held call to the conversation"
            //at_send_command("AT+CHLD=3", NULL);

            /* success or failure is ignored by the upper layer here.
               it will call GET_CURRENT_CALLS and determine success that way */
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
        case RIL_REQUEST_UDUB:
            /* user determined user busy */
            /* sometimes used: ATH */
            //at_send_command("ATH", NULL);

            /* success or failure is ignored by the upper layer here.
               it will call GET_CURRENT_CALLS and determine success that way */
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;

        case RIL_REQUEST_SEPARATE_CONNECTION:
            {
#if 0
                char  cmd[12];
                int   party = ((int*)data)[0];

                // Make sure that party is in a valid range.
                // (Note: The Telephony middle layer imposes a range of 1 to 7.
                // It's sufficient for us to just make sure it's single digit.)
                if (party > 0 && party < 10) {
                    sprintf(cmd, "AT+CHLD=2%d", party);
                    at_send_command(cmd, NULL);
                    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
                } else {
                    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
                }
#endif
                RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
            }
            break;

        case RIL_REQUEST_SCREEN_STATE:
            screenState = (*((int *)data) == 1) ? TRUE : FALSE;
            setFastDormancy(!screenState);
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
        case RIL_REQUEST_SIGNAL_STRENGTH:
            requestSignalStrength(data, datalen, t);
            break;
        case RIL_REQUEST_VOICE_REGISTRATION_STATE:
            requestRegistrationState(data, datalen, t);
            break;
        case RIL_REQUEST_DATA_REGISTRATION_STATE:
            requestGPRSRegistrationState(data, datalen, t);
            break;
        case RIL_REQUEST_OPERATOR:
            requestOperator(data, datalen, t);
            break;
        case RIL_REQUEST_RADIO_POWER:
            requestRadioPower(data, datalen, t);
            break;
        case RIL_REQUEST_DTMF:
        case RIL_REQUEST_DTMF_START:
            requestDTMF(data, datalen, t);
            break;
        case RIL_REQUEST_SEND_SMS:
            requestSendSMS(data, datalen, t);
            break;
        case RIL_REQUEST_SETUP_DATA_CALL:
            requestSetupDataCall(data, datalen, t);
            break;
        case RIL_REQUEST_DEACTIVATE_DATA_CALL:
            requestDeactivateDataCall(data, datalen, t);
            break;
        case RIL_REQUEST_SMS_ACKNOWLEDGE:
            requestSMSAcknowledge(data, datalen, t);
            break;

        case RIL_REQUEST_GET_IMSI:
            RIL_onRequestComplete(t, RIL_E_SUCCESS,
                                  simIMSI, sizeof(char *));
            break;
        case RIL_REQUEST_GET_IMEI:
            // report IMEI if we already have it
            if (modemIMEI[0]) {
                RIL_onRequestComplete(t, RIL_E_SUCCESS,
                                      modemIMEI, sizeof(char *));
            }
            else
                imeiToken = t;
            break;

        case RIL_REQUEST_GET_IMEISV:
            RIL_onRequestComplete(t, RIL_E_SUCCESS,
                                  "02", sizeof(char *));
            break;

        case RIL_REQUEST_BASEBAND_VERSION:
            requestBasebandVersion(data, datalen, t);
            break;

        case RIL_REQUEST_SIM_IO:
            requestSIM_IO(data,datalen,t);
            break;

        case RIL_REQUEST_SEND_USSD:
            requestSendUSSD(data, datalen, t);
            break;

        case RIL_REQUEST_CANCEL_USSD:
            requestCancelUSSD(data, datalen, t);
            break;

        case RIL_REQUEST_SET_NETWORK_SELECTION_AUTOMATIC:
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
        case RIL_REQUEST_SET_NETWORK_SELECTION_MANUAL:
            requestRegisterNetwork(data, datalen, t);
            break;
        case RIL_REQUEST_DATA_CALL_LIST:
            requestDataCallList(&t);
            break;

        case RIL_REQUEST_QUERY_NETWORK_SELECTION_MODE:
            requestQueryNetworkSelectionMode(data, datalen, t);
            break;

        case RIL_REQUEST_QUERY_AVAILABLE_NETWORKS:
            requestQueryAvailableNetworks(data, datalen, t);
            break;

        case RIL_REQUEST_GET_PREFERRED_NETWORK_TYPE:
            requestGetPreferredNetworkType(data, datalen, t);
            break;
        case RIL_REQUEST_SET_PREFERRED_NETWORK_TYPE:
            requestSetPreferredNetworkType(data, datalen, t);
            break;

        case RIL_REQUEST_OEM_HOOK_RAW:
            // echo back data
            RIL_onRequestComplete(t, RIL_E_SUCCESS, data, datalen);
            break;


        case RIL_REQUEST_OEM_HOOK_STRINGS:
            {
                int i;
                const char ** cur;

                LOGD("got OEM_HOOK_STRINGS: 0x%8p %lu", data, (long)datalen);


                for (i = (datalen / sizeof (char *)), cur = (const char **)data ;
                     i > 0 ; cur++, i --) {
                    LOGD("> '%s'", *cur);
                }

                // echo back strings
                RIL_onRequestComplete(t, RIL_E_SUCCESS, data, datalen);
                break;
            }

        case RIL_REQUEST_WRITE_SMS_TO_SIM:
            requestWriteSmsToSim(data, datalen, t);
            break;

        case RIL_REQUEST_DELETE_SMS_ON_SIM:
            RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
            break;

        case RIL_REQUEST_ENTER_SIM_PIN:
        case RIL_REQUEST_ENTER_SIM_PUK:
        case RIL_REQUEST_ENTER_SIM_PIN2:
        case RIL_REQUEST_ENTER_SIM_PUK2:
        case RIL_REQUEST_CHANGE_SIM_PIN:
        case RIL_REQUEST_CHANGE_SIM_PIN2:
            requestEnterSimPin(data, datalen, t);
            break;
        case RIL_REQUEST_CDMA_QUERY_ROAMING_PREFERENCE:
            requestGetRoamingPreference(data, datalen, t);
            break;

        case RIL_REQUEST_CDMA_SET_ROAMING_PREFERENCE:
            requestSetRoamingPreference(data, datalen, t);
            break;

        default:
            RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
            break;
    }
}

/**
 * Synchronous call from the RIL to us to return current radio state.
 * RADIO_STATE_UNAVAILABLE should be the initial state.
 */
static RIL_RadioState
currentState()
{
    return sState;
}
/**
 * Call from RIL to us to find out whether a specific request code
 * is supported by this implementation.
 *
 * Return 1 for "supported" and 0 for "unsupported"
 */

static int
onSupports (int requestCode)
{
    //@@@ todo

    return 1;
}

static void onCancel (RIL_Token t)
{
    //@@@todo

}

static const char * getVersion(void)
{
    return "NITDroid ofono-ril 0.0.9";
}

void
setRadioState(RIL_RadioState newState)
{
    RIL_RadioState oldState;

    pthread_mutex_lock(&s_state_mutex);

    oldState = sState;

    if (s_closed > 0) {
        // If we're closed, the only reasonable state is
        // RADIO_STATE_UNAVAILABLE
        // This is here because things on the main thread
        // may attempt to change the radio state after the closed
        // event happened in another thread
        newState = RADIO_STATE_UNAVAILABLE;
    }

    if (sState != newState || s_closed > 0) {
        sState = newState;

        pthread_cond_broadcast (&s_state_cond);
    }

    pthread_mutex_unlock(&s_state_mutex);


    /* do these outside of the mutex */
    /*if (sState != oldState)*/ {
        RIL_onUnsolicitedResponse (RIL_UNSOL_RESPONSE_RADIO_STATE_CHANGED,
                                   NULL, 0);

        /* FIXME onSimReady() and onRadioPowerOn() cannot be called
         * from the AT reader thread
         * Currently, this doesn't happen, but if that changes then these
         * will need to be dispatched on the request thread
         */
        if (sState == RADIO_STATE_SIM_READY) {
            onSIMReady();
        } else if (sState == RADIO_STATE_SIM_NOT_READY) {
            pollSIMState(NULL);
        }
    }
}

/** Returns SIM_NOT_READY on error */
static SIM_Status 
getSIMStatus()
{
    if (sState == RADIO_STATE_OFF || sState == RADIO_STATE_UNAVAILABLE) {
        return SIM_NOT_READY;
    }

    return simStatus;
}


/**
 * Get the current card status.
 *
 * This must be freed using freeCardStatus.
 * @return: On success returns RIL_E_SUCCESS
 */
static int getCardStatus(RIL_CardStatus_v6 **pp_card_status) {
    static RIL_AppStatus app_status_array[] = {
        // SIM_ABSENT = 0
        { RIL_APPTYPE_UNKNOWN, RIL_APPSTATE_UNKNOWN, RIL_PERSOSUBSTATE_UNKNOWN,
          NULL, NULL, 0, RIL_PINSTATE_UNKNOWN, RIL_PINSTATE_UNKNOWN },
        // SIM_NOT_READY = 1
        { RIL_APPTYPE_SIM, RIL_APPSTATE_DETECTED, RIL_PERSOSUBSTATE_UNKNOWN,
          NULL, NULL, 0, RIL_PINSTATE_UNKNOWN, RIL_PINSTATE_UNKNOWN },
        // SIM_READY = 2
        { RIL_APPTYPE_SIM, RIL_APPSTATE_READY, RIL_PERSOSUBSTATE_READY,
          NULL, NULL, 0, RIL_PINSTATE_UNKNOWN, RIL_PINSTATE_UNKNOWN },
        // SIM_PIN = 3
        { RIL_APPTYPE_SIM, RIL_APPSTATE_PIN, RIL_PERSOSUBSTATE_UNKNOWN,
          NULL, NULL, 0, RIL_PINSTATE_ENABLED_NOT_VERIFIED, RIL_PINSTATE_UNKNOWN },
        // SIM_PUK = 4
        { RIL_APPTYPE_SIM, RIL_APPSTATE_PUK, RIL_PERSOSUBSTATE_UNKNOWN,
          NULL, NULL, 0, RIL_PINSTATE_ENABLED_BLOCKED, RIL_PINSTATE_UNKNOWN },
        // SIM_NETWORK_PERSONALIZATION = 5
        { RIL_APPTYPE_SIM, RIL_APPSTATE_SUBSCRIPTION_PERSO, RIL_PERSOSUBSTATE_SIM_NETWORK,
          NULL, NULL, 0, RIL_PINSTATE_ENABLED_NOT_VERIFIED, RIL_PINSTATE_UNKNOWN }
    };
    RIL_CardState card_state;
    int num_apps;

    int sim_status = getSIMStatus();
    if (sim_status == SIM_ABSENT) {
        card_state = RIL_CARDSTATE_ABSENT;
        num_apps = 0;
    } else {
        card_state = RIL_CARDSTATE_PRESENT;
        num_apps = 1;
    }

    // Allocate and initialize base card status.
    RIL_CardStatus_v6 *p_card_status = malloc(sizeof(RIL_CardStatus_v6));
    p_card_status->card_state = card_state;
    p_card_status->universal_pin_state = RIL_PINSTATE_UNKNOWN;
    p_card_status->gsm_umts_subscription_app_index = RIL_CARD_MAX_APPS;
    p_card_status->cdma_subscription_app_index = RIL_CARD_MAX_APPS;
    p_card_status->num_applications = num_apps;

    // Initialize application status
    int i;
    for (i = 0; i < RIL_CARD_MAX_APPS; i++) {
        p_card_status->applications[i] = app_status_array[SIM_ABSENT];
    }

    // Pickup the appropriate application status
    // that reflects sim_status for gsm.
    if (num_apps != 0) {
        // Only support one app, gsm
        p_card_status->num_applications = 1;
        p_card_status->gsm_umts_subscription_app_index = 0;

        // Get the correct app status
        p_card_status->applications[0] = app_status_array[sim_status];
    }

    *pp_card_status = p_card_status;
    return RIL_E_SUCCESS;
}

/**
 * Free the card status returned by getCardStatus
 */
static void freeCardStatus(RIL_CardStatus_v6 *p_card_status) {
    free(p_card_status);
}

/**
 * SIM ready means any commands that access the SIM will work, including:
 *  AT+CPIN, AT+CSMS, AT+CNMI, AT+CRSM
 *  (all SMS-related commands)
 */

static void pollSIMState (void *param)
{
    setRadioState(!!sim ? RADIO_STATE_SIM_READY : RADIO_STATE_SIM_NOT_READY);
}

static void waitForClose()
{
    pthread_mutex_lock(&s_state_mutex);

    while (s_closed == 0) {
        pthread_cond_wait(&s_state_cond, &s_state_mutex);
    }

    pthread_mutex_unlock(&s_state_mutex);
}

static void* mainLoop(void *param)
{
    LOGD("Running main loop");
    g_main_loop_run(loop);
    LOGE("Main loop ended");

    return 0;
}

static void callPropertyChanged(DBusGProxy *proxy, const gchar *property,
                                GValue *value, gpointer priv)
{
    int callIndex = (int) priv;
    LOGD("callPropertyChanged(%d): %s->%s", callIndex, property, (char*)g_value_peek_pointer(value));

    if (!g_strcmp0(property, "State")) {
        GSList *l;
        int found = 0;
        RIL_CallState state = 0xffffffff;

        pthread_mutex_lock(&lock);
        for (l = voiceCalls; l; l = l->next) {
            ORIL_Call *call = (ORIL_Call*) l->data;
            if (proxy == call->obj) {
                found = 1;
                state = ofonoStateToRILState(g_value_peek_pointer(value));
                call->rilCall.state = state;
                break;
            }
        }
        pthread_mutex_unlock(&lock);

        // for disconnected calls we'll send it on vcm->CallRemoved signal
        if (0xffffffff != (unsigned int)state)
            RIL_onUnsolicitedResponse(RIL_UNSOL_RESPONSE_CALL_STATE_CHANGED, NULL, 0);

        if (!found)
            LOGW("BUG? Call not found");
    }

    g_value_unset(value);
}

static void callDisconnectReason(DBusGProxy *proxy, const gchar *reason,
                                 gpointer priv)
{
    LOGW("callDisconnectReason: %s", reason);
}

static void vcmPropertyChanged(DBusGProxy *proxy, const gchar *property,
                               GValue *value, gpointer user_data)
{
    // XXX
    LOGW("vcm_property_changed %s->%s", property, g_strdup_value_contents(value));

    if (!g_strcmp0("Calls", property)) {
        GPtrArray *callArr = g_value_peek_pointer(value);
        if (!callArr->len) {
            LOGD("Calls is empty. Disconnected?");
        }

        RIL_onUnsolicitedResponse(RIL_UNSOL_RESPONSE_CALL_STATE_CHANGED,
                                  NULL, 0);
    }
    g_value_unset(value);
}

static void vcmCallAdded(DBusGProxy *proxy, const char *objPath,
                         GHashTable *prop, gpointer priv)
{
    LOGD("vcmCallAdded: %s", objPath);
    g_hash_table_foreach(prop, (GHFunc)hash_entry_gvalue_print, NULL);

    ORIL_Call *call = malloc(sizeof(ORIL_Call));
    if (!call) {
        LOGE("vcmCallAdded failed: ENOMEM");
        return;
    }

    memset(call, sizeof(ORIL_Call), 0);
    //call->rilCallPtr = &call->rilCall;
    strncpy(call->objPath, objPath, sizeof(call->objPath));

    const GValue *number = g_hash_table_lookup(prop, "LineIdentification");
    strncpy(call->number, g_value_peek_pointer(number), sizeof(call->number));

    const GValue *name = g_hash_table_lookup(prop, "Name");
    strncpy(call->name, g_value_peek_pointer(name), sizeof(call->name));

    const GValue *state = g_hash_table_lookup(prop, "State");
    call->rilCall.state = ofonoStateToRILState(g_value_peek_pointer(state));

    unsigned callIndex = 0;
    sscanf(objPath, "/isimodem/voicecall%02u", &callIndex); // FIXME
    call->rilCall.index = callIndex;
    call->rilCall.toa = 145; // international format
    call->rilCall.isVoice = 1;
    call->rilCall.number = call->number;
    call->rilCall.name = call->name;
    call->rilCall.uusInfo = NULL;

    if (RIL_CALL_INCOMING == call->rilCall.state) {
        call->rilCall.isMT = 1;
        RIL_onUnsolicitedResponse(RIL_UNSOL_CALL_RING, 0, 0);
    }
    else //if (RIL_CALL_INCOMING == call->rilCall.state)
        call->rilCall.isMT = 0;
    /* Presentation: 0=Allowed, 1=Restricted, 2=Not Specified/Unknown 3=Payphone */
    call->rilCall.namePresentation = strlen(call->name) ? 0 : 2;
    call->rilCall.numberPresentation = strlen(call->number) ? 0 : 2;

    call->obj = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE,
                                          objPath, OFONO_IFACE_CALL);
    if (call->obj) {
        // signal PropertyChanged(string property, variant value)
        dbus_g_proxy_add_signal(call->obj, OFONO_SIGNAL_PROPERTY_CHANGED,
                                G_TYPE_STRING, G_TYPE_VALUE, G_TYPE_INVALID);
        dbus_g_proxy_connect_signal(call->obj,
                                    OFONO_SIGNAL_PROPERTY_CHANGED,
                                    G_CALLBACK(callPropertyChanged), 0, NULL);

        // signal DisconnectReason(string reason)
        dbus_g_proxy_add_signal(call->obj, OFONO_SIGNAL_DISCONNECT_REASON,
                                G_TYPE_STRING, G_TYPE_INVALID);
        dbus_g_proxy_connect_signal(call->obj,
                                    OFONO_SIGNAL_DISCONNECT_REASON,
                                    G_CALLBACK(callDisconnectReason), 0, NULL);
    }

    pthread_mutex_lock(&lock);
    voiceCalls = g_slist_append(voiceCalls, call);
    pthread_mutex_unlock(&lock);

    RIL_onUnsolicitedResponse(RIL_UNSOL_RESPONSE_CALL_STATE_CHANGED, 0, 0);
}

static void vcmCallRemoved(DBusGProxy *proxy, const char *objPath, gpointer priv)
{
    LOGD("vcmCallRemoved: %s", objPath);

    GSList *l;
    int found = 0;

    pthread_mutex_lock(&lock);
    for (l = voiceCalls; l; l = l->next) {
        ORIL_Call *call = (ORIL_Call*) l->data;
        if (!g_strcmp0(objPath, call->objPath)) {
            found = 1;
            dbus_g_proxy_disconnect_signal(call->obj,
                                           OFONO_SIGNAL_PROPERTY_CHANGED,
                                           G_CALLBACK(callPropertyChanged), 0);
            dbus_g_proxy_disconnect_signal(call->obj, OFONO_SIGNAL_DISCONNECT_REASON,
                                           G_CALLBACK(callDisconnectReason), 0);
            free(call);
            voiceCalls = g_slist_delete_link(voiceCalls, l);
            break;
        }
    }
    pthread_mutex_unlock(&lock);

    RIL_onUnsolicitedResponse(RIL_UNSOL_RESPONSE_CALL_STATE_CHANGED, 0, 0);
    if (!found)
        LOGE("call not found: %s", objPath);
}

static void audioSettingsPropertyChanged(DBusGProxy *proxy, const gchar *property,
                                         GValue *value, gpointer priv)
{
    // XXX
    LOGW("audioSettingsPropertyChanged %s->%s", property, g_strdup_value_contents(value));
    if (!g_strcmp0(property, "Active"))
        cmtAudioSetActive(g_value_get_boolean(value) ? 1 : 0);
}

static void sim_property_changed(DBusGProxy *proxy, const gchar *property,
                                 GValue *value, gpointer user_data)
{
    // XXX
    LOGW("sim_property_changed %s->%s", property, g_strdup_value_contents(value));

    // sometimes we don't have IMSI at interface creation time
    // may be property is changing now?
    if (!simIMSI[0] && !g_strcmp0(property, "SubscriberIdentity")) {
        strncpy(simIMSI, g_value_peek_pointer(value), sizeof(simIMSI));
        RIL_onUnsolicitedResponse(RIL_UNSOL_RESPONSE_SIM_STATUS_CHANGED, 0, 0);
    }
    else if (SIM_ABSENT == simStatus && !g_strcmp0(property, "Present")) {
        simStatus = g_value_get_boolean(value) ? SIM_READY : SIM_ABSENT;
        RIL_onUnsolicitedResponse(RIL_UNSOL_RESPONSE_SIM_STATUS_CHANGED, 0, 0);
    }
    else if (!g_strcmp0(property, "PinRequired")) {
        LOGD("PinRequired: %s", (char*) g_value_peek_pointer(value));
        if ( !strcasecmp(g_value_peek_pointer(value), "pin") )
            simStatus = SIM_PIN;
        else if ( !strcasecmp(g_value_peek_pointer(value), "puk") )
            simStatus = SIM_PUK;
        else if ( strcasecmp(g_value_peek_pointer(value), "none") != 0 )
            simStatus = SIM_NOT_READY; // FIXME

        RIL_onUnsolicitedResponse(RIL_UNSOL_RESPONSE_SIM_STATUS_CHANGED, 0, 0);
    }

    g_value_unset(value);
}

static void supsrvPropertyChanged(DBusGProxy *proxy, const gchar *property,
                                  GValue *value, gpointer user_data)
{
    const char *propValue = g_value_peek_pointer(value);
    LOGW("supsrvPropertyChanged %s->%s", property, propValue);
    g_value_unset(value);
}

static void supsrvRequestReceived(DBusGProxy *proxy, const gchar *message,
                                  gpointer user_data)
{
    // XXX
    LOGW("supsrvRequestReceived %s", message);
}

static void sms_property_changed(DBusGProxy *proxy, const gchar *property,
                                 GValue *value, gpointer user_data)
{
    // XXX
    LOGW("sms_property_changed %s->%s", property, g_strdup_value_contents(value));
    g_value_unset(value);
}

static void smsImmediateMessage(DBusGProxy *proxy, const gchar *message,
                                GHashTable *dict, gpointer userData)
{
    LOGD("smsImmediateMessage: %s", message);
}

extern int encodePDU(unsigned char *pdu, const char *message, const char *smsc, const char *sender);

static void smsIncomingMessage(DBusGProxy *proxy, const gchar *message,
                               GHashTable *dict, gpointer userData)
{
    // TODO: more accurate guess about buffer length
    unsigned char *pdu = malloc(240 + strlen(message)*4);

    LOGD("smsIncomingMessage: %s", message);
    g_hash_table_foreach(dict, (GHFunc)hash_entry_gvalue_print, NULL);
    GValue *sender = g_hash_table_lookup(dict, "Sender");

    if (sender) {
        if (encodePDU(pdu, message, "+79168999100", g_value_peek_pointer(sender))) {
            LOGD("PDU: %s", pdu);
            RIL_onUnsolicitedResponse(RIL_UNSOL_RESPONSE_NEW_SMS, pdu, sizeof(char*));
        }
        g_value_unset(sender);
    }
    //g_hash_table_destroy(dict);
    free(pdu);
}

static void connman_property_changed(DBusGProxy *proxy, const gchar *property,
                                     GValue *value, gpointer user_data)
{
    // XXX
    LOGW("connman_property_changed %s->%s", property, g_strdup_value_contents(value));

    if (!g_strcmp0(property, "Attached")) {
        connmanAttached = g_value_get_boolean(value);
        sendNetworkStateChanged();
    } else if (!g_strcmp0(property, "RoamingAllowed")) {
        roamingAllowed = g_value_get_boolean(value);
    }
    g_value_unset(value);
}

static void pdc_property_changed(DBusGProxy *proxy, const gchar *property,
                                 GValue *value, gpointer user_data)
{
    // XXX
    LOGW("pcd_property_changed %s->%s", property, g_strdup_value_contents(value));
    if (!g_strcmp0(property, "Active")) {
        pdcActive = g_value_get_boolean(value);
        if (pdcActive) {
            getIP();
        }
    }
    g_value_unset(value);
}

static void netregPropertyChanged(DBusGProxy *proxy, const gchar *property,
                                  GValue *value, gpointer user_data)
{
    if (!g_strcmp0(property, "Strength")) {
        //LOGD("Strength: %u, screenState=%d", g_value_get_uint(value), screenState);
        if (screenState) {
            netregStrength = (unsigned int)g_value_get_uchar(value);
            requestSignalStrength(0, 0, 0);
        }
        g_value_unset(value);
        return;
    }
    else if (!g_strcmp0(property, "BaseStation")) {
        // Shut it up
        return;
    }
    else if (!g_strcmp0(property, "CellId")) {
        netregCID = g_value_get_uint(value);
    }
    else if (!g_strcmp0(property, "LocationAreaCode")) {
        netregLAC = g_value_get_uint(value);
    }
    else if (!g_strcmp0(property, "Status")) {
        const gchar *status = g_value_peek_pointer(value);
        if (!g_strcmp0(status, "searching")) {
            netregStatus = 2; // Not registered, but MT is currently searching
        }
        else if (!g_strcmp0(status, "registered")) {
            netregStatus = 1;
        }
        else if (!g_strcmp0(status, "roaming")) {
            netregStatus = 5;
        }
        else {
            netregStatus = 0; // Not registered, not searching
            netregMCC[0] = 0;
            netregMNC[0] = 0;
            netregOperator[0] = 0;
        }
    }
    else if (!g_strcmp0(property, "Name")) {
        snprintf(netregOperator, sizeof(netregOperator), "%s",
                 (const char* )g_value_peek_pointer(value));
    }
    else if (!g_strcmp0(property, "MobileNetworkCode")) {
        snprintf(netregMNC, sizeof(netregMNC), "%s",
                 (const char*) g_value_peek_pointer(value));
    }
    else if (!g_strcmp0(property, "MobileCountryCode")) {
        snprintf(netregMCC, sizeof(netregMCC), "%s",
                 (const char*) g_value_peek_pointer(value));
    }
    else if (!g_strcmp0(property, "Technology")) {
        const gchar *tech = g_value_peek_pointer(value);
        if (!g_strcmp0(tech, "gsm")){
            netregTech = 1;
        }else if (!g_strcmp0(tech, "edge")){
            netregTech = 2;
        }else if (!g_strcmp0(tech, "umts")){
            netregTech = 3;
        }else if (!g_strcmp0(tech, "hspa")){
            netregTech = 11;
        }else if (!g_strcmp0(tech, "lte")){
            /* RIL doesn't support LTE, report unknown */
            netregTech = 11;
        }
    }
    else if (!g_strcmp0(property, "Mode")) {
        const gchar *mode = g_value_peek_pointer(value);
        if (!g_strcmp0(mode, "auto")){
            netregMode = 0;
        }else if (!g_strcmp0(mode, "manual")){
            netregMode = 1;
        }
    }

    gchar *valStr = g_strdup_value_contents(value);
    LOGW("netreg_property_changed %s->%s", property, valStr);
    g_free(valStr);
    sendNetworkStateChanged();
    g_value_unset(value);
}

static void radiosettingsPropertyChanged(DBusGProxy *proxy, const gchar *property,
                                         GValue *value, gpointer user_data)
{
    LOGD("RadioSettings property changed %s",property); 
}

static void initVoiceCallInterfaces()
{
    vcm = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, MODEM, OFONO_IFACE_CALLMAN);
    if (vcm) {
        // VoiceCallManager.PropertyChanged
        dbus_g_proxy_add_signal(vcm, OFONO_SIGNAL_PROPERTY_CHANGED,
                                G_TYPE_STRING, G_TYPE_VALUE,
                                G_TYPE_INVALID);

        dbus_g_proxy_connect_signal(vcm,
                                    OFONO_SIGNAL_PROPERTY_CHANGED,
                                    G_CALLBACK(vcmPropertyChanged), vcm, NULL);

        // VoiceCallManager.CallAdded
        dbus_g_proxy_add_signal(vcm, OFONO_SIGNAL_CALL_ADDED,
                                DBUS_TYPE_G_OBJECT_PATH, type_a_sv,
                                G_TYPE_INVALID);

        dbus_g_proxy_connect_signal(vcm,
                                    OFONO_SIGNAL_CALL_ADDED,
                                    G_CALLBACK(vcmCallAdded), vcm, NULL);

        // VoiceCallManager.CallRemoved
        dbus_g_proxy_add_signal(vcm, OFONO_SIGNAL_CALL_REMOVED,
                                DBUS_TYPE_G_OBJECT_PATH, G_TYPE_INVALID);

        dbus_g_proxy_connect_signal(vcm,
                                    OFONO_SIGNAL_CALL_REMOVED,
                                    G_CALLBACK(vcmCallRemoved), vcm, NULL);
    }
    else
        LOGE("Failed to create VCM proxy object");
}

static void initSimInterface()
{
    sim = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, MODEM, OFONO_IFACE_SIMMANAGER);
    if (sim) {
        dbus_g_proxy_add_signal(sim, OFONO_SIGNAL_PROPERTY_CHANGED,
                                G_TYPE_STRING, G_TYPE_VALUE, G_TYPE_INVALID);
        dbus_g_proxy_connect_signal(sim,
                                    OFONO_SIGNAL_PROPERTY_CHANGED,
                                    G_CALLBACK(sim_property_changed), sim, NULL);
        LOGW("Sim proxy created");

#if 0
        GHashTable *dict = iface_get_properties(sim);
        if (!dict) {
            LOGE("SimManager.GetProperties failed");
            return;
        }
        g_hash_table_foreach(dict, (GHFunc)hash_entry_gvalue_print, NULL);

        // Read IMSI
        GValue *value = (GValue *) g_hash_table_lookup(dict, "SubscriberIdentity");
        if (value) {
            strncpy(simIMSI, g_value_peek_pointer(value), sizeof(simIMSI));
        }
        else {
            LOGE("No SubscriberIdentity! SIM is locked?");
        }

        g_hash_table_destroy(dict);
#endif
    }
    else
        LOGE("Failed to create SIM proxy object");
}

static void initConnManager()
{
    LOGD("initConnManager");
    // DataConnectionManager
    connman = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, MODEM, OFONO_IFACE_CONNMAN);
    if (connman) {
        dbus_g_proxy_add_signal(connman, OFONO_SIGNAL_PROPERTY_CHANGED,
                                G_TYPE_STRING, G_TYPE_VALUE, G_TYPE_INVALID);
        dbus_g_proxy_connect_signal(connman,
                                    OFONO_SIGNAL_PROPERTY_CHANGED,
                                    G_CALLBACK(connman_property_changed), connman, NULL);
        LOGW("DataConnectionManager proxy created");
    }
    else {
        LOGE("Failed to create DataConnectionManager proxy object");
        return;
    }

    // find existing context
    LOGD("Trying to find existing context");
    char *pdcPath = NULL;
    GPtrArray *arrContexts = 0;
    GError *error = NULL;
    if (!dbus_g_proxy_call(connman, "GetContexts", &error, G_TYPE_INVALID,
                           type_a_oa_sv, &arrContexts,
                           G_TYPE_INVALID))
    {
        LOGE("initConnManager: GetContexts error: %s", error->message);
        LOGW("New context will be created");
    }

    // we'll use first found context
    if (arrContexts && arrContexts->len) {
        GValueArray *ctx = g_ptr_array_index(arrContexts, 0);
        pdcPath = g_strdup(g_value_get_boxed(g_value_array_get_nth(ctx, 0)));
        LOGD("existing pdcPath: %s", pdcPath);
    }

    if (!pdcPath) {
        // create new context if nothing found
        GError *error = NULL;
        LOGD("ConnMan.CreateContext preparing for crash...");
        if ( !dbus_g_proxy_call(connman, "AddContext", &error,
                                G_TYPE_STRING, "internet",
                                G_TYPE_STRING, "internet",
                                G_TYPE_INVALID,
                                DBUS_TYPE_G_PROXY, &pdc, G_TYPE_INVALID) )
        {
            LOGE("ConnMan.CreateContext failed: %s", error->message);
            g_error_free (error);
            return;
        }
        dbus_g_proxy_set_interface(pdc, OFONO_IFACE_PDC);
    }
    else {
        // create org.ofono.PrimaryDataContext proxy
        LOGD("pdcPath: %s", pdcPath);
        pdc = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, pdcPath, OFONO_IFACE_PDC);
        g_free(pdcPath);
    }

    if (pdc) {
        dbus_g_proxy_add_signal(pdc, OFONO_SIGNAL_PROPERTY_CHANGED,
                                G_TYPE_STRING, G_TYPE_VALUE, G_TYPE_INVALID);
        dbus_g_proxy_connect_signal(pdc,
                                    OFONO_SIGNAL_PROPERTY_CHANGED,
                                    G_CALLBACK(pdc_property_changed), pdc, NULL);
        LOGW("PrimaryDataContext proxy created");
    }
    else
        LOGE("Failed to create PrimaryDataContext proxy object");
}

static void modem_property_changed(DBusGProxy *proxy, const gchar *property,
                                   GValue *value, gpointer user_data)
{
    // XXX
    LOGD("modem_property_changed: %s->%s", property, g_strdup_value_contents(value));

    if (!vcm && g_strcmp0(property, "Online") == 0) {
        LOGD("Modem->Onlne: %s", g_value_get_boolean(value) ? "true" : "false");
        //TODO: what?
    }
    else if (g_strcmp0(property, "Interfaces") == 0) {
        const gchar **ifArr = g_value_peek_pointer(value);
        LOGD("Interfaces:");
        while(*ifArr) {
            LOGD("  >> %s", *ifArr);
            if (!vcm && !g_strcmp0(*ifArr, OFONO_IFACE_CALLMAN)) {
                initVoiceCallInterfaces();
            }
            else if (!sim && !g_strcmp0(*ifArr, OFONO_IFACE_SIMMANAGER)) {
                initSimInterface();
            }
            else if (!netreg && !g_strcmp0(*ifArr, OFONO_IFACE_NETREG)) {
                netreg = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, MODEM, OFONO_IFACE_NETREG);
                if (netreg) {
                    dbus_g_proxy_add_signal(netreg, OFONO_SIGNAL_PROPERTY_CHANGED,
                                            G_TYPE_STRING, G_TYPE_VALUE, G_TYPE_INVALID);
                    dbus_g_proxy_connect_signal(netreg,
                                                OFONO_SIGNAL_PROPERTY_CHANGED,
                                                G_CALLBACK(netregPropertyChanged), netreg, NULL);
                    LOGW("NetReg proxy created");
                }
                else
                    LOGE("Failed to create NetReg proxy object");
            }
            else if (!radiosettings && !g_strcmp0(*ifArr, OFONO_IFACE_RADIOSETTINGS)) {
                radiosettings = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, MODEM, OFONO_IFACE_RADIOSETTINGS);
                if (radiosettings) {
                    dbus_g_proxy_add_signal(radiosettings, OFONO_SIGNAL_PROPERTY_CHANGED,
                                            G_TYPE_STRING, G_TYPE_VALUE, G_TYPE_INVALID);
                    dbus_g_proxy_connect_signal(radiosettings,
                                                OFONO_SIGNAL_PROPERTY_CHANGED,
                                                G_CALLBACK(radiosettingsPropertyChanged), radiosettings, NULL);
                    LOGW("NetReg proxy created");
                }
                else
                    LOGE("Failed to create NetReg proxy object");
            }
            else if (!sms && !g_strcmp0(*ifArr, OFONO_IFACE_SMSMAN)) {
                sms = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, MODEM, OFONO_IFACE_SMSMAN);
                if (sms) {
                    dbus_g_proxy_add_signal(sms, OFONO_SIGNAL_PROPERTY_CHANGED,
                                            G_TYPE_STRING, G_TYPE_VALUE, G_TYPE_INVALID);
                    dbus_g_proxy_connect_signal(sms,
                                                OFONO_SIGNAL_PROPERTY_CHANGED,
                                                G_CALLBACK(sms_property_changed), sms, NULL);

                    dbus_g_proxy_add_signal(sms, OFONO_SIGNAL_IMMEDIATE_MESSAGE,
                                            G_TYPE_STRING,
                                            dbus_g_type_get_map("GHashTable", G_TYPE_STRING, G_TYPE_VALUE),
                                            G_TYPE_INVALID);
                    dbus_g_proxy_connect_signal(sms, OFONO_SIGNAL_IMMEDIATE_MESSAGE,
                                                G_CALLBACK(smsImmediateMessage), sms, 0);

                    dbus_g_proxy_add_signal(sms, OFONO_SIGNAL_INCOMING_MESSAGE,
                                            G_TYPE_STRING,
                                            dbus_g_type_get_map("GHashTable", G_TYPE_STRING, G_TYPE_VALUE),
                                            G_TYPE_INVALID);
                    dbus_g_proxy_connect_signal(sms, OFONO_SIGNAL_INCOMING_MESSAGE,
                                                G_CALLBACK(smsIncomingMessage), sms, 0);
                    LOGW("SmsManager proxy created");
                }
                else
                    LOGE("Failed to create SmsMan proxy object");
            }
            else if (!supsrv && !g_strcmp0(*ifArr, OFONO_IFACE_SUPSRV)) {
                supsrv = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, MODEM, OFONO_IFACE_SUPSRV);
                if (supsrv) {
                    dbus_g_proxy_add_signal(supsrv, OFONO_SIGNAL_PROPERTY_CHANGED,
                                            G_TYPE_STRING, G_TYPE_VALUE, G_TYPE_INVALID);
                    dbus_g_proxy_connect_signal(supsrv,
                                                OFONO_SIGNAL_PROPERTY_CHANGED,
                                                G_CALLBACK(supsrvPropertyChanged), supsrv, NULL);

                    dbus_g_proxy_add_signal(supsrv, OFONO_SIGNAL_REQUEST_RECEIVED,
                                            G_TYPE_STRING, G_TYPE_INVALID);
                    dbus_g_proxy_connect_signal(supsrv, OFONO_SIGNAL_REQUEST_RECEIVED,
                                                G_CALLBACK(supsrvRequestReceived), supsrv, 0);

                    LOGW("SupplementaryServices proxy created");
                }
                else
                    LOGE("Failed to create SupplementaryServices proxy object");
            }
            else if (!audioSettings && !g_strcmp0(*ifArr, OFONO_IFACE_AUDIOSETTINGS)) {
                audioSettings = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, MODEM, OFONO_IFACE_AUDIOSETTINGS);
                if (audioSettings) {
                    dbus_g_proxy_add_signal(audioSettings, OFONO_SIGNAL_PROPERTY_CHANGED,
                                            G_TYPE_STRING, G_TYPE_VALUE, G_TYPE_INVALID);
                    dbus_g_proxy_connect_signal(audioSettings,
                                                OFONO_SIGNAL_PROPERTY_CHANGED,
                                                G_CALLBACK(audioSettingsPropertyChanged), audioSettings, NULL);
                    LOGW("AudioSettings proxy created");
                }
                else
                    LOGE("Failed to create AudioSettings proxy object");
            }
            else if (!connman && !g_strcmp0(*ifArr, OFONO_IFACE_CONNMAN)) {
                initConnManager();
            }
            ifArr++;
        }
    }
    else if (g_strcmp0(property, "Powered") == 0) {
        if (poweredToken) {
            RIL_onRequestComplete(poweredToken, RIL_E_SUCCESS, NULL, 0);
            poweredToken = 0;
        }
    }
    else if (g_strcmp0(property, "Serial") == 0) {
        strncpy(modemIMEI, g_value_peek_pointer(value), sizeof(modemIMEI));
        if (imeiToken) {
            RIL_onRequestComplete(imeiToken, RIL_E_SUCCESS,
                                  modemIMEI, sizeof(char *));
            imeiToken = 0;
        }
    }
    else if (g_strcmp0(property, "Revision") == 0) {
        strncpy(modemRev, g_value_peek_pointer(value), sizeof(modemRev));
        if (modemRevToken) {
            RIL_onRequestComplete(modemRevToken, RIL_E_SUCCESS, 
                                  modemRev, sizeof(char *));
            modemRevToken = 0;
        }
    }
    else if (g_strcmp0(property, "Features") == 0) {
        const gchar **fArr = g_value_peek_pointer(value);
        while(*fArr) {
            LOGD("  >> %s", *fArr);
            if (!goingOnline && g_strcmp0(*fArr, "rat") == 0) {
                LOGW("rat available, going online");
                GValue value = G_VALUE_INITIALIZATOR;
                g_value_init(&value, G_TYPE_BOOLEAN);
                g_value_set_boolean(&value, TRUE);
                objSetProperty(modem, "Online", &value);
                goingOnline = 1;
                setRadioState(RADIO_STATE_SIM_READY);
            }
            else if (g_strcmp0(*fArr, "gprs") == 0) {
                sendNetworkStateChanged();
            }
            fArr++;
        }
    }


    g_value_unset(value);
}

static int initOfono()
{
    // give a chance to ofonod for settling
    sleep(1);

    GError *error = NULL;
    connection = dbus_g_bus_get(DBUS_BUS_SYSTEM, &error);
    if (!connection) {
        LOGE("Failed to open connection to bus: %s\n", error->message);
        g_error_free (error);
        return 0;
    }
    LOGW("dbus connect - ok");

    error = NULL;
    manager = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, "/", "org.ofono.Manager");
    if (!manager) {
        LOGE("Failed to create Manager proxy object: %s", error->message);
        return 0;
    }
    LOGD("proxy manager - ok");

    GPtrArray *modems = 0;
    if (!dbus_g_proxy_call(manager, "GetModems", &error, G_TYPE_INVALID,
                           type_a_oa_sv, &modems,
                           G_TYPE_INVALID))
    {
        LOGE(".GetModems failed: %s", error->message);
        return 0;
    }

    if (!modems || !modems->len) {
        LOGE("modems->len is empty. Probably, modem isn't detected yet.");
        return 0;
    }

    GValueArray *mdm = g_ptr_array_index(modems, 0);
    const char *modemPath = g_value_get_boxed(g_value_array_get_nth(mdm, 0));
    if (g_strcmp0(MODEM, modemPath) != 0) {
        LOGE("Modem path dosn't match: \"%s\", but we expect \"%s\"", modemPath, MODEM);
        return 0;
    }
    g_ptr_array_free(modems, TRUE);

    error = NULL;
    modem = dbus_g_proxy_new_for_name(connection, OFONO_SERVICE, MODEM, "org.ofono.Modem");
    if (!modem) {
        LOGE("Failed to create Modem proxy object: %s", error->message);
        return 0;
    }
    dbus_g_proxy_add_signal(modem, OFONO_SIGNAL_PROPERTY_CHANGED, G_TYPE_STRING, G_TYPE_VALUE, G_TYPE_INVALID);
    dbus_g_proxy_connect_signal(modem,
                                OFONO_SIGNAL_PROPERTY_CHANGED,
                                G_CALLBACK(modem_property_changed), modem, NULL);
    LOGW("modem proxy - ok");

    LOGW("Ofono initialization - ok");
    return 0;
}

const RIL_RadioFunctions *RIL_Init(const struct RIL_Env *env, int argc, char **argv)
{
    int ret;
    pthread_attr_t attr;
    pthread_t s_tid_mainloop;

    s_rilenv = env;

    if (!g_thread_supported ())
    {
        g_thread_init(NULL);
        dbus_g_thread_init();
    }
    g_type_init();

    // types for DBus
    type_a_sv = dbus_g_type_get_map("GHashTable", G_TYPE_STRING, G_TYPE_VALUE);

    type_oa_sv = dbus_g_type_get_struct("GValueArray",
                                        DBUS_TYPE_G_OBJECT_PATH,
                                        type_a_sv,
                                        G_TYPE_INVALID);

    type_a_oa_sv = dbus_g_type_get_collection("GPtrArray", type_oa_sv);

    // marshallers
    dbus_g_object_register_marshaller(g_cclosure_user_marshal_VOID__STRING_BOXED,
                                      G_TYPE_NONE,
                                      G_TYPE_STRING,
                                      G_TYPE_VALUE,
                                      G_TYPE_INVALID);

    dbus_g_object_register_marshaller(g_cclosure_user_marshal_VOID__STRING_BOXED,
                                      G_TYPE_NONE,
                                      DBUS_TYPE_G_OBJECT_PATH,
                                      type_a_sv,
                                      G_TYPE_INVALID);

    loop = g_main_loop_new (NULL, FALSE);
    setRadioState(RADIO_STATE_OFF);

    cmtAudioInit();

    if (initOfono())
        return 0;

    pthread_attr_init (&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
    ret = pthread_create(&s_tid_mainloop, &attr, mainLoop, NULL);

    return &s_callbacks;
}
