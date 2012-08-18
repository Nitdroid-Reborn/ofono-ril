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

#include <glib.h>

#define LOG_TAG "RIL"
#include <utils/Log.h>

static inline unsigned char makeSemiOctet(guint8 in)
{
    if (in < 10)
        return in + '0';
    if (in < 16)
        return in - 0xa + 'a';
    return 0;
}

static inline void setSemiOctet(unsigned char *pdu, int *offset, unsigned char oct)
{
    pdu[*offset] = oct;
	*offset = *offset + 1;
}

static inline void setOctet(unsigned char *pdu, int *offset, guint8 oct)
{
    setSemiOctet(pdu, offset, makeSemiOctet((oct & 0xf0) >> 4));
    setSemiOctet(pdu, offset, makeSemiOctet(oct & 0x0f));
}

static int encodeNumber(unsigned char *pdu, const char *num)
{
    unsigned char *pduPtr = pdu;
    *pduPtr++ = '9';
    *pduPtr++ = '1';

    int res = 0, resOdd = 1;
    while(num[res]) {
        if (!num[resOdd]) {
            *pduPtr++ = 'F';
            *pduPtr = num[res++];
            break;
        }
        *pduPtr++ = num[resOdd];
        *pduPtr++ = num[res];
        res += 2; resOdd += 2;
    }

    return res ? res : 0;
}

int encodePDU(unsigned char *pdu, const char *message, const char *smsc, const char *sender)
{
    int ofs = 0;
    setSemiOctet(pdu, &ofs, '0');

    // SMS Service Center
    int smcSize = encodeNumber(&pdu[2], smsc[0] == '+' ? &smsc[1] : "0000");
    ALOGD("smcSize: %d", smcSize);
    if (!smcSize) return 0;
    setSemiOctet(pdu, &ofs, makeSemiOctet(smcSize/2 + (smcSize & 0x1) + 1)); // length (in octets)
    ofs += smcSize + (smcSize & 0x1) + 2;

    setSemiOctet(pdu, &ofs, '0');
    setSemiOctet(pdu, &ofs, '4'); // First octet of the SMS-DELIVER PDU

    // Sender
    int senderSize = encodeNumber(&pdu[ofs+2], sender[0] == '+' ? &sender[1] : "0000");
    ALOGD("senderSize: %d", senderSize);
    if (!senderSize) return 0;
    setSemiOctet(pdu, &ofs, '0');
    setSemiOctet(pdu, &ofs, makeSemiOctet(senderSize));// length
    ofs += senderSize + (senderSize & 0x1) + 2;

    setOctet(pdu, &ofs, 0x00); // TP-PID
    setOctet(pdu, &ofs, 0x08); // TP-DCS (Class Unspecified, UCS2)
    setOctet(pdu, &ofs, 0x99); // TP-SCTS

    // Timestamp (whatever, don't realy care about it)
    setOctet(pdu, &ofs, 0x30);
    setOctet(pdu, &ofs, 0x92);
    setOctet(pdu, &ofs, 0x51);
    setOctet(pdu, &ofs, 0x61);
    setOctet(pdu, &ofs, 0x95);
    setOctet(pdu, &ofs, 0x80);

    gsize converted;
    char *ucs2_encoded = g_convert(message, -1, "UCS-2BE//TRANSLIT", "UTF-8",
                                   NULL, &converted, NULL);

    if (!ucs2_encoded || !converted) {
        ALOGE("!ucs2_encoded || !converted");
        return 0;
    }
    ALOGD("UCS2 length: %d %d", (int)converted, ofs);

    // pdu encoder able to encode only to ucs2 encoding (2bytes/char),
    // but length field stored as uint8.
    // Cut down size of the message (better than drop it).
    if (converted > 254)
        converted = 254;

    setOctet(pdu, &ofs, (guint8)converted); // TP-TP-User-Data-Length
    const char *strPtr = ucs2_encoded;
    while(converted-- > 0)
        setOctet(pdu, &ofs, (guint8) *strPtr++);

    g_free(ucs2_encoded);
    pdu[ofs] = 0;
    return ofs;
}
