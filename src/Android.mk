#  Copyright (C) 2010 The NitDroid Project
#  Copyright (C) 2006 The Android Open Source Project
#
#  Author: Alexey Roslyakov <alexey.roslyakov@newsycat.com>
#
#  This program is free software; you can redistribute it and/or modify
#  it under the terms of the GNU General Public License version 2 as
#  published by the Free Software Foundation.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
#
LOCAL_PATH:= $(call my-dir)
include $(CLEAR_VARS)

LOCAL_SRC_FILES:= ril.c

LOCAL_C_INCLUDES := \
	$(LOCAL_PATH)/../dbus \
	$(KERNEL_HEADERS) \
	$(call include-path-for, glib) \
	$(call include-path-for, dbus)
##

LOCAL_SHARED_LIBRARIES := libcutils libglib-2.0 libril

LOCAL_STATIC_LIBRARIES := libgdbus_glib

LOCAL_CFLAGS := -DRIL_SHLIB -DHAVE_CONFIG_H

LOCAL_LDLIBS += -lpthread

LOCAL_PRELINK_MODULE := false
LOCAL_MODULE:= libofono-ril

include $(BUILD_SHARED_LIBRARY)
