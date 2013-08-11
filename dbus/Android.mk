LOCAL_PATH:= $(call my-dir)
include $(CLEAR_VARS)

LOCAL_SRC_FILES:= \
        dbus-glib.c                             \
        dbus-gmain.c                            \
        dbus-gmarshal.c                         \
        dbus-gobject.c                          \
        dbus-gproxy.c                           \
        dbus-gtest.c                            \
        dbus-gvalue.c                           \
        dbus-gthread.c                          \
        dbus-gtype-specialized.c                \
        dbus-gutils.c                           \
        dbus-gsignature.c                       \
        dbus-gvalue-utils.c                     \
##

LOCAL_CFLAGS+=-O3

LOCAL_C_INCLUDES:= \
	$(LOCAL_PATH)/.. \
	external/dbus \
	external/glib/glib \
	external/glib \
	external/glib/android \
##

LOCAL_MODULE:=libdbus_glib
LOCAL_MODULE_TAGS := optional

include $(BUILD_STATIC_LIBRARY)
