
FRAMAC_SHARE	:=$(shell frama-c.byte -print-path)
FRAMAC_LIBDIR	:=$(shell frama-c.byte -print-libpath)
PLUGIN_NAME	= PCVA


PLUGIN_CMO	= options register
#PLUGIN_GUI_CMO 	= register_gui 
include $(FRAMAC_SHARE)/Makefile.dynamic

