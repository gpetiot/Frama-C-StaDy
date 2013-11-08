
FRAMAC_SHARE	:=$(shell frama-c.byte -print-path)
FRAMAC_LIBDIR	:=$(shell frama-c.byte -print-libpath)
PLUGIN_NAME	= PCVA

PLUGIN_TESTS_DIRS:=bubble_sort insertion_sort merge_arrays merge_sort quick_sort tcas
PLUGIN_PTESTS_OPTS:=-j 1

PLUGIN_CMO	= options prop_id pcva_printer states pcva_socket native_precond register
PLUGIN_GUI_CMO 	= register_gui 
include $(FRAMAC_SHARE)/Makefile.dynamic

