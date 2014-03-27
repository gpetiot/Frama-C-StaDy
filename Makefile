
FRAMAC_SHARE	:=$(shell frama-c.byte -print-path)
FRAMAC_LIBDIR	:=$(shell frama-c.byte -print-libpath)
PLUGIN_NAME	:= StaDy

PLUGIN_TESTS_DIRS := \
	behaviors \
	quantified \
	binary_search \
	bubble_sort \
	insertion_sort \
	merge_arrays \
	merge_sort \
	quick_sort \
	tcas \
	first_subset \
	next_subset \
	deleteSubstr0 \
	deleteSubstr1a \
	deleteSubstr1b \
	deleteSubstr1c \
	deleteSubstr1d \
	deleteSubstr2a \
	deleteSubstr2b \
	deleteSubstr2c \
	deleteSubstr3 \
	deleteSubstr4 \
	sum_array \
	num_of \
	struct
PLUGIN_PTESTS_OPTS := -j 1

PLUGIN_CMO	:= \
	sd_options \
	sd_states \
	sd_utils \
	sd_subst \
	sd_socket \
	sd_native_precond \
	sd_printer \
	sd_register
PLUGIN_GUI_CMO 	:= sd_register_gui 
include $(FRAMAC_SHARE)/Makefile.dynamic

