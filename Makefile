
FRAMAC_SHARE	:=$(shell frama-c.byte -print-path)
FRAMAC_LIBDIR	:=$(shell frama-c.byte -print-libpath)
PLUGIN_DIR ?=.
PLUGIN_NAME	:= StaDy

PLUGIN_TESTS_DIRS := \
	stmt_spec \
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
	deleteSubstr1a \
	deleteSubstr1c \
	deleteSubstr2b \
	deleteSubstr3 \
	deleteSubstr4 \
	sum_array \
	num_of \
	struct \
	overflow_should_crash \
	overflow_shouldnt_crash

#unused tests: deleteSubstr0 deleteSubstr1b deleteSubstr1d deleteSubstr2a deleteSubstr2c type_invariants

PLUGIN_PTESTS_OPTS := -j 1

PLUGIN_CMO	:= \
	sd_options \
	sd_debug \
	sd_states \
	sd_subst \
	sd_utils \
	sd_socket \
	sd_native_precond \
	sd_insertions \
	sd_print \
	sd_register
PLUGIN_GUI_CMO 	:= sd_register_gui 
include $(FRAMAC_SHARE)/Makefile.dynamic

install::
	$(PRINT_CP) $(PLUGIN_NAME) share files
	$(MKDIR) $(FRAMAC_SHARE)/stady
	$(CP) $(StaDy_DIR)/externals.c $(FRAMAC_SHARE)/stady

uninstall::
	$(PRINT_RM) $(PLUGIN_NAME) share files
	$(RM) -r $(FRAMAC_SHARE)/stady

clean::
	$(RM) $(StaDy_DIR)/__sd_instru_*.c
	$(RM) $(StaDy_DIR)/__sd_*.pl
	$(RM) -r $(StaDy_DIR)/pathcrawler___sd_instru_*
	$(RM) -r $(StaDy_DIR)/testcases___sd_instru_*
