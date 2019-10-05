
m4_define([plugin_file],Makefile.in)

m4_define([FRAMAC_SHARE_ENV],
          [m4_normalize(m4_esyscmd([echo $FRAMAC_SHARE]))])

m4_define([FRAMAC_SHARE],
	  [m4_ifval(FRAMAC_SHARE_ENV,[FRAMAC_SHARE_ENV],
                                     [m4_esyscmd(frama-c -print-path)])])

m4_ifndef([FRAMAC_M4_MACROS], [m4_include(FRAMAC_SHARE/configure.ac)])

check_plugin(stady,PLUGIN_RELATIVE_PATH(plugin_file),
	     [support for StaDy plug-in],yes,yes)

plugin_require(stady,PathCrawler)
check_plugin_dependencies

# Check Frama-C version
#######################

AC_MSG_CHECKING(for Frama-C version)
AC_MSG_RESULT($FRAMAC_VERSION)

VERSION_NUMBER=`echo $FRAMAC_VERSION | sed -e 's/^\([[0-9]]*\).*$/\1/'`
REQUIRED_NUMBER=19

if test -z "$VERSION_NUMBER" -o "$VERSION_NUMBER" -lt "$REQUIRED_NUMBER"; then
  AC_MSG_ERROR(Frama-C version must be at least $REQUIRED_NUMBER.)
fi;

if test $VERSION_NUMBER -gt $REQUIRED_NUMBER; then
  AC_MSG_WARN(Frama-C version is more recent than $REQUIRED_NUMBER, \
use it at your own risk.)
fi;

# OCaml version
###############

OCAMLVERSION=`ocamlc -v | sed -n -e 's|.*version *\(.*\)$|\1|p' `

MAY_RUN_TESTS=yes

# C compiler and stdio.h
#########################

AC_CHECK_HEADERS([stdio.h],[HAVE_STDIO_H=yes],)

# not sure it can actually happens:
# look like the configure stops on error if no C compiler detected
if test -z $HAVE_STDIO_H; then
  MAY_RUN_TESTS=no
  AC_MSG_WARN([stdio.h missing: non-regression tests unavailable.])
fi

# GMP library
#############

AC_CHECK_LIB(gmp,__gmpz_init,HAVE_GMP=yes,) # also set LIBS

if test -z $HAVE_GMP; then
  MAY_RUN_TESTS=no
  AC_MSG_WARN([GMP library missing: non-regression tests unavailable.])
fi

#######################
# Generating Makefile #
#######################

AC_SUBST(MAY_RUN_TESTS)
AC_SUBST(OCAMLVERSION)

write_plugin_config(Makefile)
