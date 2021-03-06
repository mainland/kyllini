AC_INIT([kzc Ziria Compiler], [0.1], [mainland@drexel.edu], [kzc])

AC_PREREQ([2.62])

AC_CONFIG_SRCDIR([src/KZC/Monad.hs])

AC_CONFIG_HEADERS([include/KzcConfig.h])
AC_CONFIG_FILES([Makefile kyllini.buildinfo include/KzcSysTools.h mk/common.mk])

#
# Find the C compiler
#
AC_ARG_WITH([gcc],
	    [AC_HELP_STRING([--with-gcc], [path to gcc])],
            [CC=$withval],
            [AC_PATH_PROG(CC, gcc)])

CC_STRING=$(echo $CC | sed -e 's/[[\\]]/\\&/g')
AC_SUBST(CC_STRING)

#
# Find the Haskell compiler
#
AC_ARG_WITH([compiler],
	    [AC_HELP_STRING([--with-compiler], [path to Haskell compiler])],
            [HC=$withval],
            [AC_PATH_PROG(HC, ghc)])

#
# Find the C preprocessor
#
AC_PROG_CPP()

CPP_STRING=$(echo $CPP | sed -e 's/[[\\]]/\\&/g')
AC_SUBST(CPP_STRING)

#
# Look for clock bits
#
AC_CHECK_HEADERS(sys/resource.h)
AC_CHECK_HEADERS(sys/time.h)
AC_CHECK_HEADERS([mach/mach.h])
AC_CHECK_HEADERS([mach/mach_time.h])
AC_SEARCH_LIBS([clock_gettime],[rt posix4])
AC_CHECK_FUNCS([clock clock_gettime mach_timebase_info])

#
# Look for semaphore bits
#
AC_CHECK_HEADERS([dispatch/dispatch.h])

#
# Function checks
#
AC_FUNC_ALLOCA()

#
# Finish up
#

AC_OUTPUT
