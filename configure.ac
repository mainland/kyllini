AC_INIT([kzc Ziria Compiler], [0.1], [mainland@drexel.edu], [kzc])

AC_PREREQ([2.62])

AC_CONFIG_SRCDIR([src/KZC/Monad.hs])

AC_CONFIG_HEADERS([include/KzcConfig.h])
AC_CONFIG_FILES([Makefile kzc.buildinfo include/KzcSysTools.h])

#
# Find the C compiler
#
AC_ARG_WITH([gcc],
	    [AC_HELP_STRING([--with-gcc], [path to gcc])],
            [CC=$withval],
            [AC_PATH_PROG(CC, gcc)])

#
# Find the Haskell compiler
#
AC_ARG_WITH([compiler],
	    [AC_HELP_STRING([--with-compiler], [path to Haskell compiler])],
            [HC=$withval],
            [AC_PATH_PROG(HC, ghc)])

#
# Finish up
#

AC_OUTPUT
