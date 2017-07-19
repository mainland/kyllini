/*
Copyright (c) 2015-2017
        Drexel University.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:
1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. Neither the name of the University nor the names of its contributors
   may be used to endorse or promote products derived from this software
   without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY AND CONTRIBUTORS ``AS IS'' AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED.  IN NO EVENT SHALL THE UNIVERSITY OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
SUCH DAMAGE.
*/

#if !defined(KZ_H)
#define KZ_H

#include <limits.h>
#include <math.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/*
 * See:
 *   https://www.gnu.org/software/autoconf/manual/autoconf-2.69/html_node/Particular-Functions.html
 */

#ifdef HAVE_ALLOCA_H
# include <alloca.h>
#elif !defined alloca
# ifdef __GNUC__
#  define alloca __builtin_alloca
# elif defined _AIX
#  define alloca __alloca
# elif defined _MSC_VER
#  include <malloc.h>
#  define alloca _alloca
# elif !defined HAVE_ALLOCA
#  ifdef  __cplusplus
extern "C"
#  endif
void *alloca (size_t);
# endif
#endif

#include <kz/types.h>
#include <kz/bits.h>
#include <kz/driver.h>
#include <kz/ext.h>
#include <kz/threads.h>

#ifdef __cplusplus
#define QTY(M,N)  Q<M,N>
#define UQTY(M,N) UQ<M,N>

#include <fixed.hpp>
#endif

#if defined(WHOLEPROGRAM)
#include <bits.c>
#include <driver.c>
#include <ext.c>
#include <ext_zira.c>
#include <io.cpp>
#include <threads.c>
#include <sora/kz_sora.cpp>
#endif /* defined(WHOLEPROGRAM) */

#if defined(FIRSTCLASSLABELS)
typedef void* KONT;

#define LABEL(k) k
#define LABELADDR(k) &&k
#define JUMP(l) goto l
#define INDJUMP(k) goto *k
#define BREAK goto done

#define BEGIN_DISPATCH dispatch:
#define END_DISPATCH done:
#else /* !defined(FIRSTCLASSLABELS) */
typedef int KONT;

#define LABEL(k) case k
#define LABELADDR(k) k
#define JUMP(l) curk = l; goto dispatch
#define INDJUMP(k) curk = k; goto dispatch
#define BREAK goto done

#define BEGIN_DISPATCH dispatch: switch(curk) {
#define END_DISPATCH } done:
#endif /* !defined(FIRSTCLASSLABELS) */

#endif /* !defined(KZ_H) */
