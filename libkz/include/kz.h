#if !defined(KZ_H)
#define KZ_H

#include <alloca.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <kz/types.h>
#include <kz/bits.h>
#include <kz/driver.h>
#include <kz/ext.h>
#include <kz/threads.h>

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
