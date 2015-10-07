#include <alloca.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <kz/types.h>
#include <kz/ext.h>
#include <kz/driver.h>
#include <kz/rt.h>

#define FIRSTCLASSLABELS

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
#define BREAK break

#define BEGIN_DISPATCH dispatch: switch(curk) {
#define END_DISPATCH }
#endif /* !defined(FIRSTCLASSLABELS) */

#ifdef __cplusplus
extern "C" {
#endif

void kz_main(const kz_params_t*);

#ifdef __cplusplus
}
#endif
