#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define FIRSTCLASSLABELS

#if defined(FIRSTCLASSLABELS)
typedef void* KONT;

#define LABEL(k) k
#define LABELADDR(k) &&k
#define JUMP(l) goto l
#define INDJUMP(k) goto *k

#define BEGIN_DISPATCH dispatch:
#define END_DISPATCH
#else /* !defined(FIRSTCLASSLABELS) */
typedef int KONT;

#define LABEL(k) case k
#define LABELADDR(k) k
#define JUMP(l) curk = l; goto dispatch
#define INDJUMP(k) curk = k; goto dispatch

#define BEGIN_DISPATCH dispatch: switch(curk) {
#define END_DISPATCH }
#endif /* !defined(FIRSTCLASSLABELS) */

typedef struct complex_t {
    int32_t re;
    int32_t im;
} complex_t;

typedef struct complex8_t {
    int8_t re;
    int8_t im;
} complex8_t;

typedef struct complex16_t {
    int16_t re;
    int16_t im;
} complex16_t;

typedef struct complex32_t {
    int32_t re;
    int32_t im;
} complex32_t;

typedef struct complex64_t {
    int64_t re;
    int64_t im;
} complex64_t;
