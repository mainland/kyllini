#include <alloca.h>
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

void kzc_error(const char*);

double __kz_sqrt(double d);
double __kz_log2(double d);

int32_t __kz_round_int32(double d);
int32_t __kz_ceil_int32(double d);

int16_t __kz_sin_int16(int16_t x);
int16_t __kz_cos_int16(int16_t x);
int16_t __kz_atan2_int16(int16_t y, int16_t x);

int32_t __kz_atan2_int32(int32_t y, int32_t x);

complex32_t __kz_sumc32(const complex32_t x[4]);

int32_t __kz_v_sum_int32(int n, const int32_t *xs);

complex16_t __kz_v_sum_complex16(int n, const complex16_t *xs);

void __kz_v_or(int n, const uint8_t *in1, const uint8_t *in2, uint8_t *out);

void __kz_sora_ifft(int n, const complex16_t *in, complex16_t *out);
void __kz_sora_fft(int n, const complex16_t *in, complex16_t *out);

int16_t __kz_viterbiSig11a_brick_decode_fast(int n, const int8_t svalue[48], const uint8_t *bitValue);
int16_t __kz_viterbi_brick_decode_fast(int n, const int8_t svalue[48], const uint8_t *bitValue);
