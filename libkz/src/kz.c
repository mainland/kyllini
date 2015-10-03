#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include <kz.h>

void kzc_error(const char* s)
{
    fputs(s, stderr);
    abort();
}

double __kz_sqrt(double d)
{
    return sqrt(d);
}

double __kz_log2(double d)
{
    return log(d) / log(2.0);
}

int32_t __kz_round_int32(double d)
{
    return round(d);
}

int32_t __kz_ceil_int32(double d)
{
    return ceil(d);
}

int16_t __kz_sin_int16(int16_t x)
{
    return sin(x);
}

int16_t __kz_cos_int16(int16_t x)
{
    return cos(x);
}

int16_t __kz_atan2_int16(int16_t y, int16_t x)
{
    return atan2(y, x);
}

int32_t __kz_atan2_int32(int32_t y, int32_t x)
{
    return atan2(y, x);
}

complex32_t __kz_sumc32(const complex32_t x[4])
{
    complex32_t res = { 0, 0 };
    int i;

    for (i = 0; i < 4; ++i) {
        res.re += x[i].re;
        res.im += x[i].im;
    }

    return res;
}

int32_t __kz_v_sum_int32(int n, const int32_t *xs)
{
    int32_t sum = 0;
    int i = 0;

    for (i = 0; i < n; ++i)
        sum += xs[i];

    return sum;
}

complex16_t __kz_v_sum_complex16(int n, const complex16_t *xs)
{
    complex16_t res = { 0, 0 };
    int i;

    for (i = 0; i < n; ++i) {
        res.re += xs[i].re;
        res.im += xs[i].im;
    }

    return res;
}

void __kz_v_or(int n, const uint8_t *xs, const uint8_t *ys, uint8_t *out)
{
    int i;

    for (i = 0; i < n; ++i)
        out[i] = xs[i] | ys[i];
}

void __kz_sora_ifft(int n, const complex16_t *in, complex16_t *out)
{
}

void __kz_sora_fft(int n, const complex16_t *in, complex16_t *out)
{
}

int16_t __kz_viterbiSig11a_brick_decode_fast(int n, const int8_t svalue[48], const uint8_t *bitValue)
{
    return 0;
}

int16_t __kz_viterbi_brick_decode_fast(int n, const int8_t svalue[48], const uint8_t *bitValue)
{
    return 0;
}
