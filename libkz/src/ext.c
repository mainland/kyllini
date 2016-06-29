/*
Copyright (c) 2015-2016
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

#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <kz/ext.h>

FORCEINLINE
void __kz_bits_to_int8(int n, int m, int8_t *dst, const uint8_t *src)
{
    memcpy(dst, src, n);
}

FORCEINLINE
void __kz_int8_to_bits(int n, int m, uint8_t *dst, const int8_t *src)
{
    memcpy(dst, src, m);
}

FORCEINLINE
void __kz_hexprint_int8(int n, const int8_t *a, int32_t len)
{
    int i;

    for (i = 0; i < len; i++)
        printf("%02X ", a[i]);
}

FORCEINLINE
void __kz_zero_bit(int n, bit_t *x)
{
    memset(x, 0, n / BIT_ARRAY_ELEM_BITS);

    if (n % BIT_ARRAY_ELEM_BITS != 0) {
        bit_t mask = ~((1 << (n % BIT_ARRAY_ELEM_BITS)) - 1);

        x[n / BIT_ARRAY_ELEM_BITS] &= mask;
    }
}

FORCEINLINE
void __kz_zero_int8(int n, int8_t *x)
{
    memset(x, 0, n*sizeof(int8_t));
}

FORCEINLINE
void __kz_zero_int16(int n, int16_t *x)
{
    memset(x, 0, n*sizeof(int16_t));
}

FORCEINLINE
void __kz_zero_int32(int n, int32_t *x)
{
    memset(x, 0, n*sizeof(int32_t));
}

FORCEINLINE
void __kz_zero_complex8(int n, complex8_t *x)
{
    memset(x, 0, n*sizeof(complex8_t));
}

FORCEINLINE
void __kz_zero_complex16(int n, complex16_t *x)
{
    memset(x, 0, n*sizeof(complex16_t));
}

FORCEINLINE
void __kz_zero_complex32(int n, complex32_t *x)
{
    memset(x, 0, n*sizeof(complex32_t));
}

FORCEINLINE
void __kz_copy_int16(int n, int m, int16_t *dst, const int16_t *src, int32_t len)
{
    memcpy(dst, src, len*sizeof(int16_t));
}

FORCEINLINE
double __kz_sqrt(double d)
{
    return sqrt(d);
}

FORCEINLINE
double __kz_log2(double d)
{
    return log(d) / log(2.0);
}

FORCEINLINE
int32_t __kz_round_int32(double d)
{
    return round(d);
}

FORCEINLINE
int32_t __kz_ceil_int32(double d)
{
    return ceil(d);
}

FORCEINLINE
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

FORCEINLINE
void __kz_v_add_int16(int n, int16_t *c, const int16_t *a, const int16_t *b)
{
    int i;

    for (i = 0; i < n; ++i)
        c[i] = a[i] + b[i];
}

FORCEINLINE
void __kz_v_add_int32(int n, int32_t *c, const int32_t *a, const int32_t *b)
{
    int i;

    for (i = 0; i < n; ++i)
        c[i] = a[i] + b[i];
}

FORCEINLINE
void __kz_v_add_complex16(int n, complex16_t *c, const complex16_t *a, const complex16_t *b)
{
    int i;

    for (i = 0; i < n; ++i) {
        c[i].re = a[i].re + b[i].re;
        c[i].im = a[i].im + b[i].im;
    }
}

FORCEINLINE
void __kz_v_add_complex32(int n, complex32_t *c, const complex32_t *a, const complex32_t *b)
{
    int i;

    for (i = 0; i < n; ++i) {
        c[i].re = a[i].re + b[i].re;
        c[i].im = a[i].im + b[i].im;
    }
}

FORCEINLINE
void __kz_v_sub_int16(int n, int16_t *c, const int16_t *a, const int16_t *b)
{
    int i;

    for (i = 0; i < n; ++i)
        c[i] = a[i] - b[i];
}

FORCEINLINE
void __kz_v_sub_int32(int n, int32_t *c, const int32_t *a, const int32_t *b)
{
    int i;

    for (i = 0; i < n; ++i)
        c[i] = a[i] - b[i];
}

FORCEINLINE
void __kz_v_sub_complex16(int n, complex16_t *c, const complex16_t *a, const complex16_t *b)
{
    int i;

    for (i = 0; i < n; ++i) {
        c[i].re = a[i].re - b[i].re;
        c[i].im = a[i].im - b[i].im;
    }
}

FORCEINLINE
void __kz_v_sub_complex32(int n, complex32_t *c, const complex32_t *a, const complex32_t *b)
{
    int i;

    for (i = 0; i < n; ++i) {
        c[i].re = a[i].re - b[i].re;
        c[i].im = a[i].im - b[i].im;
    }
}

FORCEINLINE
void __kz_v_hadd_int32(int32_t *z, const int32_t x[4])
{
    int32_t y;

    y = x[0] + x[1] + x[2] + x[3];

    z[0] = y;
    z[1] = y;
    z[2] = y;
    z[3] = y;
}

FORCEINLINE
void __kz_v_hadd_complex16(complex16_t *z, const complex16_t x[4])
{
    int16_t re;
    int16_t im;

    re = x[0].re + x[1].re + x[2].re + x[3].re;
    im = x[0].im + x[1].im + x[2].im + x[3].im;

    z[0].re = re;
    z[1].re = re;
    z[2].re = re;
    z[3].re = re;

    z[0].im = im;
    z[1].im = im;
    z[2].im = im;
    z[3].im = im;
}

FORCEINLINE
void __kz_v_mul_complex16(int n, complex16_t *c, const complex16_t *a, const complex16_t *b, int32_t shift)
{
    int i;

    for (i = 0; i < n; ++i) {
        c[i].re = (a[i].re * b[i].re - a[i].im * b[i].im) >> shift;
        c[i].im = (a[i].re * b[i].im + a[i].im * b[i].re) >> shift;
    }
}

FORCEINLINE
void __kz_v_mul_complex16_int32(int n, int32_t *re, int32_t *im, const complex16_t *a, const complex16_t *b)
{
    int i;

    for (i = 0; i < n; ++i) {
        re[i] = a[i].re * b[i].re + a[i].im * b[i].im;
        im[i] = a[i].re * b[i].im - a[i].im * b[i].re;
    }
}

FORCEINLINE
void __kz_v_conj_mul_complex16(int n, complex16_t *c, const complex16_t *a, const complex16_t *b, int32_t shift)
{
    int i;

    for (i = 0; i < n; ++i) {
        c[i].re = (a[i].re * b[i].re + a[i].im * b[i].im) >> shift;
        c[i].im = (a[i].im * b[i].re - a[i].re * b[i].im) >> shift;
    }
}

FORCEINLINE
void __kz_v_conj_mul_complex16_int32(int n, int32_t *re, int32_t *im, const complex16_t *a, const complex16_t *b)
{
    int i;

    for (i = 0; i < n; ++i) {
        re[i] = a[i].re * b[i].re + a[i].im * b[i].im;
        im[i] = a[i].im * b[i].re - a[i].re * b[i].im;
    }
}

FORCEINLINE
void __kz_v_shift_right_int16(int n, int16_t *z, const int16_t *x, int32_t shift)
{
    int i;

    for (i = 0; i < n; ++i)
        z[i] = x[i] >> shift;
}

FORCEINLINE
void __kz_v_shift_right_int32(int n, int32_t *z, const int32_t *x, int32_t shift)
{
    int i;

    for (i = 0; i < n; ++i)
        z[i] = x[i] >> shift;
}

FORCEINLINE
void __kz_v_shift_right_complex16(int n, complex16_t *z, const complex16_t *x, int32_t shift)
{
    int i;

    for (i = 0; i < n; ++i) {
        z[i].re = x[i].re >> shift;
        z[i].im = x[i].im >> shift;
    }
}

FORCEINLINE
void __kz_v_shift_right_complex32(int n, complex32_t *z, const complex32_t *x, int32_t shift)
{
    int i;

    for (i = 0; i < n; ++i) {
        z[i].re = x[i].re >> shift;
        z[i].im = x[i].im >> shift;
    }
}

FORCEINLINE
void __kz_v_shift_left_int16(int n, int16_t *z, const int16_t *x, int32_t shift)
{
    int i;

    for (i = 0; i < n; ++i)
        z[i] = x[i] << shift;
}

FORCEINLINE
void __kz_v_shift_left_int32(int n, int32_t *z, const int32_t *x, int32_t shift)
{
    int i;

    for (i = 0; i < n; ++i)
        z[i] = x[i] << shift;
}

FORCEINLINE
void __kz_v_shift_left_complex16(int n, complex16_t *z, const complex16_t *x, int32_t shift)
{
    int i;

    for (i = 0; i < n; ++i) {
        z[i].re = x[i].re << shift;
        z[i].im = x[i].im << shift;
    }
}

FORCEINLINE
void __kz_v_shift_left_complex32(int n, complex32_t *z, const complex32_t *x, int32_t shift)
{
    int i;

    for (i = 0; i < n; ++i) {
        z[i].re = x[i].re << shift;
        z[i].im = x[i].im << shift;
    }
}

FORCEINLINE
int16_t __kz_v_sum_int16(int n, const int16_t *xs)
{
    int16_t sum = 0;
    int i = 0;

    for (i = 0; i < n; ++i)
        sum += xs[i];

    return sum;
}

FORCEINLINE
int32_t __kz_v_sum_int32(int n, const int32_t *xs)
{
    int32_t sum = 0;
    int i = 0;

    for (i = 0; i < n; ++i)
        sum += xs[i];

    return sum;
}

FORCEINLINE
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

FORCEINLINE
complex32_t __kz_v_sum_complex32(int n, const complex32_t *xs)
{
    complex32_t res = { 0, 0 };
    int i;

    for (i = 0; i < n; ++i) {
        res.re += xs[i].re;
        res.im += xs[i].im;
    }

    return res;
}

FORCEINLINE
void __kz_v_or(int n, const uint8_t *xs, const uint8_t *ys, uint8_t *out)
{
    int i;

    for (i = 0; i < BIT_ARRAY_LEN(n); ++i)
        out[i] = xs[i] | ys[i];
}

FORCEINLINE
void __kz_v_and(int n, const uint8_t *xs, const uint8_t *ys, uint8_t *out)
{
    int i;

    for (i = 0; i < BIT_ARRAY_LEN(n); ++i)
        out[i] = xs[i] & ys[i];
}

FORCEINLINE
void __kz_v_xor(int n, const uint8_t *xs, const uint8_t *ys, uint8_t *out)
{
    int i;

    for (i = 0; i < BIT_ARRAY_LEN(n); ++i)
        out[i] = xs[i] ^ ys[i];
}

FORCEINLINE
void __kz_v_andnot(int n, const uint8_t *xs, const uint8_t *ys, uint8_t *out)
{
    int i;

    for (i = 0; i < BIT_ARRAY_LEN(n); ++i)
        out[i] = (~xs[i]) & ys[i];
}
