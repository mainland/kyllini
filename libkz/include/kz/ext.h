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

#if !defined(KZ_EXT_H)
#define KZ_EXT_H

#include <kz/types.h>

#define ZIRIA_COMPAT

#ifdef __cplusplus
extern "C" {
#endif

void __kz_butterfly16_fft(int n, complex16_t *in);
void __kz_butterfly128_ifft(int n, complex16_t *in);
void __kz_butterfly32_ifft(int n, complex16_t *in);
void __kz_butterfly8_ifft(int n, complex16_t *in);

void __kz_hexprint_int8(int n, const int8_t *a, int32_t length);

void __kz_bits_to_int8(int n, int m, int8_t *dst, const uint8_t *src);
void __kz_int8_to_bits(int n, int m, uint8_t *dst, const int8_t *src);

void __kz_zero_bit(int n, bit_t *x);
void __kz_zero_int8(int n, int8_t *x);
void __kz_zero_int16(int n, int16_t *x);
void __kz_zero_int32(int n, int32_t *x);
void __kz_zero_complex8(int n, complex8_t *x);
void __kz_zero_complex16(int n, complex16_t *x);
void __kz_zero_complex32(int n, complex32_t *x);

void __kz_copy_int8(int n, int m, int8_t *dst, const int8_t *src, int32_t len);
void __kz_copy_int16(int n, int m, int16_t *dst, const int16_t *src, int32_t len);
void __kz_copy_int32(int n, int m, int32_t *dst, const int32_t *src, int32_t len);
void __kz_copy_complex8(int n, int m, complex8_t *dst, const complex8_t *src, int32_t len);
void __kz_copy_complex16(int n, int m, complex16_t *dst, const complex16_t *src, int32_t len);
void __kz_copy_complex32(int n, int m, complex32_t *dst, const complex32_t *src, int32_t len);

double __kz_sqrt(double d);
double __kz_log2(double d);

int32_t __kz_round_int32(double d);
int32_t __kz_ceil_int32(double d);

int16_t __kz_sin_int16(int16_t x);
int16_t __kz_cos_int16(int16_t x);
int16_t __kz_atan2_int16(int16_t y, int16_t x);

int32_t __kz_atan2_int32(int32_t y, int32_t x);

complex32_t __kz_sumc32(const complex32_t x[4]);

void __kz_v_add_int16(int n, int16_t *c, const int16_t *a, const int16_t *b);
void __kz_v_add_int32(int n, int32_t *c, const int32_t *a, const int32_t *b);
void __kz_v_add_complex16(int n, complex16_t *c, const complex16_t *a, const complex16_t *b);
void __kz_v_add_complex32(int n, complex32_t *c, const complex32_t *a, const complex32_t *b);

void __kz_v_sub_int16(int n_, int16_t *c, const int16_t *a, const int16_t *b);
void __kz_v_sub_int32(int n_, int32_t *c, const int32_t *a, const int32_t *b);
void __kz_v_sub_complex16(int n_, complex16_t *c, const complex16_t *a, const complex16_t *b);
void __kz_v_sub_complex32(int n_, complex32_t *c, const complex32_t *a, const complex32_t *b);

void __kz_v_hadd_int32(int32_t *zz__460, const int32_t x__461[4]);
void __kz_v_hadd_complex16(complex16_t *z, const complex16_t x[4]);

void __kz_v_mul_complex16(int n, complex16_t *c, const complex16_t *a, const complex16_t *b, int32_t shift);
void __kz_v_mul_complex16_int32(int n, int32_t *re, int32_t *im, const complex16_t *a, const complex16_t *b);

void __kz_v_conj_mul_complex16(int n, complex16_t *c, const complex16_t *a, const complex16_t *b, int32_t shift);
void __kz_v_conj_mul_complex16_int32(int n, int32_t *re, int32_t *im, const complex16_t *a, const complex16_t *b);

void __kz_v_shift_right_int32(int n, int32_t *z, const int32_t *x, int32_t shift);
void __kz_v_shift_right_int16(int n, int16_t *z, const int16_t *x, int32_t shift);
void __kz_v_shift_right_complex16(int n, complex16_t *z, const complex16_t *x, int32_t shift);
void __kz_v_shift_right_complex32(int n, complex32_t *z, const complex32_t *x, int32_t shift);

void __kz_v_shift_left_int32(int n, int32_t *z, const int32_t *x, int32_t shift);
void __kz_v_shift_left_int16(int n, int16_t *z, const int16_t *x, int32_t shift);
void __kz_v_shift_left_complex16(int n, complex16_t *z, const complex16_t *x, int32_t shift);
void __kz_v_shift_left_complex32(int n, complex32_t *z, const complex32_t *x, int32_t shift);

int16_t     __kz_v_sum_int16(int n, const int16_t *xs);
int32_t     __kz_v_sum_int32(int n, const int32_t *xs);
complex16_t __kz_v_sum_complex16(int n, const complex16_t *xs);
complex32_t __kz_v_sum_complex32(int n, const complex32_t *xs);

void __kz_v_or(int n, const uint8_t *in1, const uint8_t *in2, uint8_t *out);
void __kz_v_and(int n, const uint8_t *in1, const uint8_t *in2, uint8_t *out);
void __kz_v_xor(int n, const uint8_t *in1, const uint8_t *in2, uint8_t *out);
void __kz_v_andnot(int n, const uint8_t *in1, const uint8_t *in2, uint8_t *out);

void __kz_permutatew1313(const complex16_t x[4], complex16_t *y);
void __kz_interleave_loww(const complex16_t x[4], const complex16_t y[4], complex16_t* z);

void __kz_sora_ifft(int n, const complex16_t *in, complex16_t *out);
void __kz_sora_fft(int n, const complex16_t *in, complex16_t *out);

void __kz_viterbi_brick_init_fast(int32_t frame_length, int16_t code_rate, int16_t depth);
int16_t __kz_viterbiSig11a_brick_decode_fast(int n, const int8_t svalue[48], uint8_t *bitValue);
int16_t __kz_viterbi_brick_decode_fast(int n, const int8_t svalue[48], uint8_t *bitValue);

#ifdef __cplusplus
}
#endif

#endif /* !defined(KZ_EXT_H) */
