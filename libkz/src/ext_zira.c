/*
   Copyright (c) Microsoft Corporation
   All rights reserved.

   Licensed under the Apache License, Version 2.0 (the ""License""); you
   may not use this file except in compliance with the License. You may
   obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

   THIS CODE IS PROVIDED ON AN *AS IS* BASIS, WITHOUT WARRANTIES OR
   CONDITIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED, INCLUDING WITHOUT
   LIMITATION ANY IMPLIED WARRANTIES OR CONDITIONS OF TITLE, FITNESS FOR
   A PARTICULAR PURPOSE, MERCHANTABLITY OR NON-INFRINGEMENT.

   See the Apache Version 2.0 License for specific language governing
   permissions and limitations under the License.
*/

#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <xmmintrin.h>
#include <emmintrin.h>

#include <kz/ext.h>

#if defined(ZIRIA_COMPAT)
FORCEINLINE
void __kz_v_mul_complex16(int n, complex16_t *c, const complex16_t *a, const complex16_t *b, int32_t shift)
{
    const unsigned wlen = 4;
    const __m128i xmm6 = _mm_set1_epi32(0x0000FFFF);
    const __m128i xmm5 = _mm_set1_epi32(0xFFFF0000);
    const __m128i xmm4 = _mm_set1_epi32(0x00010000);

    __m128i* as = (__m128i*) a;
    __m128i* bs = (__m128i*) b;
    __m128i* cs = (__m128i*) c;
    for (int i = 0; i < n / wlen; i++){
        __m128i mx = _mm_loadu_si128(&as[i]);
        __m128i my = _mm_loadu_si128(&bs[i]);

        __m128i ms1 = _mm_xor_si128(mx, xmm5);
        ms1 = _mm_add_epi32(ms1, xmm4);

        __m128i ms2 = _mm_shufflehi_epi16(mx, _MM_SHUFFLE(2, 3, 0, 1));
        ms2 = _mm_shufflelo_epi16(ms2, _MM_SHUFFLE(2, 3, 0, 1));

        __m128i mre = _mm_srai_epi32(_mm_madd_epi16(ms1, my), shift);
        __m128i mim = _mm_srai_epi32(_mm_madd_epi16(ms2, my), shift);

        mre = _mm_and_si128(mre,xmm6);
        mim = _mm_and_si128(mim,xmm6);

        mim = _mm_slli_epi32(mim,0x10);

        _mm_storeu_si128(&cs[i], _mm_or_si128(mre, mim));
    }

    for (int i = (n / wlen) * wlen; i < n; i++){
        c[i].re = (a[i].re * b[i].re - a[i].im * b[i].im) >> shift;
        c[i].im = (a[i].re * b[i].im + a[i].im * b[i].re) >> shift;
    }
}
#endif /* defined(ZIRIA_COMPAT) */

#if defined(ZIRIA_COMPAT)
FORCEINLINE
void __kz_v_conj_mul_complex16_int32(int n, int32_t *re, int32_t *im, const complex16_t *a, const complex16_t *b)
{
  const unsigned wlen = 4;
  const __m128i xmm5 = _mm_set1_epi32(0xFFFF0000);
  const __m128i xmm4 = _mm_set1_epi32(0x00010000);

  __m128i* Xs = (__m128i*) a;
  __m128i* Ys = (__m128i*) b;
  __m128i* Res = (__m128i*) re;
  __m128i* Ims = (__m128i*) im;

  for (int i = 0; i < n / wlen; i++) {
      __m128i mx = _mm_loadu_si128(&Xs[i]);
      __m128i my = _mm_loadu_si128(&Ys[i]);

      __m128i ms2 = _mm_xor_si128(my, xmm5);
      ms2 = _mm_add_epi32(ms2, xmm4);

      ms2 = _mm_shufflehi_epi16(ms2, _MM_SHUFFLE(2, 3, 0, 1));
      ms2 = _mm_shufflelo_epi16(ms2, _MM_SHUFFLE(2, 3, 0, 1));

      _mm_storeu_si128(&Res[i], _mm_madd_epi16(my, mx));
      _mm_storeu_si128(&Ims[i], _mm_madd_epi16(ms2, mx));
  }

  for (int i = (n / wlen) * wlen; i < n; i++) {
      re[i] = a[i].re * b[i].re + a[i].im * b[i].im ;
      im[i] = a[i].im * b[i].re - a[i].re * b[i].im ;
  }
}
#endif /* defined(ZIRIA_COMPAT) */

#if defined(ZIRIA_COMPAT)
FORCEINLINE
void __kz_v_shift_right_complex16(int n, complex16_t *z, const complex16_t *x, int32_t shift)
{
    const unsigned wlen = 4;

    __m128i* Xs = (__m128i*) x;
    __m128i* Zs = (__m128i*) z;

    for (int i = 0; i < n / wlen; i++)
        _mm_storeu_si128(&Zs[i], _mm_srai_epi16(_mm_loadu_si128(&Xs[i]),shift));

    uint16_t* Ps = (uint16_t*) x;
    uint16_t* Qs = (uint16_t*) z;

    for (int i = (n / wlen) * wlen * 2; i < n * 2; i++)
        Qs[i] = Ps[i] >> shift;
}
#endif /* defined(ZIRIA_COMPAT) */
