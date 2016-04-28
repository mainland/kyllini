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

#if !defined(KZ_TYPES_H)
#define KZ_TYPES_H

#include <limits.h>
#include <stdint.h>

typedef uint8_t bit_t;

#define BIT_ARRAY_LEN(n) (((n) + BIT_ARRAY_ELEM_BITS - 1) / BIT_ARRAY_ELEM_BITS)
#define BIT_ARRAY_ELEM_BITS (sizeof(bit_t) * CHAR_BIT)

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

#if defined(WHOLEPROGRAM)
#define STATIC
#define RESTRICT
#else /* !defined(WHOLEPROGRAM) */
#define STATIC static
#define RESTRICT restrict
#endif /* !defined(WHOLEPROGRAM) */

#if defined(__GNUC__) || defined(__clang__) || defined(__INTEL_COMPILER)
#define ALIGN __attribute__((aligned(16)))
#else
#define ALIGN
#endif

#if defined(WHOLEPROGRAM)
#if defined(__GNUC__) || defined(__clang__) || defined(__INTEL_COMPILER)
#define FORCEINLINE inline __attribute__((always_inline))
#else
#define FORCEINLINE
#endif
#else /* !defined(WHOLEPROGRAM) */
#define FORCEINLINE
#endif /* !defined(WHOLEPROGRAM) */

#endif /* !defined(KZ_TYPES_H) */
