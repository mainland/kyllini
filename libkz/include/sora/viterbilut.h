#pragma once

#include <emmintrin.h>
#include <stdint.h>


#include <tmmintrin.h>

// hepler to reverse vector for taking endianness into account
static inline __m128i
_mm_bswap_si128 (__m128i x)
{
        // Reverse order of all bytes in the 128-bit word.

#ifdef __SSSE3__
        return _mm_shuffle_epi8(x,
                _mm_set_epi8(
                         0,  1,  2,  3,
                         4,  5,  6,  7,
                         8,  9, 10, 11,
                        12, 13, 14, 15));
#else
        // Swap bytes in each 16-bit word:
        __m128i a = _mm_or_si128(
                _mm_slli_epi16(x, 8),
                _mm_srli_epi16(x, 8));

        // Reverse all 16-bit words in 64-bit halves:
        a = _mm_shufflelo_epi16(a, _MM_SHUFFLE(0, 1, 2, 3));
        a = _mm_shufflehi_epi16(a, _MM_SHUFFLE(0, 1, 2, 3));

        // Reverse 64-bit halves:
        return _mm_shuffle_epi32(a, _MM_SHUFFLE(1, 0, 3, 2));
#endif
}


extern const __m128i ALL_INVERSE_ONE =
  _mm_bswap_si128(
  _mm_set_epi8 ( int8_t(0xFE), int8_t(0xFE), int8_t(0xFE), int8_t(0xFE),
                 int8_t(0xFE), int8_t(0xFE), int8_t(0xFE), int8_t(0xFE),
                 int8_t(0xFE), int8_t(0xFE), int8_t(0xFE), int8_t(0xFE),
                 int8_t(0xFE), int8_t(0xFE), int8_t(0xFE), int8_t(0xFE) )
);

extern const __m128i ALL_ONE =
  _mm_bswap_si128(
  _mm_set_epi8 ( 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
                 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01 )
);

extern const __m128i ALL_M128 =
  _mm_bswap_si128(
  _mm_set_epi8 ( int8_t(0x80), int8_t(0x80), int8_t(0x80), int8_t(0x80),
                 int8_t(0x80), int8_t(0x80), int8_t(0x80), int8_t(0x80),
                 int8_t(0x80), int8_t(0x80), int8_t(0x80), int8_t(0x80),
                 int8_t(0x80), int8_t(0x80), int8_t(0x80), int8_t(0x80) )
);

extern const __m128i ALL_INIT =
  _mm_bswap_si128(
  _mm_set_epi8 ( 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
                 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30 )
);

extern const __m128i ALL_INIT0 =
  _mm_bswap_si128(
  _mm_set_epi8( 0x00, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
                0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30 )
);

extern const __m128i INDEXES[4] alignas(16) = {
  _mm_bswap_si128(
  _mm_set_epi8 ( 0x00, 0x04, 0x08, 0x0C, 0x10, 0x14, 0x18, 0x1C,
                 0x20, 0x24, 0x28, 0x2C, 0x30, 0x34, 0x38, 0x3C )
),

  _mm_bswap_si128(
  _mm_set_epi8 ( 0x40, 0x44, 0x48, 0x4C, 0x50, 0x54, 0x58, 0x5C,
                 0x60, 0x64, 0x68, 0x6C, 0x70, 0x74, 0x78, 0x7C )
),

  _mm_bswap_si128(
  _mm_set_epi8 ( int8_t(0x80), int8_t(0x84), int8_t(0x88), int8_t(0x8C),
                 int8_t(0x90), int8_t(0x94), int8_t(0x98), int8_t(0x9C),
                 int8_t(0xA0), int8_t(0xA4), int8_t(0xA8), int8_t(0xAC),
                 int8_t(0xB0), int8_t(0xB4), int8_t(0xB8), int8_t(0xBC) )
),

  _mm_bswap_si128(
  _mm_set_epi8 ( int8_t(0xC0), int8_t(0xC4), int8_t(0xC8), int8_t(0xCC),
                 int8_t(0xD0), int8_t(0xD4), int8_t(0xD8), int8_t(0xDC),
                 int8_t(0xE0), int8_t(0xE4), int8_t(0xE8), int8_t(0xEC),
                 int8_t(0xF0), int8_t(0xF4), int8_t(0xF8), int8_t(0xFC) )
)

};

//extern const uint8_t __attribute__((weak)) VIT_MA[64][8 * SOFT_RANGE] =
extern const __m128i VIT_MA[64] = {
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14,  0, 14, 14,  0, 14,  0, 14,  0, 14,  0,  0, 14,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0, 14,  0,  0, 14,  0, 14,  0, 14,  0, 14, 14,  0, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14,  0, 14, 14,  0, 14,  0, 14,  0, 14,  0,  0, 14,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0, 14,  0,  0, 14,  0, 14,  0, 14,  0, 14, 14,  0, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0, 14,  0,  0, 14,  0, 14,  0, 14,  0, 14, 14,  0, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14,  0, 14, 14,  0, 14,  0, 14,  0, 14,  0,  0, 14,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0, 14,  0,  0, 14,  0, 14,  0, 14,  0, 14, 14,  0, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14,  0, 14, 14,  0, 14,  0, 14,  0, 14,  0,  0, 14,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12,  2, 12, 12,  2, 12,  2, 12,  2, 12,  2,  2, 12,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2, 12,  2,  2, 12,  2, 12,  2, 12,  2, 12, 12,  2, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12,  2, 12, 12,  2, 12,  2, 12,  2, 12,  2,  2, 12,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2, 12,  2,  2, 12,  2, 12,  2, 12,  2, 12, 12,  2, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2, 12,  2,  2, 12,  2, 12,  2, 12,  2, 12, 12,  2, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12,  2, 12, 12,  2, 12,  2, 12,  2, 12,  2,  2, 12,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2, 12,  2,  2, 12,  2, 12,  2, 12,  2, 12, 12,  2, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12,  2, 12, 12,  2, 12,  2, 12,  2, 12,  2,  2, 12,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10,  4, 10, 10,  4, 10,  4, 10,  4, 10,  4,  4, 10,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4, 10,  4,  4, 10,  4, 10,  4, 10,  4, 10, 10,  4, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10,  4, 10, 10,  4, 10,  4, 10,  4, 10,  4,  4, 10,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4, 10,  4,  4, 10,  4, 10,  4, 10,  4, 10, 10,  4, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4, 10,  4,  4, 10,  4, 10,  4, 10,  4, 10, 10,  4, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10,  4, 10, 10,  4, 10,  4, 10,  4, 10,  4,  4, 10,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4, 10,  4,  4, 10,  4, 10,  4, 10,  4, 10, 10,  4, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10,  4, 10, 10,  4, 10,  4, 10,  4, 10,  4,  4, 10,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  6,  8,  8,  6,  8,  6,  8,  6,  8,  6,  6,  8,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  8,  6,  6,  8,  6,  8,  6,  8,  6,  8,  8,  6,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  6,  8,  8,  6,  8,  6,  8,  6,  8,  6,  6,  8,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  8,  6,  6,  8,  6,  8,  6,  8,  6,  8,  8,  6,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  8,  6,  6,  8,  6,  8,  6,  8,  6,  8,  8,  6,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  6,  8,  8,  6,  8,  6,  8,  6,  8,  6,  6,  8,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  8,  6,  6,  8,  6,  8,  6,  8,  6,  8,  8,  6,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  6,  8,  8,  6,  8,  6,  8,  6,  8,  6,  6,  8,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  8,  6,  6,  8,  6,  8,  6,  8,  6,  8,  8,  6,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  6,  8,  8,  6,  8,  6,  8,  6,  8,  6,  6,  8,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  8,  6,  6,  8,  6,  8,  6,  8,  6,  8,  8,  6,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  6,  8,  8,  6,  8,  6,  8,  6,  8,  6,  6,  8,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  6,  8,  8,  6,  8,  6,  8,  6,  8,  6,  6,  8,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  8,  6,  6,  8,  6,  8,  6,  8,  6,  8,  8,  6,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  6,  8,  8,  6,  8,  6,  8,  6,  8,  6,  6,  8,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  8,  6,  6,  8,  6,  8,  6,  8,  6,  8,  8,  6,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4, 10,  4,  4, 10,  4, 10,  4, 10,  4, 10, 10,  4, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10,  4, 10, 10,  4, 10,  4, 10,  4, 10,  4,  4, 10,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4, 10,  4,  4, 10,  4, 10,  4, 10,  4, 10, 10,  4, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10,  4, 10, 10,  4, 10,  4, 10,  4, 10,  4,  4, 10,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10,  4, 10, 10,  4, 10,  4, 10,  4, 10,  4,  4, 10,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4, 10,  4,  4, 10,  4, 10,  4, 10,  4, 10, 10,  4, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10,  4, 10, 10,  4, 10,  4, 10,  4, 10,  4,  4, 10,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4, 10,  4,  4, 10,  4, 10,  4, 10,  4, 10, 10,  4, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2, 12,  2,  2, 12,  2, 12,  2, 12,  2, 12, 12,  2, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12,  2, 12, 12,  2, 12,  2, 12,  2, 12,  2,  2, 12,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2, 12,  2,  2, 12,  2, 12,  2, 12,  2, 12, 12,  2, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12,  2, 12, 12,  2, 12,  2, 12,  2, 12,  2,  2, 12,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12,  2, 12, 12,  2, 12,  2, 12,  2, 12,  2,  2, 12,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2, 12,  2,  2, 12,  2, 12,  2, 12,  2, 12, 12,  2, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12,  2, 12, 12,  2, 12,  2, 12,  2, 12,  2,  2, 12,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2, 12,  2,  2, 12,  2, 12,  2, 12,  2, 12, 12,  2, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0, 14,  0,  0, 14,  0, 14,  0, 14,  0, 14, 14,  0, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14,  0, 14, 14,  0, 14,  0, 14,  0, 14,  0,  0, 14,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0, 14,  0,  0, 14,  0, 14,  0, 14,  0, 14, 14,  0, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14,  0, 14, 14,  0, 14,  0, 14,  0, 14,  0,  0, 14,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14,  0, 14, 14,  0, 14,  0, 14,  0, 14,  0,  0, 14,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0, 14,  0,  0, 14,  0, 14,  0, 14,  0, 14, 14,  0, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14,  0, 14, 14,  0, 14,  0, 14,  0, 14,  0,  0, 14,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0, 14,  0,  0, 14,  0, 14,  0, 14,  0, 14, 14,  0, 14,  0)
),
};

//extern const uint8_t __attribute__((weak)) VIT_MB[16*64] = {
extern const __m128i VIT_MB[64] = {
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14, 14,  0, 14,  0,  0, 14, 14,  0,  0, 14,  0, 14, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0,  0, 14,  0, 14, 14,  0,  0, 14, 14,  0, 14,  0,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14, 14,  0, 14,  0,  0, 14, 14,  0,  0, 14,  0, 14, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0,  0, 14,  0, 14, 14,  0,  0, 14, 14,  0, 14,  0,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14, 14,  0, 14,  0,  0, 14, 14,  0,  0, 14,  0, 14, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0,  0, 14,  0, 14, 14,  0,  0, 14, 14,  0, 14,  0,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14, 14,  0, 14,  0,  0, 14, 14,  0,  0, 14,  0, 14, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0,  0, 14,  0, 14, 14,  0,  0, 14, 14,  0, 14,  0,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12, 12,  2, 12,  2,  2, 12, 12,  2,  2, 12,  2, 12, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2,  2, 12,  2, 12, 12,  2,  2, 12, 12,  2, 12,  2,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12, 12,  2, 12,  2,  2, 12, 12,  2,  2, 12,  2, 12, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2,  2, 12,  2, 12, 12,  2,  2, 12, 12,  2, 12,  2,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12, 12,  2, 12,  2,  2, 12, 12,  2,  2, 12,  2, 12, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2,  2, 12,  2, 12, 12,  2,  2, 12, 12,  2, 12,  2,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12, 12,  2, 12,  2,  2, 12, 12,  2,  2, 12,  2, 12, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2,  2, 12,  2, 12, 12,  2,  2, 12, 12,  2, 12,  2,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10, 10,  4, 10,  4,  4, 10, 10,  4,  4, 10,  4, 10, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4,  4, 10,  4, 10, 10,  4,  4, 10, 10,  4, 10,  4,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10, 10,  4, 10,  4,  4, 10, 10,  4,  4, 10,  4, 10, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4,  4, 10,  4, 10, 10,  4,  4, 10, 10,  4, 10,  4,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10, 10,  4, 10,  4,  4, 10, 10,  4,  4, 10,  4, 10, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4,  4, 10,  4, 10, 10,  4,  4, 10, 10,  4, 10,  4,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10, 10,  4, 10,  4,  4, 10, 10,  4,  4, 10,  4, 10, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4,  4, 10,  4, 10, 10,  4,  4, 10, 10,  4, 10,  4,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  8,  6,  8,  6,  6,  8,  8,  6,  6,  8,  6,  8,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  6,  8,  6,  8,  8,  6,  6,  8,  8,  6,  8,  6,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  8,  6,  8,  6,  6,  8,  8,  6,  6,  8,  6,  8,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  6,  8,  6,  8,  8,  6,  6,  8,  8,  6,  8,  6,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  8,  6,  8,  6,  6,  8,  8,  6,  6,  8,  6,  8,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  6,  8,  6,  8,  8,  6,  6,  8,  8,  6,  8,  6,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  8,  6,  8,  6,  6,  8,  8,  6,  6,  8,  6,  8,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  6,  8,  6,  8,  8,  6,  6,  8,  8,  6,  8,  6,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  6,  8,  6,  8,  8,  6,  6,  8,  8,  6,  8,  6,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  8,  6,  8,  6,  6,  8,  8,  6,  6,  8,  6,  8,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  6,  8,  6,  8,  8,  6,  6,  8,  8,  6,  8,  6,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  8,  6,  8,  6,  6,  8,  8,  6,  6,  8,  6,  8,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  6,  8,  6,  8,  8,  6,  6,  8,  8,  6,  8,  6,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  8,  6,  8,  6,  6,  8,  8,  6,  6,  8,  6,  8,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 8,  6,  6,  8,  6,  8,  8,  6,  6,  8,  8,  6,  8,  6,  6,  8)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 6,  8,  8,  6,  8,  6,  6,  8,  8,  6,  6,  8,  6,  8,  8,  6)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4,  4, 10,  4, 10, 10,  4,  4, 10, 10,  4, 10,  4,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10, 10,  4, 10,  4,  4, 10, 10,  4,  4, 10,  4, 10, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4,  4, 10,  4, 10, 10,  4,  4, 10, 10,  4, 10,  4,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10, 10,  4, 10,  4,  4, 10, 10,  4,  4, 10,  4, 10, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4,  4, 10,  4, 10, 10,  4,  4, 10, 10,  4, 10,  4,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10, 10,  4, 10,  4,  4, 10, 10,  4,  4, 10,  4, 10, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 (10,  4,  4, 10,  4, 10, 10,  4,  4, 10, 10,  4, 10,  4,  4, 10)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 4, 10, 10,  4, 10,  4,  4, 10, 10,  4,  4, 10,  4, 10, 10,  4)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2,  2, 12,  2, 12, 12,  2,  2, 12, 12,  2, 12,  2,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12, 12,  2, 12,  2,  2, 12, 12,  2,  2, 12,  2, 12, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2,  2, 12,  2, 12, 12,  2,  2, 12, 12,  2, 12,  2,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12, 12,  2, 12,  2,  2, 12, 12,  2,  2, 12,  2, 12, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2,  2, 12,  2, 12, 12,  2,  2, 12, 12,  2, 12,  2,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12, 12,  2, 12,  2,  2, 12, 12,  2,  2, 12,  2, 12, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 (12,  2,  2, 12,  2, 12, 12,  2,  2, 12, 12,  2, 12,  2,  2, 12)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 2, 12, 12,  2, 12,  2,  2, 12, 12,  2,  2, 12,  2, 12, 12,  2)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0,  0, 14,  0, 14, 14,  0,  0, 14, 14,  0, 14,  0,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14, 14,  0, 14,  0,  0, 14, 14,  0,  0, 14,  0, 14, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0,  0, 14,  0, 14, 14,  0,  0, 14, 14,  0, 14,  0,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14, 14,  0, 14,  0,  0, 14, 14,  0,  0, 14,  0, 14, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0,  0, 14,  0, 14, 14,  0,  0, 14, 14,  0, 14,  0,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14, 14,  0, 14,  0,  0, 14, 14,  0,  0, 14,  0, 14, 14,  0)
),
  _mm_bswap_si128(
  _mm_set_epi8 (14,  0,  0, 14,  0, 14, 14,  0,  0, 14, 14,  0, 14,  0,  0, 14)
),
  _mm_bswap_si128(
  _mm_set_epi8 ( 0, 14, 14,  0, 14,  0,  0, 14, 14,  0,  0, 14,  0, 14, 14,  0)
)
};
