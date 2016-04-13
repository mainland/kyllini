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

#define STATIC static
#define RESTRICT restrict

#endif /* !defined(KZ_TYPES_H) */
