#if !defined(KZ_DRIVER_H)
#define KZ_DRIVER_H

#include <stdio.h>
#include <stdlib.h>

#include <kz/types.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
    DEV_DUMMY = 0,
    DEV_MEMORY,
    DEV_FILE
} kz_dev_t;

typedef enum {
    MODE_TEXT = 0,
    MODE_BINARY
} kz_mode_t;

typedef struct {
    kz_dev_t  src_dev;
    kz_mode_t src_mode;
    char*     src;
    kz_dev_t  dst_dev;
    kz_mode_t dst_mode;
    char*     dst;
} kz_params_t;

typedef struct {
    kz_dev_t dev;
    void*    buf;
    size_t   len;
    size_t   idx;
} kz_buf_t;

void kz_main(const kz_params_t*);

void kz_error(const char*);

void         kz_init_input_bit(const kz_params_t*, kz_buf_t*);
void         kz_init_output_bit(const kz_params_t*, kz_buf_t*);
void         kz_cleanup_input_bit(const kz_params_t*, kz_buf_t*);
void         kz_cleanup_output_bit(const kz_params_t*, kz_buf_t*);
const bit_t* kz_input_bit(kz_buf_t*, size_t);
void         kz_output_bit(kz_buf_t*, const bit_t*, size_t);

void          kz_init_input_int8(const kz_params_t*, kz_buf_t*);
void          kz_init_output_int8(const kz_params_t*, kz_buf_t*);
void          kz_cleanup_input_int8(const kz_params_t*, kz_buf_t*);
void          kz_cleanup_output_int8(const kz_params_t*, kz_buf_t*);
const int8_t* kz_input_int8(kz_buf_t*, size_t);
void          kz_output_int8(kz_buf_t*, const int8_t*, size_t);

void           kz_init_input_int16(const kz_params_t*, kz_buf_t*);
void           kz_init_output_int16(const kz_params_t*, kz_buf_t*);
void           kz_cleanup_input_int16(const kz_params_t*, kz_buf_t*);
void           kz_cleanup_output_int16(const kz_params_t*, kz_buf_t*);
const int16_t* kz_input_int16(kz_buf_t*, size_t);
void           kz_output_int16(kz_buf_t*, const int16_t*, size_t);

void           kz_init_input_int32(const kz_params_t*, kz_buf_t*);
void           kz_init_output_int32(const kz_params_t*, kz_buf_t*);
void           kz_cleanup_input_int32(const kz_params_t*, kz_buf_t*);
void           kz_cleanup_output_int32(const kz_params_t*, kz_buf_t*);
const int32_t* kz_input_int32(kz_buf_t*, size_t);
void           kz_output_int32(kz_buf_t*, const int32_t*, size_t);

void           kz_init_input_uint8(const kz_params_t*, kz_buf_t*);
void           kz_init_output_uint8(const kz_params_t*, kz_buf_t*);
void           kz_cleanup_input_uint8(const kz_params_t*, kz_buf_t*);
void           kz_cleanup_output_uint8(const kz_params_t*, kz_buf_t*);
const uint8_t* kz_input_uint8(kz_buf_t*, size_t);
void           kz_output_uint8(kz_buf_t*, const uint8_t*, size_t);

void            kz_init_input_uint16(const kz_params_t*, kz_buf_t*);
void            kz_init_output_uint16(const kz_params_t*, kz_buf_t*);
void            kz_cleanup_input_uint16(const kz_params_t*, kz_buf_t*);
void            kz_cleanup_output_uint16(const kz_params_t*, kz_buf_t*);
const uint16_t* kz_input_uint16(kz_buf_t*, size_t);
void            kz_output_uint16(kz_buf_t*, const uint16_t*, size_t);

void            kz_init_input_uint32(const kz_params_t*, kz_buf_t*);
void            kz_init_output_uint32(const kz_params_t*, kz_buf_t*);
void            kz_cleanup_input_uint32(const kz_params_t*, kz_buf_t*);
void            kz_cleanup_output_uint32(const kz_params_t*, kz_buf_t*);
const uint32_t* kz_input_uint32(kz_buf_t*, size_t);
void            kz_output_uint32(kz_buf_t*, const uint32_t*, size_t);

void               kz_init_input_complex16(const kz_params_t*, kz_buf_t*);
void               kz_init_output_complex16(const kz_params_t*, kz_buf_t*);
void               kz_cleanup_input_complex16(const kz_params_t*, kz_buf_t*);
void               kz_cleanup_output_complex16(const kz_params_t*, kz_buf_t*);
const complex16_t* kz_input_complex16(kz_buf_t*, size_t);
void               kz_output_complex16(kz_buf_t*, const complex16_t*, size_t);

void               kz_init_input_complex32(const kz_params_t*, kz_buf_t*);
void               kz_init_output_complex32(const kz_params_t*, kz_buf_t*);
void               kz_cleanup_input_complex32(const kz_params_t*, kz_buf_t*);
void               kz_cleanup_output_complex32(const kz_params_t*, kz_buf_t*);
const complex32_t* kz_input_complex32(kz_buf_t*, size_t);
void               kz_output_complex32(kz_buf_t*, const complex32_t*, size_t);

void         kz_init_input_float(const kz_params_t*, kz_buf_t*);
void         kz_init_output_float(const kz_params_t*, kz_buf_t*);
void         kz_cleanup_input_float(const kz_params_t*, kz_buf_t*);
void         kz_cleanup_output_float(const kz_params_t*, kz_buf_t*);
const float* kz_input_float(kz_buf_t*, size_t);
void         kz_output_float(kz_buf_t*, const float*, size_t);

void          kz_init_input_double(const kz_params_t*, kz_buf_t*);
void          kz_init_output_double(const kz_params_t*, kz_buf_t*);
void          kz_cleanup_input_double(const kz_params_t*, kz_buf_t*);
void          kz_cleanup_output_double(const kz_params_t*, kz_buf_t*);
const double* kz_input_double(kz_buf_t*, size_t);
void          kz_output_double(kz_buf_t*, const double*, size_t);

void        kz_init_input_bytes(const kz_params_t*, kz_buf_t*);
void        kz_init_output_bytes(const kz_params_t*, kz_buf_t*);
void        kz_cleanup_input_bytes(const kz_params_t*, kz_buf_t*);
void        kz_cleanup_output_bytes(const kz_params_t*, kz_buf_t*);
const void* kz_input_bytes(kz_buf_t*, size_t);
void        kz_output_bytes(kz_buf_t*, void*, size_t);

#ifdef __cplusplus
}
#endif

#endif /* !defined(KZ_DRIVER_H) */
