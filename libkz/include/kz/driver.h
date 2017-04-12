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
    int       dummy_samples;
} kz_params_t;

typedef struct {
    kz_dev_t dev;
    void*    buf;
    size_t   len;
    size_t   idx;
    int      dummy_samples;
} kz_buf_t;

void kz_main(const kz_params_t*);

void kz_assert(int flag, const char* loc, const char *format, ...)
    __attribute__((format (printf, 3, 4)));
void kz_check_error(int err, const char* loc, const char *format, ...)
    __attribute__((format (printf, 3, 4)));

#define kz_zero(x, n) bzero(x, n)

void kz_error(const char*);

long double kz_get_cpu_time(void);
long double kz_get_real_time(void);

void         kz_init_input_bit(const kz_params_t*, kz_buf_t*);
void         kz_init_output_bit(const kz_params_t*, kz_buf_t*);
void         kz_cleanup_input_bit(const kz_params_t*, kz_buf_t*);
void         kz_cleanup_output_bit(const kz_params_t*, kz_buf_t*);
const bit_t* kz_input_bit(kz_buf_t*, size_t);
void         kz_output_bit(kz_buf_t*, const bit_t*, size_t);

void       kz_init_input_int(const kz_params_t*, kz_buf_t*);
void       kz_init_output_int(const kz_params_t*, kz_buf_t*);
void       kz_cleanup_input_int(const kz_params_t*, kz_buf_t*);
void       kz_cleanup_output_int(const kz_params_t*, kz_buf_t*);
const int* kz_input_int(kz_buf_t*, size_t);
void       kz_output_int(kz_buf_t*, const int*, size_t);

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

void            kz_init_input_uint(const kz_params_t*, kz_buf_t*);
void            kz_init_output_uint(const kz_params_t*, kz_buf_t*);
void            kz_cleanup_input_uint(const kz_params_t*, kz_buf_t*);
void            kz_cleanup_output_uint(const kz_params_t*, kz_buf_t*);
const unsigned* kz_input_uint(kz_buf_t*, size_t);
void            kz_output_uint(kz_buf_t*, const unsigned*, size_t);

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
void        kz_output_bytes(kz_buf_t*, const void*, size_t);

#ifdef __cplusplus
}
#endif

#endif /* !defined(KZ_DRIVER_H) */
