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

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <string.h>

#include <type_traits>

#include <kz/bits.h>
#include <kz/driver.h>

#define DEFAULT_BUFSIZE 4096

template<typename T> void init_input(const kz_params_t* params, kz_buf_t* buf);
template<typename T> void init_output(const kz_params_t* params, kz_buf_t* buf);
template<typename T> void cleanup_input(const kz_params_t* params, kz_buf_t* buf);
template<typename T> void cleanup_output(const kz_params_t* params, kz_buf_t* buf);
template<typename T> const T* input(kz_buf_t* buf, size_t n);
template<typename T>  void output(kz_buf_t* buf, const T* data, size_t n);

static bit_t parse_bit(const char* s, bool* success);
static int   print_bit(FILE* fp, bit_t x, bool comma);

static bit_t read_bit(kz_buf_t *buf, int i);
static void  write_bit(kz_buf_t *buf, int i, bit_t bit);

static void *read_file(const char* file, const char* mode, size_t* len);
static void free_buf(kz_buf_t* buf);

template<typename T>
typename std::enable_if<std::is_signed<T>::value && std::is_integral<T>::value,int>::type
parse(const char* s, bool* success)
{
    char* endptr;
    int x;

    x = strtol(s, &endptr, 10);
    if (endptr == s && x == 0)
        *success = false;
    else if (errno == EINVAL)
        *success = false;
    else
        *success = true;

    return x;
}

template<typename T>
typename std::enable_if<std::is_unsigned<T>::value && std::is_integral<T>::value,int>::type
parse(const char* s, bool* success)
{
    char* endptr;
    int x;

    x = strtoul(s, &endptr, 10);
    if (endptr == s && x == 0)
        *success = false;
    else if (errno == EINVAL)
        *success = false;
    else
        *success = true;

    return x;
}

template<typename T>
typename std::enable_if<std::is_floating_point<T>::value,int>::type
parse(const char* s, bool* success)
{
    char* endptr;
    int x;

    x = strtod(s, &endptr);
    if (endptr == s && x == 0)
        *success = false;
    else if (errno == EINVAL)
        *success = false;
    else
        *success = true;

    return x;
}

bit_t parse_bit(const char* s, bool* success)
{
    char* endptr;
    long x;

    x = strtoul(s, &endptr, 10);
    if (endptr == s && x == 0)
        *success = false;
    else if (errno == EINVAL)
        *success = false;
    else
        *success = true;

    if (x <= 1)
        return x;
    else {
        fprintf(stderr, "Illegal bit value: %s\n", s);
        exit(EXIT_FAILURE);
    }
}

template<typename T>
typename std::enable_if<std::is_integral<T>::value,void>::type
print(FILE* fp, T x, bool comma)
{
    if (comma)
        fprintf(fp, "%ld,", (long) x);
    else
        fprintf(fp, "%ld", (long) x);
}

template<typename T>
typename std::enable_if<std::is_floating_point<T>::value,void>::type
print(FILE* fp, T x, bool comma)
{
    if (comma)
        fprintf(fp, "%g,", (double) x);
    else
        fprintf(fp, "%g", (double) x);
}

static int print_bit(FILE* fp, bit_t x, bool comma)
{
    if (comma)
        return fprintf(fp, "%d,", (int) (x > 0 ? 1 : 0));
    else
        return fprintf(fp, "%d", (int) (x > 0 ? 1 : 0));
}

template<typename T> void init_input(const kz_params_t* params, kz_buf_t* buf)
{
    if (params->src_dev == DEV_FILE) {

        buf->dev = DEV_FILE;
        buf->buf = NULL;
        buf->len = 0;
        buf->idx = 0;

        if (params->src == NULL)
            return;

        if (params->src_mode == MODE_BINARY) {
            buf->buf = read_file(params->src, "rb", &(buf->len));
            buf->idx = 0;
            buf->len /= sizeof(T);
        } else if (params->src_mode == MODE_TEXT) {
            size_t  size = DEFAULT_BUFSIZE;
            char    *text;
            size_t  text_len;
            char    *s;
            T       x;
            bool    success;

            text = (char*) read_file(params->src, "r", &text_len);
            assert(text != NULL);

            buf->buf = malloc(size*sizeof(T));
            assert(buf->buf != NULL);

            s = strtok(text, ",");
            if (s == NULL) {
                fprintf(stderr,"Input file contains no samples.");
                exit(EXIT_FAILURE);
            }

            do {
                x = parse<T>(s, &success);
                if(success)
                    ((T*) buf->buf)[buf->len++] = x;
                else
                    s = strtok(NULL, ",");
            } while(!success);

            while ((s = strtok(NULL, ",")))  {
                x = parse<T>(s, &success);
                if (success) {
                    if (buf->len == size) {
                        size *= 2;
                        buf->buf = realloc(buf->buf, size*sizeof(T));
                        assert(buf->buf != NULL);
                    }

                    ((T*) buf->buf)[buf->len++] = x;
                }
            }

            free(text);
        }
    } else {
        buf->dev = params->src_dev;
        buf->buf = malloc(DEFAULT_BUFSIZE*sizeof(T));
        buf->idx = 0;
        buf->len = 0;
        buf->dummy_samples = params->dummy_samples;
    }
}

template<typename T> void init_output(const kz_params_t* params, kz_buf_t* buf)
{
    buf->dev = params->dst_dev;
    buf->len = DEFAULT_BUFSIZE;
    buf->idx = 0;
    buf->buf = malloc(DEFAULT_BUFSIZE*sizeof(T));
    assert(buf->buf != NULL);
}

template<typename T> void cleanup_input(const kz_params_t* params, kz_buf_t* buf)
{
    free_buf(buf);
}

template<typename T> void cleanup_output(const kz_params_t* params, kz_buf_t* buf)
{
    if (params->dst_dev == DEV_FILE) {
        if (params->dst_mode == MODE_BINARY) {
            FILE *fp;

            fp = fopen(params->dst, "wb");
            if (fp == NULL) {
                fprintf(stderr, "Cannot open file %s\n", params->dst);
                exit(EXIT_FAILURE);
            }
            assert(fwrite(buf->buf, 1, sizeof(T)*buf->idx, fp) == sizeof(T)*buf->idx);
            assert(fclose(fp) == 0);
        } else if (params->dst_mode == MODE_TEXT) {
            FILE *fp;
            int i;

            fp = fopen(params->dst, "w");
            if (fp == NULL) {
                fprintf(stderr, "Cannot open file %s\n", params->dst);
                exit(EXIT_FAILURE);
            }

            for (i = 0; i < buf->idx; ++i)
                print(fp, ((T*) buf->buf)[i], i < buf->idx - 1);
        }
    }

    free_buf(buf);
}

template<typename T> const T* input(kz_buf_t* buf, size_t n)
{
    if (buf->dev == DEV_DUMMY) {
        buf->dummy_samples -= n;
        if (buf->dummy_samples >= 0)
            return (T*) buf->buf;
        else
            return NULL;
    } else {
        if (buf->idx + n <= buf->len) {
            T* p = &((T*) buf->buf)[buf->idx];

            buf->idx += n;
            return p;
        } else
            return NULL;
    }
}

template<typename T> void output(kz_buf_t* buf, const T* data, size_t n)
{
    if (buf->dev == DEV_DUMMY)
        return;
    else {
        if (buf->idx + n > buf->len) {
            do {
                buf->len *= 2;
            } while (buf->idx + n > buf->len);

            buf->buf = realloc(buf->buf, buf->len*sizeof(T));
            assert(buf->buf != NULL);
        }

        memcpy(&((T*) buf->buf)[buf->idx], data, n*sizeof(T));
        buf->idx += n;
    }
}

bit_t read_bit(kz_buf_t *buf, int i)
{
    return ((bit_t*) buf->buf)[i / BIT_ARRAY_ELEM_BITS] & (1 << (i & (BIT_ARRAY_ELEM_BITS - 1)));
}

void write_bit(kz_buf_t *buf, int i, bit_t bit)
{
    bit_t mask = 1 << (i & (BIT_ARRAY_ELEM_BITS - 1));

    if (bit)
        ((bit_t*) buf->buf)[i / BIT_ARRAY_ELEM_BITS] |= mask;
    else
        ((bit_t*) buf->buf)[i / BIT_ARRAY_ELEM_BITS] &= ~mask;
}

void* read_file(const char* file, const char* mode, size_t* len)
{
    FILE   *fp;
    char   *buf;
    size_t size;

    fp = fopen(file, mode);
    if (fp == NULL) {
        fprintf(stderr, "Cannot open file %s\n", file);
        exit(EXIT_FAILURE);
    }

    assert(fseek(fp, 0, SEEK_END) == 0);
    size = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    buf = (char*) malloc(size + 1);
    assert(buf != NULL);
    assert(fread(buf, 1, size, fp) == size);
    assert(fclose(fp) == 0);
    buf[size] = 0;
    *len = size;
    return buf;
}

void free_buf(kz_buf_t* buf)
{
    free(buf->buf);
    buf->buf = NULL;
}

#define DECLARE_IO(D,T) \
void kz_init_input_##D(const kz_params_t* params, kz_buf_t* buf) \
{ \
    init_input<T>(params, buf); \
} \
\
void kz_init_output_##D(const kz_params_t* params, kz_buf_t* buf) \
{ \
    init_output<T>(params, buf); \
} \
\
void kz_cleanup_input_##D(const kz_params_t* params, kz_buf_t* buf) \
{ \
    cleanup_input<T>(params, buf); \
} \
\
void kz_cleanup_output_##D(const kz_params_t* params, kz_buf_t* buf) \
{ \
    cleanup_output<T>(params, buf); \
} \
\
const T* kz_input_##D(kz_buf_t* buf, size_t n) \
{ \
    return input<T>(buf, n); \
} \
\
void kz_output_##D(kz_buf_t* buf, const T* data, size_t n) \
{ \
    output(buf, data, n); \
}

DECLARE_IO(int8,int8_t)
DECLARE_IO(int16,int16_t)
DECLARE_IO(int32,int32_t)

DECLARE_IO(uint8,uint8_t)
DECLARE_IO(uint16,uint16_t)
DECLARE_IO(uint32,uint32_t)

DECLARE_IO(float,float)
DECLARE_IO(double,double)

/*
 * bit input/output
 */
void kz_init_input_bit(const kz_params_t* params, kz_buf_t* buf)
{
    if (params->src_dev == DEV_FILE) {
        buf->dev = DEV_FILE;
        buf->buf = NULL;
        buf->len = 0;
        buf->idx = 0;

        if (params->src == NULL)
            return;

        if (params->src_mode == MODE_BINARY) {
            buf->buf = read_file(params->src, "rb", &(buf->len));
            buf->idx = 0;
            buf->len *= CHAR_BIT;
        } else if (params->src_mode == MODE_TEXT) {
            size_t  size = DEFAULT_BUFSIZE;
            char    *text;
            size_t  text_len;
            char    *s;
            bit_t   x;
            bool    success;

            text = (char*) read_file(params->src, "r", &text_len);
            assert(text != NULL);

            buf->buf = malloc((size + BIT_ARRAY_ELEM_BITS - 1)/BIT_ARRAY_ELEM_BITS);
            assert(buf->buf != NULL);

            s = strtok(text, ",");
            if (s == NULL) {
                fprintf(stderr,"Input file contains no samples.");
                exit(EXIT_FAILURE);
            }

            do {
                x = parse_bit(s, &success);
                if(success)
                    write_bit(buf, buf->len++, x);
                else
                    s = strtok(NULL, ",");
            } while(!success);

            while ((s = strtok(NULL, ",")))  {
                x = parse_bit(s, &success);
                if (success) {
                    if (buf->len == size) {
                        size *= 2;
                        buf->buf = realloc(buf->buf, (size + BIT_ARRAY_ELEM_BITS - 1)/BIT_ARRAY_ELEM_BITS);
                        assert(buf->buf != NULL);
                    }

                    write_bit(buf, buf->len++, x);
                }
            }

            free(text);
        }
    } else {
        buf->dev = params->src_dev;
        buf->buf = NULL;
        buf->idx = 0;
        buf->len = 0;
        buf->dummy_samples = params->dummy_samples;
    }
}

void kz_init_output_bit(const kz_params_t* params, kz_buf_t* buf)
{
    init_output<bit_t>(params, buf);
    buf->len *= BIT_ARRAY_ELEM_BITS;
}

void kz_cleanup_input_bit(const kz_params_t* params, kz_buf_t* buf)
{
    free_buf(buf);
}

void kz_cleanup_output_bit(const kz_params_t* params, kz_buf_t* buf)
{
    if (params->dst_dev == DEV_FILE) {
        if (params->dst_mode == MODE_BINARY) {
            FILE *fp;
            size_t size = (buf->idx + BIT_ARRAY_ELEM_BITS - 1)/BIT_ARRAY_ELEM_BITS;

            fp = fopen(params->dst, "wb");
            if (fp == NULL) {
                fprintf(stderr, "Cannot open file %s\n", params->dst);
                exit(EXIT_FAILURE);
            }
            assert(fwrite(buf->buf, 1, size, fp) == size);
            assert(fclose(fp) == 0);
        } else if (params->dst_mode == MODE_TEXT) {
            FILE *fp;
            unsigned i;

            fp = fopen(params->dst, "w");
            if (fp == NULL) {
                fprintf(stderr, "Cannot open file %s\n", params->dst);
                exit(EXIT_FAILURE);
            }

            for (i = 0; i < buf->idx; ++i)
                print_bit(fp, read_bit(buf, i), i < buf->idx - 1);
        }
    }

    free_buf(buf);
}

inline size_t bit_array_len(size_t n)
{
    return (n + (sizeof(bit_t) - 1))/sizeof(bit_t);
}

#define BITBUF_SIZE 64

static bit_t dummy_bitbuf;
static bit_t bitbuf[BITBUF_SIZE];

const bit_t* kz_input_bit(kz_buf_t* buf, size_t n)
{
    if (buf->dev == DEV_DUMMY) {
        buf->dummy_samples -= n;
        if (buf->dummy_samples >= 0)
            return &dummy_bitbuf;
        else
            return NULL;
    } else {
        if (buf->idx + n > buf->len)
            return NULL;

        if (buf->idx % BIT_ARRAY_ELEM_BITS == 0) {
            bit_t* p = &((bit_t*) buf->buf)[buf->idx / BIT_ARRAY_ELEM_BITS];

            buf->idx += n;
            return p;
        } else {
            /* Copy bits to a temporary buffer so we can return a pointer to the
             * bits.
             */
            assert(n <= BITBUF_SIZE*BIT_ARRAY_ELEM_BITS);

            kz_bitarray_copy(bitbuf, 0, (bit_t*) buf->buf, buf->idx, n);
            buf->idx += n;

            return bitbuf;
        }
    }
}

void kz_output_bit(kz_buf_t* buf, const bit_t* data, size_t n)
{
    if (buf->dev == DEV_DUMMY)
        return;
    else {
        if (buf->idx + n > buf->len) {
            do {
                buf->len *= 2;
            } while (buf->idx + n > buf->len);

            buf->buf = realloc(buf->buf, (buf->len + BIT_ARRAY_ELEM_BITS - 1)/BIT_ARRAY_ELEM_BITS);
            assert(buf->buf != NULL);
        }

        kz_bitarray_copy((bit_t*) buf->buf, buf->idx, data, 0, n);
        buf->idx += n;
    }
}

/*
 * complext16_t input/output
 */

void kz_init_input_complex16(const kz_params_t* params, kz_buf_t* buf)
{
    assert(sizeof(complex16_t) == 2*sizeof(int16_t));
    init_input<int16_t>(params, buf);
    buf->idx /= 2;
    buf->len /= 2;
}

void kz_init_output_complex16(const kz_params_t* params, kz_buf_t* buf)
{
    assert(sizeof(complex16_t) == 2*sizeof(int16_t));
    init_output<int16_t>(params, buf);
    buf->idx /= 2;
    buf->len /= 2;
}

void kz_cleanup_input_complex16(const kz_params_t* params, kz_buf_t* buf)
{
    assert(sizeof(complex16_t) == 2*sizeof(int16_t));
    buf->idx *= 2;
    buf->len *= 2;
    cleanup_input<int16_t>(params, buf);
}

void kz_cleanup_output_complex16(const kz_params_t* params, kz_buf_t* buf)
{
    assert(sizeof(complex16_t) == 2*sizeof(int16_t));
    buf->idx *= 2;
    buf->len *= 2;
    cleanup_output<int16_t>(params, buf);
}

const complex16_t* kz_input_complex16(kz_buf_t* buf, size_t n)
{
    return input<complex16_t>(buf, n);
}

void kz_output_complex16(kz_buf_t* buf, const complex16_t* data, size_t n)
{
    output<complex16_t>(buf, data, n);
}

/*
 * complext32_t input/output
 */

void kz_init_input_complex32(const kz_params_t* params, kz_buf_t* buf)
{
    assert(sizeof(complex32_t) == 2*sizeof(int32_t));
    init_input<int32_t>(params, buf);
    buf->idx /= 2;
    buf->len /= 2;
}

void kz_init_output_complex32(const kz_params_t* params, kz_buf_t* buf)
{
    assert(sizeof(complex32_t) == 2*sizeof(int32_t));
    init_output<int32_t>(params, buf);
    buf->idx /= 2;
    buf->len /= 2;
}

void kz_cleanup_input_complex32(const kz_params_t* params, kz_buf_t* buf)
{
    assert(sizeof(complex32_t) == 2*sizeof(int32_t));
    buf->idx *= 2;
    buf->len *= 2;
    cleanup_input<int32_t>(params, buf);
}

void kz_cleanup_output_complex32(const kz_params_t* params, kz_buf_t* buf)
{
    assert(sizeof(complex32_t) == 2*sizeof(int32_t));
    buf->idx *= 2;
    buf->len *= 2;
    cleanup_output<int32_t>(params, buf);
}

const complex32_t* kz_input_complex32(kz_buf_t* buf, size_t n)
{
    return input<complex32_t>(buf, n);
}

void kz_output_complex32(kz_buf_t* buf, const complex32_t* data, size_t n)
{
    output<complex32_t>(buf, data, n);
}

/*
 * bytes input/output
 */

void kz_init_input_bytes(const kz_params_t* params, kz_buf_t* buf)
{
    init_input<uint8_t>(params, buf);
}

void kz_init_output_bytes(const kz_params_t* params, kz_buf_t* buf)
{
    init_output<uint8_t>(params, buf);
}

void kz_cleanup_input_bytes(const kz_params_t* params, kz_buf_t* buf)
{
    cleanup_input<uint8_t>(params, buf);
}

void kz_cleanup_output_bytes(const kz_params_t* params, kz_buf_t* buf)
{
    cleanup_output<uint8_t>(params, buf);
}

const void*
kz_input_bytes(kz_buf_t* buf, size_t n)
{
    return input<uint8_t>(buf, n);
}

void
kz_output_bytes(kz_buf_t* buf, void* data, size_t n)
{
    output<uint8_t>(buf, (uint8_t*) data, n);
}
