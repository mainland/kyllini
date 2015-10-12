#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <kz/rt.h>

void kz_error(const char* s)
{
    fflush(stdout);
    fflush(stderr);
    fprintf(stderr, "%s\n", s);
    exit(EXIT_FAILURE);
}

void kz_bitarray_print(const bit_t* x, int32_t n)
{
    int i;

    for (i = 0; i < n; ++i) {
        int bit = x[i/BIT_ARRAY_ELEM_BITS] & (1 << (i % BIT_ARRAY_ELEM_BITS));

        if (bit)
            fprintf(stdout, "1");
        else
            fprintf(stdout, "0");
    }
}

inline
void copy_first_bits(uint8_t* dst, int dst_off, int* len, uint8_t c)
{
    if (*len >= (CHAR_BIT - dst_off)) {
        /* mask the first off bits */
        uint8_t mask = (1 << dst_off) - 1;

        *dst &= mask;
        *dst |= c & ~mask;

        *len -= CHAR_BIT - dst_off;
    } else {
        /* mask len bits starting off bits in */
        uint8_t mask = ((1 << *len) - 1) << dst_off;

        *dst &= ~mask;
        *dst |= c & mask;

        *len = 0;
    }
}

void kz_bitarray_copy(uint8_t* dst_orig, int dst_idx,
                      const uint8_t* src_orig, int src_idx,
                      int len)
{
    const uint8_t* src = src_orig + (src_idx / CHAR_BIT);
    uint8_t* dst = dst_orig + (dst_idx / CHAR_BIT);
    int src_off = src_idx % CHAR_BIT;
    int dst_off = dst_idx % CHAR_BIT;

    if (len == 0)
        return;

    if (dst_off == src_off) {
        int off = dst_off;

        /* Copy leading bits */
        if (off != 0) {
            copy_first_bits(dst, dst_off, &len, *src++);
            dst++;
        }

        /* Copy middle bits, one byte at a time */
        int bytes_len = len / CHAR_BIT;

        if (bytes_len != 0) {
            memcpy(dst, src, bytes_len);
            dst += bytes_len;
            src += bytes_len;
        }

        /* Copy trailing bits */
        int bits_len = len % CHAR_BIT;

        if (bits_len != 0) {
            /* mask the first bits_len bits */
            uint8_t mask = (1 << bits_len) - 1;

            *dst &= ~mask;
            *dst |= *src & mask;
        }
    } else {
        uint8_t c;
        int bit_diff_ls;
        int bit_diff_rs;

        /* Copy leading CHAR_BIT - dst_off bits to line up the
           destination */
        if (dst_off < src_off) {
            bit_diff_rs = src_off - dst_off;
            bit_diff_ls = CHAR_BIT - bit_diff_rs;

            c = *src++ >> bit_diff_rs;
            c |= *src << bit_diff_ls;
        } else {
            bit_diff_ls = dst_off - src_off;
            bit_diff_rs = CHAR_BIT - bit_diff_ls;
            c = *src << bit_diff_ls;
        }
        copy_first_bits(dst, dst_off, &len, c);
        dst++;

        /* Copy middle bits, one byte at a time */
        int bytes_len = len / CHAR_BIT;

        while (bytes_len-- > 0) {
            c = *src++ >> bit_diff_rs;
            c |= *src << bit_diff_ls;
            *dst++ = c;
        }

        /* Copy trailing bits */
        int bits_len = len % CHAR_BIT;

        if (bits_len != 0) {
            /* mask the first bits_len bits */
            uint8_t mask = (1 << bits_len) - 1;

            c = *src++ >> bit_diff_rs;
            if (bits_len > CHAR_BIT - bit_diff_rs)
                c |= *src << bit_diff_ls;

            *dst &= ~mask;
            *dst |= c & mask;
        }
    }
}
