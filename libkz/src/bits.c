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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <kz/bits.h>

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

static inline
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
            memmove(dst, src, bytes_len);
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
            if (src_off + len > CHAR_BIT)
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
