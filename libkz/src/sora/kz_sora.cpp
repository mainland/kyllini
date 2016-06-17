/*
   Portions Copyright (c) Microsoft Corporation
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
#include <emmintrin.h>
#include <xmmintrin.h>

#include <kz/ext.h>
#include <sora/fft.h>
#include <sora/intalglutx.h>
#include <sora/viterbicore.h>
#include <sora/ieee80211const.h>

//
// We support Fixed Point Radians in this file.
// FP_RAD maps PI (and -PI) to 0x8000 and it represents only radians [-PI, PI)
//
typedef short FP_RAD;  // fixed point radians

// FP_FRAC fixed point fraction - [-1,1)
//
typedef short FP_FRAC; // fixed point fraction

FORCEINLINE
void __kz_permutatew1313(const complex16_t x[4], complex16_t *y)
{
    __m128i mx = _mm_loadu_si128((__m128i*) x);
    _mm_storeu_si128((__m128i*) y, _mm_shuffle_epi32(mx, _MM_SHUFFLE(3, 1, 3, 1)));
}

FORCEINLINE
void __kz_interleave_loww(const complex16_t x[4], const complex16_t y[4], complex16_t* z)
{
    __m128i mx = _mm_loadu_si128((__m128i*) x);
    __m128i my = _mm_loadu_si128((__m128i*) y);
    _mm_storeu_si128((__m128i*) z, _mm_unpacklo_epi64(mx, my));
}

FORCEINLINE
int16_t __kz_sin_int16(int16_t r)
{
    return sinx_lut[(unsigned short)r];
}

FORCEINLINE
int16_t __kz_cos_int16(int16_t r)
{
    return cosx_lut[(unsigned short)r];
}

// bit_scope - find the highest bit position of an integer
FORCEINLINE
unsigned char bit_scope_ub(unsigned char x)
{
    return bit_high_pos_lutx[x];
}

FORCEINLINE
unsigned char bit_scope_us(unsigned short x)
{
    unsigned char tt;
    if ((tt = (x >> 8)))
        return bit_scope_ub (tt) + 8;
    else
        return bit_scope_ub ((unsigned char)(x));
}

FORCEINLINE
unsigned char bit_scope_ui(unsigned int x)
{
    unsigned short tt;

    if ((tt = (x >> 16)))
        return bit_scope_us (tt) + 16;
    else
        return bit_scope_us ((unsigned short)(x));
}

FORCEINLINE
unsigned char bit_scope_s(int x)
{
    if (x>0)
        // positive value
        return bit_scope_ui ((unsigned int)x);
    else
        // negative value
        return bit_scope_ui ((unsigned int)(-x));
}

FORCEINLINE
int16_t __kz_atan2_int16(int16_t y, int16_t x)
{
    int ys = bit_scope_s(y);
    int xs = bit_scope_s(x);

    int shift = ((xs>ys)?xs:ys) - 6;

    if ( shift > 0 )
        return atan2x_lut[(unsigned char)(y>>shift)][(unsigned char)(x>>shift)];
    else
        return atan2x_lut[(unsigned char)(y)][(unsigned char)(x)];
}

FORCEINLINE
int32_t __kz_atan2_int32(int32_t y, int32_t x)
{
    return __kz_atan2_int16(y, x);
}

FORCEINLINE
void __kz_sora_ifft(int n, const complex16_t *in, complex16_t *out)
{
    // We use the safe version to respect Blink's semantic
    //      IFFT<128> (temp, pcOutput );
    switch (n) {
    case 16:
        IFFTSafe<16>(in, out);
        break;
    case 32:
        IFFTSafe<32>(in, out);
        break;
    case 64:
        IFFTSafe<64>(in, out);
        break;
    case 128:
        IFFTSafe<128>(in, out);
        break;
    case 256:
        IFFTSafe<256>(in, out);
        break;
    case 512:
        IFFTSafe<512>(in, out);
        break;
    case 1024:
        IFFTSafe<1024>(in, out);
        break;
    case 2048:
        IFFTSafe<2048>(in, out);
        break;
        // LTE compatibility
    case 12:
        IFFTSafe<12>(in, out);
        break;
    case 24:
        IFFTSafe<24>(in, out);
        break;
    case 36:
        IFFTSafe<36>(in, out);
        break;
    case 48:
        IFFTSafe<48>(in, out);
        break;
    case 60:
        IFFTSafe<60>(in, out);
        break;
    case 72:
        IFFTSafe<72>(in, out);
        break;
    case 96:
        IFFTSafe<96>(in, out);
        break;
    case 108:
        IFFTSafe<108>(in, out);
        break;
    case 120:
        IFFTSafe<120>(in, out);
        break;
    case 144:
        IFFTSafe<144>(in, out);
        break;
    case 180:
        IFFTSafe<180>(in, out);
        break;
    case 192:
        IFFTSafe<192>(in, out);
        break;
    case 216:
        IFFTSafe<216>(in, out);
        break;
    case 240:
        IFFTSafe<240>(in, out);
        break;
    case 288:
        IFFTSafe<288>(in, out);
        break;
    case 300:
        IFFTSafe<300>(in, out);
        break;
    case 324:
        IFFTSafe<324>(in, out);
        break;
    case 360:
        IFFTSafe<360>(in, out);
        break;
    case 384:
        IFFTSafe<384>(in, out);
        break;
    case 432:
        IFFTSafe<432>(in, out);
        break;
    case 480:
        IFFTSafe<480>(in, out);
        break;
    case 540:
        IFFTSafe<540>(in, out);
        break;
    case 576:
        IFFTSafe<576>(in, out);
        break;
    case 600:
        IFFTSafe<600>(in, out);
        break;
    case 648:
        IFFTSafe<648>(in, out);
        break;
    case 720:
        IFFTSafe<720>(in, out);
        break;
    case 768:
        IFFTSafe<768>(in, out);
        break;
    case 864:
        IFFTSafe<864>(in, out);
        break;
    case 900:
        IFFTSafe<900>(in, out);
        break;
    case 960:
        IFFTSafe<960>(in, out);
        break;
    case 972:
        IFFTSafe<972>(in, out);
        break;
    case 1080:
        IFFTSafe<1080>(in, out);
        break;
    case 1152:
        IFFTSafe<1152>(in, out);
        break;
    case 1200:
        IFFTSafe<1200>(in, out);
        break;
    default:
        fprintf(stderr, "__kz_sora_ifft error: ifft size %d not supported!\n", n);
        break;
    }
}

FORCEINLINE
void __kz_sora_fft(int n, const complex16_t *in, complex16_t *out)
{
    //// We use the safe version to respect Blink's semantic
    switch (n) {
    case 16:
        FFTSafe<16>(in, out);
        break;
    case 32:
        FFTSafe<32>(in, out);
        break;
    case 64:
        FFTSafe<64>(in, out);
        break;
    case 128:
        FFTSafe<128>(in, out);
        break;
    case 256:
        FFTSafe<256>(in, out);
        break;
    case 512:
        FFTSafe<512>(in, out);
        break;
    case 1024:
        FFTSafe<1024>(in, out);
        break;
    case 2048:
        FFTSafe<2048>(in, out);
        break;
        // LTE compatibility
    case 12:
        FFTSafe<12>(in, out);
        break;
    case 24:
        FFTSafe<24>(in, out);
        break;
    case 36:
        FFTSafe<36>(in, out);
        break;
    case 48:
        FFTSafe<48>(in, out);
        break;
    case 60:
        FFTSafe<60>(in, out);
        break;
    case 72:
        FFTSafe<72>(in, out);
        break;
    case 96:
        FFTSafe<96>(in, out);
        break;
    case 108:
        FFTSafe<108>(in, out);
        break;
    case 120:
        FFTSafe<120>(in, out);
        break;
    case 144:
        FFTSafe<144>(in, out);
        break;
    case 180:
        FFTSafe<180>(in, out);
        break;
    case 192:
        FFTSafe<192>(in, out);
        break;
    case 216:
        FFTSafe<216>(in, out);
        break;
    case 240:
        FFTSafe<240>(in, out);
        break;
    case 288:
        FFTSafe<288>(in, out);
        break;
    case 300:
        FFTSafe<300>(in, out);
        break;
    case 324:
        FFTSafe<324>(in, out);
        break;
    case 360:
        FFTSafe<360>(in, out);
        break;
    case 384:
        FFTSafe<384>(in, out);
        break;
    case 432:
        FFTSafe<432>(in, out);
        break;
    case 480:
        FFTSafe<480>(in, out);
        break;
    case 540:
        FFTSafe<540>(in, out);
        break;
    case 576:
        FFTSafe<576>(in, out);
        break;
    case 600:
        FFTSafe<600>(in, out);
        break;
    case 648:
        FFTSafe<648>(in, out);
        break;
    case 720:
        FFTSafe<720>(in, out);
        break;
    case 768:
        FFTSafe<768>(in, out);
        break;
    case 864:
        FFTSafe<864>(in, out);
        break;
    case 900:
        FFTSafe<900>(in, out);
        break;
    case 960:
        FFTSafe<960>(in, out);
        break;
    case 972:
        FFTSafe<972>(in, out);
        break;
    case 1080:
        FFTSafe<1080>(in, out);
        break;
    case 1152:
        FFTSafe<1152>(in, out);
        break;
    case 1200:
        FFTSafe<1200>(in, out);
        break;
    default:
        fprintf(stderr, "__kz_sora_fft error: fft size %d not supported!\n", n);
        break;
    }
}

// Viterbi brick template parameters:
const size_t TRELLIS_MAX = 5000 * 8;
TViterbiCore<TRELLIS_MAX> m_viterbi;

unsigned long ob_count;
uint16_t frame_length = 1500;
int16_t code_rate = CR_12;
size_t TRELLIS_DEPTH = 256;
unsigned char *m_outbuf = NULL;

void __kz_viterbi_brick_init_fast(int32_t frame_len, int16_t code_r, int16_t depth)
{
    ob_count = 0;
    m_viterbi.Reset();
    frame_length = frame_len;
    code_rate = code_r;
    if (m_outbuf != NULL) free((void *)m_outbuf);
    TRELLIS_DEPTH = (size_t) depth;
    m_outbuf = (unsigned char*) malloc((size_t) (TRELLIS_DEPTH + 1));
    if (m_outbuf == NULL) {
        fprintf(stderr, "Viterbi memory allocation failure!\n");
        exit(1);
    }
}

int16_t __kz_viterbi_brick_decode_fast(int n, const int8_t svalue[48], uint8_t *bitValue)
{
    static const int trellis_prefix = 6;     // 6 bit zero prefix
    static const int trellis_lookahead = 24;

    //uchar  m_outbuf[TRELLIS_DEPTH / 8 + 1];


    unsigned int total_byte_count = 0;

    // vector128 constants
    static const __m128i * const pVITMA = (const __m128i*)VIT_MA; // Branch Metric A
    static const __m128i * const pVITMB = (const __m128i*)VIT_MB; // Branch Metric B


    //uchar* input = ipin.peek();
    unsigned char* input = (unsigned char*)svalue;
    //uchar* input_end = input + NUM_INPUT;
    unsigned char* input_end = input + 48;
    while (input < input_end) {
        // advance branch
        if (code_rate == CR_12) {
                m_viterbi.BranchACS(pVITMA, input[0], pVITMB, input[1]);
                input += 2; // jump to data
        }  else if (code_rate == CR_34) {
                m_viterbi.BranchACS(pVITMA, input[0], pVITMB, input[1]);
                m_viterbi.BranchACS(pVITMA, input[2]);
                m_viterbi.BranchACS(pVITMB, input[3]);
                input += 4;
        } else if (code_rate == CR_23) {
            m_viterbi.BranchACS(pVITMA, input[0], pVITMB, input[1]);
                m_viterbi.BranchACS(pVITMA, input[2]);
                input += 3;
        }

        unsigned int tr_index = m_viterbi.trellis_index();

        if ((tr_index & 7) == 0) {
            m_viterbi.Normalize();
        }

        // check trace_back
        unsigned int output_count = 0;
        unsigned int lookahead = 0;
        const unsigned int tr_index_end = frame_length * 8 + trellis_prefix;
        if (tr_index >= tr_index_end) {
            // all bytes have been processed - track back all of them
            output_count = tr_index_end - ob_count
                - trellis_prefix;
            lookahead = tr_index - tr_index_end;
        } else if (tr_index >= ob_count + TRELLIS_DEPTH + trellis_lookahead + trellis_prefix) {
            // trace back partially

            // Note: tr_index increase during 'BranchACS', to decode out complete bytes, we may lookahead the
            // trellis without output a few more than 'trellis_lookahead'
            unsigned int remain = (tr_index - (ob_count + TRELLIS_DEPTH + trellis_lookahead + trellis_prefix)) % 8;
            output_count = TRELLIS_DEPTH;
            lookahead = trellis_lookahead + remain;
        }

        if (output_count) {
            m_viterbi.Traceback((char*)m_outbuf, output_count, lookahead);
            ob_count += output_count;

            unsigned int last_byte_count = 0;
            while (last_byte_count < output_count / 8) {
                bitValue[total_byte_count] = m_outbuf[last_byte_count];
                last_byte_count++;
                total_byte_count++;
            }
        }
    }
    return total_byte_count * 8;
}

FORCEINLINE
int16_t __kz_viterbiSig11a_brick_decode_fast(int n, const int8_t svalue[48], uint8_t *bitValue)
{
    static const int state_size = 64;
    static const int input_size = 48; // always 48 soft-values

    __m128i trellis[state_size / 16 * input_size];

    Viterbi_sig11(trellis, (char *)svalue, (char *)(bitValue));
    *((unsigned int *)bitValue) >>= 6; // remove the prefix 6 zeros

    return 0;
}
