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
#include <xmmintrin.h>

#include <kz/ext.h>
#include <sora/fft.h>

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

void __kz_viterbi_brick_init_fast(int32_t frame_length, int16_t code_rate, int16_t depth)
{
}

int16_t __kz_viterbiSig11a_brick_decode_fast(int n, const int8_t svalue[48], const uint8_t *bitValue)
{
    return 0;
}

int16_t __kz_viterbi_brick_decode_fast(int n, const int8_t svalue[48], const uint8_t *bitValue)
{
    return 0;
}
