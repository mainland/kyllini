#if !defined(KZ_BITS_H)
#define KZ_BITS_H

#include <kz/types.h>

#ifdef __cplusplus
extern "C" {
#endif

void kz_bitarray_print(const bit_t* x, int32_t n);
void kz_bitarray_copy(uint8_t* dst, int dst_idx,
                      const uint8_t* src, int src_idx,
                      int len);

#ifdef __cplusplus
}
#endif

#endif /* !defined(KZ_BITS_H) */
