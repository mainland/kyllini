#if !defined(KZ_RT_H)
#define KZ_RT_H

#include <kz/types.h>

#ifdef __cplusplus
extern "C" {
#endif

void kz_error(const char*);
void kz_bitarray_copy(uint8_t* dst, int dst_idx,
                      const uint8_t* src, int src_idx,
                      int len);

#ifdef __cplusplus
}
#endif

#endif /* !defined(KZ_RT_H) */
