#if !defined(KZ_THREADS_H)
#define KZ_THREADS_H

#ifdef __cplusplus
extern "C" {
#endif

#include <kz/types.h>

#include <pthread.h>
#include <semaphore.h>

#if defined(_MSC_VER)
#include <intrin.h>
#endif /* !defined(_MSC_VER) */

#if defined(__INTEL_COMPILER)
#include <x86intrin.h>
#endif /* !defined(__INTEL_COMPILER) */

#if defined(_MSC_VER)
#define kz_memory_barrier() _ReadWriteBarrier()
#elif defined(__INTEL_COMPILER)
#define kz_memory_barrier() __memory_barrier()
#elif defined(__GNUC__)
#define kz_memory_barrier() asm volatile("" ::: "memory")
#elif defined(__clang__)
#define kz_memory_barrier() asm volatile("" ::: "memory")
#else
#error "memory barrier undefined"
#endif

#define KZ_BUFFER_SIZE 8

/* Thread info */
typedef struct {
    sem_t sem;
    volatile unsigned int prod_cnt; /* count of items produced */
    volatile unsigned int cons_cnt; /* count of items consumed */
    volatile unsigned int cons_req; /* number of items consumer has requested */
    volatile int done;              /* set to 1 when either computation is done */
    void* result;                   /* Pointer to storage for the result of the
                                       computation */
} kz_tinfo_t;

typedef pthread_t kz_thread_t;

int kz_thread_init(kz_tinfo_t *tinfo,
                   kz_thread_t *thread,
                   void *(*start_routine)(void *));
int kz_thread_post(kz_tinfo_t *tinfo);
int kz_thread_wait(kz_tinfo_t *tinfo);
int kz_thread_join(kz_thread_t thread, void **retval);

#ifdef __cplusplus
}
#endif

#endif /* !defined(KZ_THREADS_H) */
