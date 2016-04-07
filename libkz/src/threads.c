#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <kz/threads.h>

int kz_tinfo_init(kz_tinfo_t *tinfo)
{
    return 0;
}

int kz_thread_init(kz_tinfo_t *tinfo,
                   kz_thread_t *thread,
                   void *(*start_routine)(void *))
{
    pthread_attr_t attr;
    int err;

    tinfo->prod_cnt = 0;
    tinfo->cons_cnt = 0;
    tinfo->cons_req = 0;
    tinfo->done = 0;
    tinfo->result = NULL;

    if ((err = sem_init(&(tinfo->sem), 0, 0)) != 0)
        return err;

    if ((err = pthread_attr_init(&attr)) != 0)
        return err;

    if ((err = pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED)) != 0)
        return err;

    return pthread_create(thread, NULL, start_routine, tinfo);
}

int kz_thread_post(kz_tinfo_t *tinfo)
{
    tinfo->done = 0;
    kz_memory_barrier();
    return sem_post(&(tinfo->sem));
}

int kz_thread_wait(kz_tinfo_t *tinfo)
{
    return sem_wait(&(tinfo->sem));
}

int kz_thread_join(kz_thread_t thread, void **retval)
{
    return pthread_join(thread, retval);
}
