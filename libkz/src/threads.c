#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <kz/threads.h>

void kz_tinfo_init(kz_tinfo_t *tinfo)
{
    tinfo->prod_cnt = 0;
    tinfo->cons_cnt = 0;
    tinfo->cons_req = 0;
    tinfo->done = 0;
    tinfo->result = NULL;
}

int kz_thread_create(kz_thread_t *thread,
                     void *(*start_routine)(void *),
                     void *arg)
{
    return pthread_create(thread, NULL, start_routine, arg);
}

int kz_thread_join(kz_thread_t thread, void **retval)
{
    return pthread_join(thread, retval);
}
