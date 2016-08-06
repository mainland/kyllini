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

#include <KzcConfig.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if HAVE_DISPATCH_DISPATCH_H
#include <dispatch/dispatch.h>
#endif

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

#if HAVE_DISPATCH_DISPATCH_H
    tinfo->sem = dispatch_semaphore_create(0);
    if (tinfo->sem == NULL)
        return -1;
#else /* !HAVE_DISPATCH_DISPATCH_H */
    if ((err = sem_init(&(tinfo->sem), 0, 0)) != 0)
        return err;
#endif /* !HAVE_DISPATCH_DISPATCH_H */

    if ((err = pthread_attr_init(&attr)) != 0)
        return err;

    if ((err = pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED)) != 0)
        return err;

    return pthread_create(thread, NULL, start_routine, NULL);
}

int kz_thread_post(kz_tinfo_t *tinfo)
{
    /* We start out having "produced" a phantom element that the consumer marks
     * as consumed when it next requests input. This allows us to avoid copying
     * the item in the producer/consumer buffer because it is not marked as
     * consumed until the next request from the consumer
     */
    tinfo->prod_cnt = 0;
    tinfo->cons_cnt = -1;
    tinfo->cons_req = 0;
    tinfo->done = 0;
    kz_memory_barrier();
#if HAVE_DISPATCH_DISPATCH_H
    return dispatch_semaphore_signal(tinfo->sem);
#else /* !HAVE_DISPATCH_DISPATCH_H */
    return sem_post(&(tinfo->sem));
#endif /* !HAVE_DISPATCH_DISPATCH_H */
}

int kz_thread_wait(kz_tinfo_t *tinfo)
{
#if HAVE_DISPATCH_DISPATCH_H
    return dispatch_semaphore_wait(tinfo->sem, DISPATCH_TIME_FOREVER);
#else /* !HAVE_DISPATCH_DISPATCH_H */
    return sem_wait(&(tinfo->sem));
#endif /* !HAVE_DISPATCH_DISPATCH_H */
}

int kz_thread_join(kz_thread_t thread, void **retval)
{
    /* We detach threads, so we cannot join them */
    return 0;
}
