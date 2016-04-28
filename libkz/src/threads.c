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
    /* We detach threads, so we cannot join them */
    return 0;
}
