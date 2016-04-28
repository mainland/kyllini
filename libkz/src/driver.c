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

#include <errno.h>
#include <getopt.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <sys/resource.h>
#include <sys/times.h>

#include <kz.h>

int parseOpts(kz_params_t*, int, char *[]);
void parseOptsCleanup(kz_params_t* params);
kz_mode_t parseMode(int argc, char *argv[], const char*);
kz_dev_t parseDev(int argc, char *argv[], const char* desc);
void usage(int argc, char *argv[]) __attribute__((noreturn));

void kz_assert(int flag, const char* loc, const char *format, ...)
{
    if (flag == 0) {
        va_list args;

        va_start(args, format);
        fprintf(stderr, "%s:\n  ", loc);
        vfprintf(stderr, format, args);
        fprintf(stderr, "\n");
        va_end(args);
        fflush(stdout);
        fflush(stderr);
        exit(EXIT_FAILURE);
    }
}

void kz_check_error(int err, const char* loc, const char *format, ...)
{
    if (err != 0) {
        va_list args;

        va_start(args, format);
        fprintf(stderr, "%s:\n  ", loc);
        vfprintf(stderr, format, args);
        fprintf(stderr, "\n");
        fprintf(stderr, "  %s\n", strerror(err));
        va_end(args);
        fflush(stdout);
        fflush(stderr);
        exit(EXIT_FAILURE);
    }
}

void kz_error(const char* s)
{
    fprintf(stderr, "%s\n", s);
    fflush(stdout);
    fflush(stderr);
    exit(EXIT_FAILURE);
}

long double kz_get_cpu_time(void)
{
    clockid_t clk_id;
    struct timespec ts;

    clk_id = CLOCK_PROCESS_CPUTIME_ID;

    if (clock_gettime(clk_id, &ts) == 0)
        return (long double) ts.tv_sec + (long double) ts.tv_nsec / 1e9;

    return -1;
}

long double kz_get_real_time(void)
{
    clockid_t clk_id;
    struct timespec ts;

    clk_id = CLOCK_MONOTONIC_RAW;

    if (clock_gettime(clk_id, &ts) == 0)
        return (long double) ts.tv_sec + (long double) ts.tv_nsec / 1e9;

    return -1;
}

int main(int argc, char *argv[])
{
    kz_params_t params;

    if (parseOpts(&params, argc, argv) != 0) {
        parseOptsCleanup(&params);
        return EXIT_FAILURE;
    }

    kz_main(&params);

    parseOptsCleanup(&params);

    return EXIT_SUCCESS;
}

int parseOpts(kz_params_t* params, int argc, char *argv[])
{
    static struct option longopts[] = {
        { "input",         required_argument, NULL, 'i'},
        { "input-mode",    required_argument, NULL, 'm'},
        { "input-dev",     required_argument, NULL, 'd'},
        { "output",        required_argument, NULL, 'o'},
        { "output-mode",   required_argument, NULL, 'n'},
        { "output-dev",    required_argument, NULL, 'e'},
        { "dummy-samples", required_argument, NULL, 0 },
        { NULL,            0,                 NULL, 0 }
    };
    int opt;
    int option_index = 0;

    params->src_dev = DEV_FILE;
    params->src_mode = MODE_TEXT;
    params->src = NULL;
    params->dst_dev = DEV_FILE;
    params->dst_mode = MODE_TEXT;
    params->dst = NULL;
    params->dummy_samples = 0;

    while ((opt = getopt_long(argc, argv, "", longopts, &option_index)) != -1) {
        switch (opt) {
        case 'i':
            if (params->src != NULL)
                usage(argc, argv);

            params->src = (char*) malloc(strlen(optarg)+1);
            strcpy(params->src, optarg);
            break;

        case 'o':
            if (params->dst != NULL)
                usage(argc, argv);

            params->dst = (char*) malloc(strlen(optarg)+1);
            strcpy(params->dst, optarg);
            break;

        case 'm':
            params->src_mode = parseMode(argc, argv, optarg);
            break;

        case 'n':
            params->dst_mode = parseMode(argc, argv, optarg);
            break;

        case 'd':
            params->src_dev = parseDev(argc, argv, optarg);
            break;

        case 'e':
            params->dst_dev = parseDev(argc, argv, optarg);
            break;

        case 0:
            switch (option_index) {
            case 6:
                params->dummy_samples = atoi(optarg);
                break;
            }
            break;

        default:
            usage(argc, argv);
        }
    }

    return 0;
}

void parseOptsCleanup(kz_params_t* params)
{
    if (params->src != NULL)
        free(params->src);

    if (params->dst != NULL)
        free(params->dst);
}

struct mode_desc_t {
    const char* mode_desc;
    kz_mode_t   mode;
};

struct dev_desc_t {
    const char* dev_desc;
    kz_dev_t    dev;
};

static struct mode_desc_t mode_descs[] = {
    { "text",   MODE_TEXT },
    { "binary", MODE_BINARY },
    { "bin",    MODE_BINARY },
    { NULL,     (kz_mode_t) 0 }
};

static struct dev_desc_t dev_descs[] = {
    { "dummy",  DEV_DUMMY },
    { "memory", DEV_MEMORY },
    { "file",   DEV_FILE },
    { NULL,     (kz_dev_t) 0 }
};

kz_mode_t parseMode(int argc, char *argv[], const char* desc)
{
    int i;

    for (i = 0; mode_descs[i].mode_desc != NULL; i++) {
        if (strcmp(desc, mode_descs[i].mode_desc) == 0)
            return mode_descs[i].mode;
    }

    usage(argc, argv);
}

kz_dev_t parseDev(int argc, char *argv[], const char* desc)
{
    int i;

    for (i = 0; dev_descs[i].dev_desc != NULL; i++) {
        if (strcmp(desc, dev_descs[i].dev_desc) == 0)
            return dev_descs[i].dev;
    }

    usage(argc, argv);
}

void usage(int argc, char *argv[])
{
    fprintf(stderr, "Usage: %s\n",
            argv[0]);
    exit(EXIT_FAILURE);
}
