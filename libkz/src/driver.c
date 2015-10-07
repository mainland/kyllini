#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>

#include <kz.h>

int parseOpts(kz_params_t*, int, char *[]);
kz_mode_t parseMode(int argc, char *argv[], const char*);
kz_dev_t parseDev(int argc, char *argv[], const char* desc);
void usage(int argc, char *argv[]);

int main(int argc, char *argv[])
{
    kz_params_t params;

    if (parseOpts(&params, argc, argv) != 0)
        return EXIT_FAILURE;

    kz_main(&params);

    return EXIT_SUCCESS;
}

int parseOpts(kz_params_t* params, int argc, char *argv[])
{
    struct option longopts[] = {
        { "input",       required_argument, NULL, 'i'},
        { "input-mode",  required_argument, NULL, 'm'},
        { "input-dev",   required_argument, NULL, 'd'},
        { "output",      required_argument, NULL, 'o'},
        { "output-mode", required_argument, NULL, 'n'},
        { "output-dev",  required_argument, NULL, 'e'},
        { NULL,          0,                 NULL, 0 }
    };
    int opt;

    params->src_dev = DEV_FILE;
    params->src_mode = MODE_TEXT;
    params->src = NULL;
    params->dst_dev = DEV_FILE;
    params->dst_mode = MODE_TEXT;
    params->dst = NULL;

    while ((opt = getopt_long(argc, argv, "", longopts, NULL)) != -1) {
        switch (opt) {
        case 'i':
            if (params->src != NULL)
                usage(argc, argv);

            params->src = malloc(strlen(optarg)+1);
            strcpy(params->src, optarg);
            break;

        case 'o':
            if (params->dst != NULL)
                usage(argc, argv);

            params->dst = malloc(strlen(optarg)+1);
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

        default:
            usage(argc, argv);
        }
    }

    return 0;
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
    { NULL,     0 }
};

static struct dev_desc_t dev_descs[] = {
    { "dummy",  DEV_DUMMY },
    { "memory", DEV_MEMORY },
    { "file",   DEV_FILE },
    { NULL,     0 }
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
