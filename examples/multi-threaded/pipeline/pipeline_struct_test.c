#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

#define SHARC_ON

#ifdef SHARC_ON
#include <sharc/sharc.h>
#else
#define SPRIVATE
#define SREADONLY
#define SLOCKED(x)
#define SDYNAMIC
#define SRACY
#define SCAST(x) (x)
#define SINIT(x) (x)
#endif

#define CHUNK_SIZE 10000

enum pipe_funcs {
    ADD1,
    MUL2,
    READER,
    WRITER,
    FREER,
};

struct data {
    char *data;
    unsigned int size;
};

struct stage {
    struct stage *next;
    pthread_cond_t *cv;
    pthread_mutex_t * SREADONLY mut;
    struct data *SLOCKED(mut) sdata;
    int func;
    int SLOCKED(mut) last;
};

static unsigned int do_work(struct data *d, int func);

void *thr_func(struct stage *S)
{
    struct data *ldata;
    unsigned int size = 0;
    int last = 0;
    unsigned int ret;
    char *data = NULL;

    while (!last) {
        pthread_mutex_lock(S->mut);
        while (!S->sdata)
            pthread_cond_wait(S->cv,S->mut);
        last = S->last;
        ldata = SCAST(S->sdata);
        S->sdata = NULL;
        pthread_mutex_unlock(S->mut);
        pthread_cond_signal(S->cv);
        size = ldata->size;
        if ((ret = do_work(ldata, S->func)) < size) {
            ldata->size = ret;
            pthread_mutex_lock(S->mut);
            last = S->last = 1;
            pthread_mutex_unlock(S->mut);
        }
        if (S->next) {
            pthread_mutex_lock(S->next->mut);
            while (S->next->sdata)
                pthread_cond_wait(S->next->cv,S->next->mut);
            S->next->sdata = SCAST(ldata);
            ldata = NULL;
            S->next->last = last;
            pthread_mutex_unlock(S->next->mut);
            pthread_cond_signal(S->next->cv);
        }
    }

    pthread_mutex_lock(S->mut);
    S->sdata = NULL;
    pthread_mutex_unlock(S->mut);
    pthread_cond_signal(S->cv);

    return NULL;
}

FILE *inFile;
FILE *outFile;
static unsigned int do_work(struct data *d, int func)
{
    unsigned int ret;
    int i;

    switch(func) {
        case ADD1:
            for (i = 0; i < d->size; i++)
                d->data[i] = d->data[i] + 1;
            ret = d->size;
        break;
        case MUL2:
            for (i = 0; i < d->size; i++)
                d->data[i] = d->data[i] * 2;
            ret = d->size;
        break;
        case READER:
            ret = fread(d->data,sizeof(char),d->size,inFile);
        break;
        case WRITER:
            if (d->size) fwrite(d->data,sizeof(char),d->size,outFile);
            ret = d->size;
        break;
        case FREER:
            ret = d->size;
            if (d->data) free(d->data);
            d->data = NULL;
            free(d);
        break;
        default:
            ret = d->size;
        break;
    }

    return ret;
}

static struct stage *make_stage(struct stage *next, int func)
{
    struct stage *new = malloc(sizeof(struct stage));
    pthread_mutex_t *tmut = malloc(sizeof(pthread_mutex_t));

    new->next = next;
    new->cv = malloc(sizeof(pthread_cond_t));
    new->mut = SINIT(tmut);
    new->sdata = NULL;
    new->func = func;
    new->last = 0;

    pthread_mutex_init(new->mut,NULL);
    pthread_cond_init(new->cv,NULL);

    return new;
}

int main()
{
    pthread_t tid[5];
    int i;
    struct stage *freestage = make_stage(NULL,FREER);
    struct stage *writestage = make_stage(freestage,WRITER);
    struct stage *add1stage = make_stage(writestage,ADD1);
    struct stage *mul2stage = make_stage(add1stage,MUL2);
    struct stage *readstage = make_stage(mul2stage,READER);

    inFile = fopen("inFile.txt","r");
    outFile = fopen("outFile.txt","w");

    pthread_create(&tid[0],NULL,thr_func,readstage);
    pthread_create(&tid[1],NULL,thr_func,mul2stage);
    pthread_create(&tid[2],NULL,thr_func,add1stage);
    pthread_create(&tid[3],NULL,thr_func,writestage);
    pthread_create(&tid[4],NULL,thr_func,freestage);

    while (1) {
        pthread_mutex_lock(readstage->mut);
        while (readstage->sdata)
            pthread_cond_wait(readstage->cv,readstage->mut);
        if (readstage->last) {
            pthread_mutex_unlock(readstage->mut);
            break;
        }
        readstage->sdata = malloc(sizeof(struct data));
        readstage->sdata->size = CHUNK_SIZE;
        readstage->sdata->data = malloc(CHUNK_SIZE * sizeof(char));
        pthread_cond_signal(readstage->cv);
        pthread_mutex_unlock(readstage->mut);
    }

    for(i = 0; i < 5; i++) {
        if (pthread_join(tid[i],NULL) != 0)
            printf("joining on %d failed.\n", i);
    }

    return 0;
}
