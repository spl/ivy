#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

enum pipe_funcs {
    ADD1,
    MUL2,
    READER,
    WRITER,
    FREER,
};

#define CHUNK_SIZE 10000

struct stage {
    struct stage *next;
    pthread_cond_t *cv;
    pthread_mutex_t *mut;
    char *data;
    unsigned int size;
    int func;
    int last;
};

unsigned int do_work(char *data, unsigned int size, int func);

void *thr_func(struct stage *S)
{
    unsigned int size = 0;
    int last = 0;
    unsigned int ret;
    char *data = NULL;

    while (!last) {
        pthread_mutex_lock(S->mut);
        while (!S->data)
            pthread_cond_wait(S->cv,S->mut);
        size = S->size;
        data = S->data;
        last = S->last;
        S->data = NULL;
        S->size = 0;
        pthread_cond_signal(S->cv);
        pthread_mutex_unlock(S->mut);
        if ((ret = do_work(data,size,S->func)) < size) {
            size = ret;
            pthread_mutex_lock(S->mut);
            last = S->last = 1;
            pthread_mutex_unlock(S->mut);
        }
        if (S->next) {
            pthread_mutex_lock(S->next->mut);
            while (S->next->data)
                pthread_cond_wait(S->next->cv,S->next->mut);
            S->next->size = size;
            S->next->data = data;
            S->next->last = last;
            pthread_cond_signal(S->next->cv);
            pthread_mutex_unlock(S->next->mut);
        }
    }

    pthread_mutex_lock(S->mut);
    S->data = NULL;
    S->size = 0;
    pthread_cond_signal(S->cv);
    pthread_mutex_unlock(S->mut);

    return NULL;
}

FILE *inFile;
FILE *outFile;
unsigned int do_work(char *data, unsigned int size, int func)
{
    unsigned int ret;
    int i;

    switch(func) {
        case ADD1:
            for (i = 0; i < size; i++)
                data[i] = data[i] + 1;
            ret = size;
        break;
        case MUL2:
            for (i = 0; i < size; i++)
                data[i] = data[i] * 2;
            ret = size;
        break;
        case READER:
            ret = fread(data,sizeof(char),size,inFile);
        break;
        case WRITER:
            if (size) fwrite(data,sizeof(char),size,outFile);
            ret = size;
        break;
        case FREER:
            if (data) free(data);
            ret = size;
        break;
        default:
            ret = size;
        break;
    }

    return ret;
}

struct stage *make_stage(struct stage *next, int func)
{
    struct stage *new = malloc(sizeof(struct stage));
    pthread_cond_t *cv = malloc(sizeof(pthread_cond_t));
    pthread_mutex_t *mut = malloc(sizeof(pthread_mutex_t));

    new->next = next;
    new->cv = cv;
    new->mut = mut;
    new->data = NULL;
    new->size = 0;
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
        while (readstage->data)
            pthread_cond_wait(readstage->cv,readstage->mut);
        if (readstage->last) {
            pthread_mutex_unlock(readstage->mut);
            break;
        }
        readstage->size = CHUNK_SIZE;
        readstage->data = malloc(CHUNK_SIZE * sizeof(char));
        pthread_cond_signal(readstage->cv);
        pthread_mutex_unlock(readstage->mut);
    }

    for(i = 0; i < 5; i++) {
        if (pthread_join(tid[i],NULL) != 0)
            printf("joining on %d failed.\n", i);
    }

    return 0;
}
