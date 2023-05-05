/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

#define WSIZE               4
#define DSIZE               8
#define CHUNKSIZE           (1<<12)

#define MAX(x,y)            ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)   ((size) | (alloc))

#define GET(p)              (*(unsigned int *)(p))
#define GET_PTR(p)          ((p) ? (void *)*(size_t *)(p) : 0)

#define PUT(p, val)         (*(unsigned int *)(p) = (val))
#define PUT_PTR(p, ptr)     ((p) ? *(size_t *)(p) = (size_t)(ptr) : 0)

#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define PRED(bp)            ((bp) ? (char *)(bp) : 0)
#define SUCC(bp)            ((bp) ? (char *)(bp) + DSIZE : 0)

#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED_PTR(bp)        ((bp) ? (GET_PTR(PRED(bp))) : 0)
#define SUCC_PTR(bp)        ((bp) ? (GET_PTR(SUCC(bp))) : 0)

static char *heap_listp = 0;
static char *head_listp = 0;

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
        if (!head_listp){
            head_listp = bp;
            PUT_PTR(PRED(bp), 0);
            PUT_PTR(SUCC(bp), 0);
        }
        else{
            char *last_listp = 0;
            char *now_listp = head_listp;
            if (head_listp > bp) head_listp = bp;
            while(now_listp && now_listp < bp){
                last_listp = now_listp;
                now_listp = SUCC_PTR(now_listp);
            }
            PUT_PTR(SUCC(last_listp), bp);
            PUT_PTR(PRED(bp), last_listp);
            PUT_PTR(SUCC(bp), now_listp);
            PUT_PTR(PRED(now_listp), bp);
        }
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        if (!head_listp || head_listp >= NEXT_BLKP(bp))
            head_listp = bp;
        PUT_PTR(SUCC(PRED_PTR(NEXT_BLKP(bp))), bp);
        PUT_PTR(PRED(bp), PRED_PTR(NEXT_BLKP(bp)));
        PUT_PTR(SUCC(bp), SUCC_PTR(NEXT_BLKP(bp)));
        PUT_PTR(PRED(SUCC_PTR(NEXT_BLKP(bp))), bp);
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){
        if (!head_listp || head_listp >= PREV_BLKP(bp))
            head_listp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{
        if (!head_listp || head_listp >= PREV_BLKP(bp))
            head_listp = PREV_BLKP(bp);
        PUT_PTR(SUCC(PREV_BLKP(bp)), SUCC_PTR(NEXT_BLKP(bp)));
        PUT_PTR(PRED(SUCC_PTR(NEXT_BLKP(bp))), PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))
             + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // printf("extend_heap begin:%lu\n",size);
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    // printf("extend_heap end\n");

    return coalesce(bp);
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void){
    // puts("mm_init begin");
    head_listp = 0;
    if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(6*WSIZE, 1));
    PUT_PTR(heap_listp + (2*WSIZE), 0);
    PUT_PTR(heap_listp + (4*WSIZE), 0);
    PUT(heap_listp + (6*WSIZE), PACK(6*WSIZE, 1));
    PUT(heap_listp + (7*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    // mm_checkheap(1);
    // mm_checkheap(2);
    // puts("mm_init finish");
    return 0;
}

static void *find_fit(size_t asize){
    char* bp = head_listp;
    // printf("find begin\n");
    while(bp){
        size_t size = GET_SIZE(HDRP(bp));
        if (size >= asize){
            // printf("find it\n");
            return bp;
        }
        bp = SUCC_PTR(bp);
    }
    // printf("not find it\n");
    return NULL;
}

static void place(void *bp, size_t asize){
    size_t size = GET_SIZE(HDRP(bp));
    size_t remain_size = size - asize;
    // printf("place begin size=%d remain_size=%d\n",size,remain_size);
    if (remain_size <= 6*WSIZE){
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        // printf("pred_ptr=%d succ_ptr=%d\n",(int)PRED_PTR(bp),(int)SUCC_PTR(bp));
        PUT_PTR(SUCC(PRED_PTR(bp)), SUCC_PTR(bp));
        PUT_PTR(PRED(SUCC_PTR(bp)), PRED_PTR(bp));
        if (head_listp == bp)
            head_listp = SUCC_PTR(bp);
    }
    else{
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // printf("pred_ptr=%d succ_ptr=%d\n",(int)PRED_PTR(bp),(int)SUCC_PTR(bp));
        PUT_PTR(SUCC(PRED_PTR(bp)), NEXT_BLKP(bp));
        PUT_PTR(PRED(NEXT_BLKP(bp)), PRED_PTR(bp));
        PUT_PTR(SUCC(NEXT_BLKP(bp)), SUCC_PTR(bp));
        PUT_PTR(PRED(SUCC_PTR(bp)), NEXT_BLKP(bp));
        // printf("next_blkp_pred_ptr=%d\n",(int)PRED_PTR(NEXT_BLKP(bp)));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remain_size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remain_size, 0));
        if (head_listp == bp)
            head_listp = NEXT_BLKP(bp);
    }
    // printf("place end\n");
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size){
    // printf("malloc begin:%ld\n", size);
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    
    asize = ALIGN(MAX(size + DSIZE, 6 * WSIZE));

    if ((bp = find_fit(asize)) != NULL){
        // printf("can find: %d\n",GET_SIZE(HDRP(bp)));
        place(bp, asize);
        // printf("malloc finish\n");
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    // printf("can not find: %d\n",GET_SIZE(HDRP(bp)));
    place(bp, asize);
    // printf("malloc finish\n");
    return bp;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *bp){
	/*Get gcc to be quiet */
    if (bp < mem_heap_lo() || bp > mem_heap_hi()) return;
    // printf("free begin\n");
	size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
    // printf("free end\n");
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
void *realloc(void *oldptr, size_t size){
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = *SIZE_PTR(oldptr);
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size){
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
void mm_checkheap(int verbose){
	puts("***********************************");
        /*Get gcc to be quiet. */
    char* bp = heap_listp;
    size_t size = GET_SIZE(HDRP(bp));
    int alloccc;
    if(verbose == 1){ //traverse free list
        printf("free_list:\n");
        char* bp = head_listp;
        int cnt = 0;
        size_t size;
        while(bp != 0){
            cnt++;
            size = GET_SIZE(HDRP(bp));
            printf("block:%d address: %ld size: %lu next_list: %lu next_block: %lu \n",cnt,bp,size,SUCC_PTR(bp),NEXT_BLKP(bp));
            bp = SUCC_PTR(bp);
            if(cnt > 380)break;
        }
        puts("finish check");
    }
    else if(verbose == 2){ //traverse whole list
        printf("heap_list: %ld size: %u\n",bp,size);
        int cnt = 0;
        while(size > 0){
            cnt++;
            bp = NEXT_BLKP(bp);
            size = GET_SIZE(HDRP(bp));
            alloccc = GET_ALLOC(HDRP(bp));
            printf("block:%d address: %ld size: %lu alloc: %d nxt: %lu \n",cnt,bp,size,alloccc,SUCC_PTR(bp));
        }
    }
    puts("");
}