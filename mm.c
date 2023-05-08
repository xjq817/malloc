/*
this code uses explicit allocator, LIFO strategy and segregated fit

the structure of my block:

header (4 byte) + (size | l_alloc | alloc)
succ   (4 byte) : the offset of next ptr on free list if it is not allocated
prev   (4 byte) : the offset of prev ptr on free list if it is not allocated
...   block   ... 
footer (4 byte) + (size | l_alloc | alloc)

The structure of free list:

I have RANGE_SIZE size of free_list
head_listp[i] is the i-th free list head pointer
my range: RANGE is a constant
[INITIAL_SIZE, RANGE]
(RANGE, RANGE * 2]
(RANGE * 2, RANGE * 4]
(RANGE * 4, RANGE * 8]
...
(RANGE * 2^RANGE_SIZE, +infty)

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

/* define some constant */
#define WSIZE               4 /* single word */
#define DSIZE               8 /* double word */
#define INITSIZE            16
#define CHUNKSIZE           (1<<8)

/* some auxiliary functions */
#define MAX(x,y)            ((x) > (y) ? (x) : (y))
#define PACK(size, alloc)   ((size) | (alloc))

/* read a word or a ptr at addr p */
#define GET(p)              ((p) ? *(unsigned int *)(p) : 0)
#define GET_PTR(p)          ((p) ? ((GET(p)) ? GET(p) + heap_listp : 0) : 0)

/* write a word or a ptr at addr p */
#define PUT(p, val)         ((p) ? *(unsigned int *)(p) = (val) : 0)
#define PUT_PTR(p, val)     ((p) ? (*(unsigned int *)(p) = (val) ? ((unsigned int)((char *)(val) - heap_listp)) : 0) : 0)

/* read the size and allocated fields from addr p */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)
#define GET_L_ALLOC(p)      (GET(p) & 0x2)

/* compute addr of bp's header and footer */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* compute where the addr of bp's pred and succ is */
#define PRED(bp)            ((bp) ? (char *)(bp) : 0)
#define SUCC(bp)            ((bp) ? (char *)(bp) + WSIZE : 0)

/* compute addr of bp's prev and next */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* compute addr of bp's pred and succ */
#define PRED_PTR(bp)        ((bp) ? (GET_PTR(PRED(bp))) : 0)
#define SUCC_PTR(bp)        ((bp) ? (GET_PTR(SUCC(bp))) : 0)

/* constant about segregated fit */
#define RANGE_SIZE          (20)
#define RANGE               (48)

static char *heap_listp = 0; /* the pointer to the prologue block */
static char *epilogue = 0; /* the pointer to the epilogue block */
static char *head_listp[RANGE_SIZE]; /* the head pointers of the lists about segregated fit */

/* given the size of the block, 
   returns the index of the list in which the block is located */
static size_t get_range(size_t size){
    size_t id = 0, upper = RANGE;
    while(upper < size && id < RANGE_SIZE - 1){
        upper <<= 1;
        id++;
    }
    return id;
}

/* adds a block to a linked list */
static void add_into_list(void *bp){
    size_t id = get_range(GET_SIZE(HDRP(bp)));
    PUT_PTR(PRED(bp), 0);
    PUT_PTR(SUCC(bp), head_listp[id]);
    PUT_PTR(PRED(head_listp[id]), bp);
    head_listp[id] = bp;
}

/* deletes a block to a linked list */
static void delete_from_list(void *bp){
    PUT_PTR(SUCC(PRED_PTR(bp)), SUCC_PTR(bp));
    PUT_PTR(PRED(SUCC_PTR(bp)), PRED_PTR(bp));
    if (!PRED_PTR(bp)){
        size_t id = get_range(GET_SIZE(HDRP(bp)));
        head_listp[id] = SUCC_PTR(bp);
    }
}

/* see if it can merge with the two blocks adjacent to the address */
static void *coalesce(void *bp){
    unsigned prev_alloc = GET_L_ALLOC(HDRP(bp));
    unsigned next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc){
        add_into_list(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        delete_from_list(NEXT_BLKP(bp));

        PUT(HDRP(bp), PACK(size, 2));
        PUT(FTRP(bp), PACK(size, 2));

        add_into_list(bp);
    }
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        
        delete_from_list(PREV_BLKP(bp));

        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 2));
        PUT(FTRP(bp), PACK(size, 2));

        add_into_list(bp);
    }
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))
             + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        
        delete_from_list(PREV_BLKP(bp));
        delete_from_list(NEXT_BLKP(bp));
        
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 2));
        PUT(FTRP(bp), PACK(size, 2));

        add_into_list(bp);
    }
    return bp;
}

/* expand the heap when it runs out of space */
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    PUT(HDRP(bp), PACK(size, GET_L_ALLOC(HDRP(bp))));
    PUT(FTRP(bp), PACK(size, GET_L_ALLOC(HDRP(bp))));

    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    epilogue = NEXT_BLKP(bp);

    return coalesce(bp);
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void){
    for (size_t i = 0; i < RANGE_SIZE; i++)
        head_listp[i] = 0;
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(INITSIZE, 3));
    heap_listp += (2*WSIZE);
    PUT_PTR(heap_listp, 0);
    PUT_PTR(heap_listp + (1*WSIZE), 0);
    PUT(heap_listp + (2*WSIZE), PACK(INITSIZE, 3));
    PUT(heap_listp + (3*WSIZE), PACK(0, 3));

    return 0;
}

/* given the desired size, find a suitable block or return one that cannot be found */
static void *find_fit(size_t asize){
    size_t id = get_range(asize);
    while(id < RANGE_SIZE){
        char* bp = head_listp[id];
        while(bp){
            size_t size = GET_SIZE(HDRP(bp));
            if (size >= asize) return bp;
            bp = SUCC_PTR(bp);
        }
        id++;
    }
    return NULL;
}

/* for blocks starting with bp, to allocate the space of asize */
static void place(void *bp, size_t asize){
    size_t size = GET_SIZE(HDRP(bp));
    unsigned is_alloc = GET_ALLOC(HDRP(bp));
    unsigned is_l_alloc = GET_L_ALLOC(HDRP(bp));
    if (!is_alloc) delete_from_list(bp);
    if (size < asize + INITSIZE){
        PUT(HDRP(bp), PACK(size, is_l_alloc | 1));
        PUT(FTRP(bp), PACK(size, is_l_alloc | 1));
        PUT(HDRP(NEXT_BLKP(bp)),
            PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 2 | GET_ALLOC(HDRP(NEXT_BLKP(bp)))));
    }
    else{
        PUT(HDRP(bp), PACK(asize, is_l_alloc | 1));
        PUT(FTRP(bp), PACK(asize, is_l_alloc | 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK(size - asize, 2));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size - asize, 2));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(NEXT_BLKP(bp)),
            PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), GET_ALLOC(HDRP(NEXT_BLKP(bp)))));
        if (!is_alloc) add_into_list(bp);
        else coalesce(bp);
    }
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size){
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) return NULL;
    
    asize = ALIGN(MAX(size + WSIZE, INITSIZE));

    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * free - We know how to free a block.  So we do not ignore this call.
 */
void free(void *bp){
	/*Get gcc to be quiet */
    if (bp < mem_heap_lo() || bp > mem_heap_hi()) return;
    
	size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, GET_L_ALLOC(HDRP(bp))));
    PUT(FTRP(bp), PACK(size, GET_L_ALLOC(HDRP(bp))));
    PUT(HDRP(NEXT_BLKP(bp)), 
        PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))),
             GET_ALLOC(HDRP(NEXT_BLKP(bp)))));

    coalesce(bp);
}

/*
 * realloc - Change the size of the block by mallocing a new block, copying its data.
 *      when smaller blocks can be allocated, or when they can be merged with next blocks to meet the size, 
 *      not need free(oldptr) , otherwises need.
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
 
 */
void mm_checkheap(int verbose){
    /* check the epilogue and prologue blocks
       prologue has information of header, footer, alloc and size
       epilogue has information of header, alloc and size */
    if(verbose == 0){
        printf("prologue: header: %lu, footer: %lu, alloc: %d, size: %u\n",
            (size_t)HDRP(heap_listp), (size_t)FTRP(heap_listp),
            GET_ALLOC(HDRP(heap_listp)), GET_SIZE(HDRP(heap_listp)));
        printf("epilogue: header: %lu, alloc: %u, size: %u\n",
            (size_t)HDRP(epilogue), GET_ALLOC(HDRP(epilogue)), GET_SIZE(HDRP(epilogue)));
    }
    /* check the address arrangement of the block */
    else if(verbose == 1){
        printf("begin check heap list\n");
        char* bp = heap_listp;
        int id = 0;
        while(GET_SIZE(HDRP(NEXT_BLKP(bp))) > 0){
            id++;

            bp = NEXT_BLKP(bp);
            size_t size = GET_SIZE(HDRP(bp));
            unsigned alloc = GET_ALLOC(HDRP(bp));

            printf("block:%d ,address: %lu ,size: %lu, alloc :%u ,next_block : %lu\n",
                id, (size_t)bp, size, alloc, (size_t)NEXT_BLKP(bp));
        }
        printf("finish check heap list\n");
    }
    /* check boundry of heap */
    else if(verbose == 2){
        printf("begin check boundry of heap\n");
        char* bp = heap_listp;
        size_t size = GET_SIZE(HDRP(bp));
        while(size > 0){
            if((size_t)bp < (size_t)mem_heap_lo() || (size_t)bp > (size_t)mem_heap_hi()){
                printf("illegal ptr: %lu\n", (size_t)(bp));
                exit(0);
            }
            bp = NEXT_BLKP(bp);
            size = GET_SIZE(HDRP(bp));
        }
        printf("finish check boundry of heap\n");
    }
    /* check the header and footer for each block */
    else if(verbose == 3){
        printf("begin check the header and footer for each block\n");
        char* bp = heap_listp;
        size_t size_h = GET_SIZE(HDRP(bp));
        size_t size_f = GET_SIZE(FTRP(bp));
        unsigned alloc_h = GET_ALLOC(HDRP(bp));
        unsigned alloc_f = GET_ALLOC(FTRP(bp));
        while(size_h > 0){
            /* check that the header and footer are the same size */
            if(size_h != size_f){
                printf("size unmatch: %lu\n", (size_t)(bp));
                exit(0);
            }
            /* check that the header and footer are the same alloc */
            if(alloc_f != alloc_h){
                printf("alloc unmatch: %lu\n", (size_t)(bp));
                exit(0);
            }
            bp = NEXT_BLKP(bp);
            size_h = GET_SIZE(HDRP(bp));
            size_f = GET_SIZE(FTRP(bp));
            alloc_h = GET_ALLOC(HDRP(bp));
            alloc_f = GET_ALLOC(FTRP(bp));
        }
        printf("finish check the header and footer for each block\n");
    }
    /* check that there are no two consecutive free blocks in the heap */
    else if(verbose == 4){
        printf("begin check that there are no two consecutive free blocks in the heap\n");
        char* prev = heap_listp;
        char* now = NEXT_BLKP(heap_listp);
        size_t size = GET_SIZE(HDRP(now));
        while(size > 0){
            if(!GET_ALLOC(HDRP(prev)) && !GET_ALLOC(HDRP(now))){
                printf("two adjacent free block: %lu %lu\n", (size_t)(prev), (size_t)(now));
                exit(0);
            }
            prev = NEXT_BLKP(prev);
            now = NEXT_BLKP(now);
            size = GET_SIZE(HDRP(now));
        }
        printf("finish check that there are no two consecutive free blocks in the heap\n");
    }
    /* check that all succ and pred pointers are consistent */
    else if(verbose == 5){
        printf("begin check that all succ and pred pointers are consistent\n");

        for (size_t id = 0; id < RANGE_SIZE; id++){
            char* prev = head_listp[id];
            if (!prev) continue;
            char* bp = SUCC_PTR(prev);
            while(bp){
                if (PRED_PTR(bp) != prev){
                    printf("pred succ not match: prev: %lu, succ: %lu\n", (size_t)(prev), (size_t)(bp));
                    exit(0);
                }
                prev = bp;
                bp = SUCC_PTR(bp);
            }
        }
        printf("finish check that all succ and pred pointers are consistent\n");
    }
    /* check if ptr in free list are in boundry */
    else if(verbose == 6){
        printf("begin check if ptr in free list are in boundry\n");
        for(size_t id = 0; id < RANGE_SIZE; id++){
            char *bp = head_listp[id];
            while(bp){
                if((size_t)bp < (size_t)mem_heap_lo() || (size_t)bp > (size_t)mem_heap_hi()){
                    printf("illegal ptr: %lu\n", (size_t)(bp));
                    exit(0);
                }
                bp = SUCC_PTR(bp);
            }
        }
        printf("finish check if ptr in free list are in boundry\n");
    }
    /* check that the free list matches the free block in the heap */
    else if (verbose == 7){
        printf("begin check that the free list matches the free block in the heap\n");
        int free_cnt = 0;
        for (size_t id = 0; id < RANGE_SIZE; id++){
            char *bp = head_listp[id];
            while(bp){
                free_cnt++;
                if (GET_ALLOC(HDRP(bp))){
                    printf("block: %lu are allocated, but is in the free list\n", (size_t)(bp));
                    exit(0);
                }
                bp = SUCC_PTR(bp);
            }
        }
        char *bp = heap_listp;
        while(GET_SIZE(HDRP(bp))){
            if (!GET_ALLOC(HDRP(bp))) free_cnt--;
            bp = NEXT_BLKP(bp);
        }
        if (free_cnt){
            printf("the total size of the free list is different from the number of free blocks in the heap\n");
            exit(0);
        }
        printf("finish check that the free list matches the free block in the heap\n");
    }
    /* check that all blocks in each free list fall within the list size range */
    else if(verbose == 8){
        printf("begin check that all blocks in each free list fall within the list size range\n");
        for(size_t id = 0; id < RANGE_SIZE; id++){
            char *bp = head_listp[id];
            while(bp != 0){
                size_t size = GET_SIZE(HDRP(bp));
                if((id < RANGE_SIZE - 1 && size > (size_t)(RANGE << id))
                    || (id > 0 && size <= (size_t)(RANGE << (id - 1)))){
                    printf("size unmatch: ptr: %lu, size: %lu, id: %lu\n", (size_t)(bp), size, id);
                    exit(0);
                }
                bp = SUCC_PTR(bp);
            }
        }
        printf("finish check that all blocks in each free list fall within the list size range\n");
    }
}