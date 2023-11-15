// [ Explicit  / first fit ]
/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "TEAM 02",
    /* First member's full name */
    "J_MaG",
    /* First member's email address */
    "example@example.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* **********************[ DEFINE MACROS SETTING ]******************************* */
/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */
/* 2의 비트 연산으로 4096 bytes를 제공한다. 한 페이지의 단위이기도 함. */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/*   Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*  Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE) //block header
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //block footer

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//[TYPE 1] 
#define PRED(bp) ((void** )(bp))
#define SUCC(bp) ((void** )(bp + WSIZE))

/* **********************[ FIRST FIT strategy ]******************************* */

///////////////////// [ DECLARATION : 선언부 ]//////////////////////////////
static void* heap_listp;
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t sizt);

///////////////////// [ FIT STRAGEGY : 메모리 할당 정책 ]//////////////////////////////
/* find fit strategy */
// [ First fit ] //
//Perf index = 44 (util) + 9 (thru) = 53/100
static void* find_fit(size_t asize){

    void* bp;

    /* First-fit search */
    for (bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp=NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }

    return NULL; /* No fit */
}



/////////////////////[ FREE / DEALLOCATE : 할당 해제  ]//////////////////////////////
/*
coalese free blocks
할당 해제된 블록을 합한다.
*/
static void* coalesce(void* bp){


    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //case 1 : [ 1 ][ 0 ][ 1 ]  _ 101
    // 둘 다 1일 경우 - 할당 되어 있음, 결합 금지.
    if (prev_alloc && next_alloc){
        return bp; 
    }
    //case 2 : [ 1 ][ 0 ][ 0 ] _ 100
    // 뒷 블록이 0일 경우, 결합
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    //case 3 : [ 0 ][ 0 ][ 1 ] _ 001
    // 앞 블록이 0일 경우, 결합
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);        
    }
    //case 4 : [ 0 ][ 0 ][ 0 ] _ 000
    // 앞뒤블록이 모두 0일 경우 통째로 결합
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))+ GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);

}

/////////////////////[ HANDLING HEAP : 힙 초기화 & 힙 조작 ]//////////////////////////////
/* 
 * mm_init - initialize the malloc package.
 initialize Run-time heap created by malloc
 */



int mm_init(void)

 // [TYPE 1] using 2 blocks for pred&succ

 // [ 0/1 ][ 32/1 ][ PRED ][ SUCC ][ 32/1 ][ 0/1 ]
 //------------------------------------------------
 //               ^ heap_listp;
 //________________________________________________
 //   x      ph     ->succ  ->pred    pf    ep-block
 //                 or NULL  or NULL
 //-------------------------------------------------
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); /* Alignment padding */

    PUT(heap_listp + (1*WSIZE), PACK(2*DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (4*WSIZE), PACK(2*DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (5*WSIZE), PACK(0, 1)); /* Epilogue header */

    // Pred & Succ blocks
    PUT(heap_listp + (2*WSIZE), heap_listp + (3*WSIZE));
    PUT(heap_listp + (3*WSIZE), heap_listp + (2*WSIZE));
    
    heap_listp += (2*WSIZE); 
    //header와 footer 사이에 bp 를 세팅.
    //[TYPE 1] : payload 였던 부분에 pred와 succ를 놓으므로 pred앞에 heap_list를 놓는다.

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* Extend the heap */
static void* extend_heap(size_t words){

    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
    
}

/////////////////////[ [TYPE 1] setting ]///////////////////////////////
/* free 블록 생성시 payload에 2칸의 블록을 사용하여 이전/이후 블록의 주소를 저장한다. */
static void* put_freeblock(void* bp){
    PRED(p) = heap_listp;
    SUCC(p) = SUCC(heap_listp);

    PRED(SUCC(heap_listp)) = bp;
    SUCC(heap_listp) = bp;
}

static void* rm_blocks(void* bp){


}

/////////////////////[ PLACING : 블록 조정 ]//////////////////////////////

/* place the size of block to the bp */
static void place(void* bp, size_t asize)
{
    //csize = current size / 현재 블록의 사이즈
    //asize = adjusted input size / 선행 함수에서 조정된 사이즈
    size_t csize = GET_SIZE(HDRP(bp));
    
    if((csize-asize)>= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


///////////////////// MALLOC : 말록 //////////////////////////////

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{

    size_t asize;     /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char* bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;

    else //size>DSIZE
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);

    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

    /* ORIGINAL SOURCE CODES */
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}


///////////////////// REALLOC : 재조정 //////////////////////////////
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
