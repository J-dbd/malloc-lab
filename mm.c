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
/* block 단위로 정보를 가져오는 것이 효율적이다. */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
/* size에 Alignment에서 1을 뺀 값을 더하고 비트 연산으로 
    가장 가까운 Alignment의 배수로 올리거나 내려 준다. */
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
/* size 와 alloc(0/1)의 비트 연산을 통해 
[(size)의 비트][000] / [(size)의 비트]][001] 로 pack한다. 
이것은 header나 footer에 들어간다. */
#define PACK(size, alloc) ((size) | (alloc))

/*   Read and write a word at address p */
/* 주소(address) p에 있는 값을 참조해서 
    32bit(4byte)의 unsigned int 형태로
    읽어오고(GET), 쓴다(PUT).*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
/* 주소 p의 값을 읽어와(GET(p)) 
비트 연산으로 size와 alloc(할당여부)을 각각 추출한다. 
*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*  Given block ptr bp, compute address of its header and footer */
/* 블록의 payload의 시작점을 가리키는 포인터 bp로 
    이 블록의 header pointer address와 footer pointer address를 추출한다. 
    footer pointer(FTRP)는 header pointer에서 size를 추출하여 계산한다. */
/* void*로 들어오는 bp를 char* 타입으로 캐스팅하는 이유는 byte연산을 위해서이다. 메모리 주소(memory address in intel x86)는 byte adrress format으로 표현되는데, bp를 int*로 받는다면, int*는 뒤에 오는 -WSIZE(4) 연산 시 int(4byte)단위로 연산을 한다. 따라서 이 int* bp에 -4을 한다면 -4byte가 아니라 -16byte(4*4byte)가 된다. 그러나 char*는 연산 시 char(1byte)단위 로 연산이 되어 정확히 -4byte(4*1byte)가 가능해진다. 

     */
#define HDRP(bp) ((char *)(bp) - WSIZE) //block header
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //block footer

/* Given block ptr bp, compute address of next and previous blocks */
/* 다음 블록의 bp를 현재 bp에서 현재 블록의 size만큼 추출해서 한 칸 만큼 빼고(header만큼의 word size), 이전 블록의 bp를 현재 블록의 size만큼 빼고 두 칸 만큼 빼서 이전 블록의 payload의 위치(메모리 주소)를 얻는다. */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))



/* **********************[ FIRST FIT strategy ]******************************* */

///////////////////// [ DECLARATION : 선언부 ]//////////////////////////////
static void* heap_listp;
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t sizt);

static char* recent_bp;

///////////////////// [ FIT STRAGEGY : 메모리 할당 정책 ]//////////////////////////////
/* find fit strategy */
// [ First fit ] //
//Perf index = 44 (util) + 9 (thru) = 53/100
// static void* find_fit(size_t asize){

//     void* bp;

//     /* First-fit search */
//     for (bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp=NEXT_BLKP(bp)){
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             return bp;
//         }
//     }

//     return NULL; /* No fit */
// }

// [ Next - fit ]
static void* find_fit(size_t asize){
    char* bp;

    //bp = recent_bp;

    for(bp = NEXT_BLKP(recent_bp) ; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)){
    //for(bp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)){
        if((!GET_ALLOC(HDRP(bp))) && GET_SIZE(HDRP(bp))>=asize){
            recent_bp = bp;
            return bp;
        }
        
    }
    //type 1 : free block의 크기가 0보다 큰 모두를 탐색 
    //for (bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)){ 

    //type 2 : 가장 최근 블록 이전 까지만 탐색
    //Perf index = 43 (util) + 38 (thru) = 81/100
    
    for (bp = heap_listp; bp<=recent_bp; bp = NEXT_BLKP(bp)){
        if(!(GET_ALLOC(HDRP(bp))) && GET_SIZE(HDRP(bp))>=asize){
            //recent_bp = bp;
            return bp;
        }
    }

    return NULL;

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
        recent_bp=bp;
        return bp; 
    }
    //case 2 : [ 1 ][ 0 ][ 0 ] _ 100
    // 뒷 블록이 0일 경우, 결합
    /* 뒷 블록의 bp를 통해 Footer 를 계산하지 않고 현재 블록의 bp로 footer를 구하는 이유는 HDRP(bp)로 구한 header address에 에 PUT을 통해 size를 갱신해주었기 때문이다. FTRP는 HDRP에서 사이즈를 추출하여 현재 블록의 bp에서 footer를 찾는데 그 사이즈가 이미 갱신된 사이즈고, 따라서 현재 Header는 이미 뒷블록 사이즈까지 결합된 size를 품고 있다.   */
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
    recent_bp=bp;
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
 실제 메모리 공간에서 사용할 힙을 초기화한다.
 */
int mm_init(void)

{
    /* Create the initial empty heap */
    //sbrk는 이동 전 위치를 return한다. 
    // if의 조건 안에서 heap_listp라는 변수에 넣어주는 것이 C에선 가능하다
    //아무튼 여기선 넓힌 공간이 -1, 즉 sbrk가 실패한 return을 보내주면
    //이 함수의 결과도 -1을 보내 실패함을 알린다.
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    /* heap의 가장 첫 word size의 공간(4byte)과 맨 마지막 word에는 
    0을 입력하고 이것이 힙의 처음과 끝임을 알 수 있게 한다.*/
    PUT(heap_listp, 0); /* Alignment padding */

    /* 첫번째 블록(1word, 4byte) 뒤에는 initial block / prologue block이 생성되고 8/1을 부여받는데, 이 블록의 Header와 Footer사이에 bp가 위치하게 된다. 
    이곳에서부터 탐색과 할당이 시작된다.
    */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp += (2*WSIZE); //header와 footer 사이에 bp 를 세팅.
    //recent_bp=heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    /* extend_heap에서 size를 alignment에 따라 조정하는데 
    2의 배수(dobule word를 만들어야 해서 2의 배수를 따짐)와 2의 배수가 아닐 때를
    따져 x WSIZE를 하기 때문에 이 곳에서 나눈 몫을 넣어 준다.*/
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    recent_bp=heap_listp;
    return 0;
}

/* Extend the heap */
/* 힙을 확장하고 확장한 부분의 힙에 free 블록을 세팅한다. 
즉, header/footer를 세팅하고 EP 블록을 세팅한다.*/
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

/////////////////////[ PLACING : 블록 조정 ]//////////////////////////////

/* place the size of block to the bp */
/* 블록의 사이즈 header와 footer에 입력한다. 
단, fit 전략을 통해 select한 블록의 크기와 현재 조정을 통해 넣을 블록의 크기를 비교하여 
2*DSIZE 크기 이상의 크기가 여유로 남을 때 남는 공간을 하나의 독립된 블록으로 세팅하고 
여유 공간이 충분히(2*DSIZE만큼) 없을 땐 그대로 조정한 사이즈만큼을 입력하여 메모리 할당을 마친다.*/
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

    recent_bp = bp;
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
        recent_bp=bp;
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);

    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    recent_bp=bp;
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