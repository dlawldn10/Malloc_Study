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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
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

// 워드 사이즈
#define WSIZE 4
// 더블 워드 사이즈
#define DSIZE 8
// 초기 가용 블록과 힙 확장을 위한 기본 크기
#define CHUNKSIZE (1<<12)

// x가 크면 x리턴, t가 크면 y리턴
#define MAX(x, y) ((x)>(y) ? (x):(y))

// 크기와 할당 비트를 통합해서 헤더와 푸터에 저장할 수 있는 값을 리턴한다.
// 비트 OR 연산자 |
// 각 자리수를 비교하여 하나라도 1이 있으면 1이 된다.
#define PACK(size, alloc) ((size) | (alloc))

// 인자 p가 참조하는 워드를 읽어서 리턴한다.
#define GET(p) (*(unsigned int *)(p))
// 인자 p가 가리키는 워드에 val을 저장한다.
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 주소 p에 있는 헤더/푸터의 사이즈를 리턴한다.
#define GET_SIZE(p) (GET(p) & ~0x7)
// 주소 p에 있는 헤더/푸터의 할당 비트를 리턴한다.
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp(블록 포인터)가 주어지면
// 블록 헤더를 가리키는 포인터를 리턴한다.
#define HDRP(bp) ((char *)(bp) - WSIZE)
// 푸터를 가리키는 포인터를 리턴한다.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp) - DSIZE))

// 다음 블록의 포인터 리턴
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 이전 블록의 포인터 리턴
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


int mm_init(void);
static void *extend_heap(size_t);
void *mm_malloc(size_t);
void mm_free(void *);
void *mm_realloc(void *, size_t);


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 메모리 시스템에서 4워드를 가져와서 초기화한다.
    if ((heap_listp == mem_sbrk(4*WSIZE)) == (void *)-1) return -1;
    // alignment padding
    PUT(heap_listp, 0);
    // 프롤로그 헤더
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    // 프롤로그 푸터
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    // 에필로그 헤더
    PUT(heap_listp + (3*WSIZE), PACK(0,1));
    heap_listp += (2*WSIZE);

    // 힙을 CHUNKSIZE 바이트로 확장하고 초기 가용 블록을 생성한다.
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;

    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // size를 인접 2워드의 배수(8바이트)로 반올림하고
    // 반올림한 size의 힙 공간을 요청한다.
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    // 블록 헤더를 free한다.
    PUT(HDRP(bp), PACK(size, 0));
    // 블록 푸터를 free한다.
    PUT(FTRP(bp), PACK(size, 0));
    // 새 에필로그 헤더
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 두개의 가용 블록을 통합하기 위해 coalese함수 호출하고
    // 통합된 블록의 블록 포인터를 리턴한다.
    return coalesce(dp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    //
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc %% next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

    }
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

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
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














