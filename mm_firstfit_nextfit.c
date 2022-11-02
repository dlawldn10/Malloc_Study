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
    "team5",
    "Jiwoo Lim",
    "dlawldn10@gmail.com",
    "",
    "",
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// size(변수)보다 크면서 가장 가까운 8(ALIGNMENT)의 배수로 만들어주는 것.
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))


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
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음 블록의 포인터 리턴
// 지금 위치 + GET_SIZE(본인 헤더 -> 본인 크기)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 이전 블록의 포인터 리턴
// 지금 위치 - GET_SIZE(이전 블록 풋터 -> 이전 블록 크기)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


int mm_init(void);
static void *extend_heap(size_t);
void *mm_malloc(size_t);
void mm_free(void *);
void *mm_realloc(void *, size_t);
static void *find_fit(size_t);
static void place(void *, size_t);
static void *coalesce(void *);

// next fit 으로 돌리고 싶을때 주석 해제.
#define NEXT_FIT

static char *heap_listp = NULL;


// #ifdef ~ #endif를 통해 조건부로 컴파일이 가능하다. NEXT_FIT이 선언되어 있다면 밑의 변수를 컴파일 할 것이다.
#ifdef NEXT_FIT
    // next_fit 사용 시 마지막으로 탐색한 free 블록을 가리키는 포인터이다.
    static void* last_freep;
#endif

//최초 가용 블록으로 힙 생성하기
int mm_init(void)
{
    heap_listp = mem_sbrk(4*WSIZE);
    // 메모리 시스템에서 4워드를 가져와서 초기화한다.
    if (heap_listp == (void *)-1) return -1;
    // alignment padding
    PUT(heap_listp, 0);
    // 프롤로그 헤더
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    // 프롤로그 푸터
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    // 에필로그 헤더
    PUT(heap_listp + (3*WSIZE), PACK(0,1));

    heap_listp += (2*WSIZE);

    #ifdef NEXT_FIT
        last_freep = heap_listp;                                            // next_fit 사용 시 마지막으로 탐색한 free 블록을 가리키는 포인터이다.
    #endif

    // 힙을 CHUNKSIZE 바이트로 확장하고 초기 가용 블록을 생성한다.
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;

    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // 8의 배수로 만들기
    // size를 인접 2워드의 배수(8바이트)로 반올림하고
    // 반올림한 size의 힙 공간을 요청한다.
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    // 블록 헤더를 설정한다.
    PUT(HDRP(bp), PACK(size, 0));
    // 블록 푸터를 설정한다.
    PUT(FTRP(bp), PACK(size, 0));
    // 새 에필로그 헤더
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 두개의 가용 블록을 통합하기 위해 coalese함수 호출하고
    // 통합된 블록의 블록 포인터를 리턴한다.
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{

    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) return NULL;

    // 최소 사이즈(2*DSIZE)보다 작으면 안되므로 최소 사이즈로 설정해준다.
    if (size <= DSIZE) asize = 2*DSIZE;
    // size가 8보다 크다면 size에 헤더와 푸터의 공간인 8을 더한 후 그것보다 큰 8의 배수 중 최소값이 asize가 된다.
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);

    // asize가 들어갈 수 있는 가용 공간을 찾았다면
    if ((bp = find_fit(asize)) != NULL){
        // 그 자리에 할당한다.
        place(bp, asize);
        return bp;
    }

    // 가용 공간이 없다면 extendsize만큼 extend_heap을 하고, 늘어난 그 힙에 place한다.
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

// 인접한 가용 블럭을 합친다.
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // 이전 블록과 다음 블록 모두 할당된 상태인 경우
    if (prev_alloc && next_alloc){
        return bp;
    }
    // 이전 블록만 할당된 상태인 경우
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // 다음 블록만 할당된 상태인 경우
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

    }
    // 어느 블록도 할당되지 않은 경우
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    #ifdef NEXT_FIT
        last_freep = bp;
    #endif


    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
//  할당한 블록의 크기를 바꾼다.
void *mm_realloc(void *bp, size_t size)
{
    // size가 0보다 작으면 free 시킨다.
    if(size <= 0){
        mm_free(bp);
        return 0;
    }

    // bp가 NULL이라면 그만큼 malloc
    if(bp == NULL){
        return mm_malloc(size);
    }

    // size만큼 malloc을 수행한 주소값.
    void *newp = mm_malloc(size);
    // malloc 수행을 실패했다면
    if(newp == NULL){
        return 0;
    }

    // 예전 size와 현재 size를 비교하여
    size_t oldsize = GET_SIZE(HDRP(bp));
    // 현재 바꾸고자 하는 size가 예전 사이즈보다 작다면
    if(size < oldsize){
        // 추후 메모리를 이만큼만 복사해 갈 것이기 때문에 oldsize를 size로 갱신한다.
        oldsize = size;
    }
    // 원래 있던 메모리를 복사하여 새로운 곳에 할당한다.
    memcpy(newp, bp, oldsize);
    // 원래 있던 메모리를 free해준다.
    mm_free(bp);

    // 새로 할당된 주소값을 리턴한다.
    return newp;
}

// first fit 방식으로 asize가 들어갈 수 있는 가용 공간을 찾는다.
static void *find_fit(size_t asize){

    #ifdef NEXT_FIT
        void* bp;
        void* old_last_freep = last_freep;
        
        // 이전 탐색이 종료된 시점에서부터 다시 시작한다.
        for (bp = last_freep; GET_SIZE(HDRP(bp)); bp = NEXT_BLKP(bp)) {     
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
        }
        
        // last_freep부터 찾았는데도 없으면 처음부터 찾아본다. 이 구문이 없으면 앞에 free 블록이 있음에도 extend_heap을 하게 되니 메모리 낭비가 된다.
        for (bp = heap_listp; bp < old_last_freep; bp = NEXT_BLKP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
        }
        
        // 탐색을 마쳤으니 last_freep도 수정해준다.
        last_freep = bp;
        
        return NULL;       

    #else
        void *bp;

        // 힙에서 ; 블록 헤더의 사이즈가 양수인 동안 ; 다음 블록으로 이동한다.
        for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
            // 아직 할당되지 않았고 && 공간이 넉넉한 곳을 찾았다면
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
                // 그곳의 주소를 리턴한다.
                return bp;
            }
        }
        return NULL;

    #endif

}

// 가용 블록을 allocate 처리한다.
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}














