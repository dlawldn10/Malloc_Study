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
// size(변수)보다 크면서 가장 가까운 8(ALIGNMENT)의 배수로 만들어주는 것.
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 워드 사이즈
#define WSIZE 4
// 더블 워드 사이즈
#define DSIZE 8

#define MINIMUM 16

// 초기 가용 블록과 힙 확장을 위한 기본 크기.
// 처음 4kB 할당. 초기 free 블록
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

// explicit 방식에서 bp는 prec 의 주소를 가리키고 있다.
// bp는 이중 포인터라고 할 수 있다. 그렇기에 **로 캐스팅해줘야 한다.
// 결국엔 *(bp)인 셈으로 bp가 가리키고 있는 칸의 값이 나오게 되는데, 이 때 주소값이 나오게 된다.(prec 혹은 succ)
// prec의 주소를 반환한다.
#define PREC_FREEP(bp) (*(void**)(bp))
// succ의 주소를 반환한다.
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE))


int mm_init(void);
static void *extend_heap(size_t);
void *mm_malloc(size_t);
void mm_free(void *);
void *mm_realloc(void *, size_t);
static void *find_fit(size_t);
static void place(void *, size_t);
static void *coalesce(void *);
void putFreeBlock(void *);
void removeBlock(void *);


static char *heap_listp = NULL;
// free list의 맨 첫 블록을 가리키는 포인터
static char* free_listp = NULL;


//최초 가용 블록으로 힙 생성하기
int mm_init(void)
{
    heap_listp = mem_sbrk(4*WSIZE);
    // 메모리 시스템에서 6워드를 가져와서 초기화한다.
    if (heap_listp == (void *)-1) return -1;

    // alignment padding
    PUT(heap_listp, 0);
    // 프롤로그 헤더
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1));
    // prec
    PUT(heap_listp + (2*WSIZE), NULL);
    // succ
    PUT(heap_listp + (3*WSIZE), NULL);
    // 프롤로그 풋터
    PUT(heap_listp + (4*WSIZE), PACK(MINIMUM, 1));
    // 에필로그 헤더
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));


    free_listp = heap_listp + (2*WSIZE);


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
    size = (words % 2) ? (words+1) * WSIZE : (words) * WSIZE;
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
        putFreeBlock(bp);
        return bp;
    }
    // 이전 블록만 할당된 상태인 경우
    else if (prev_alloc && !next_alloc){
        // free 상태였던 다음 블록을 free 리스트에서 제거한다.
        removeBlock(NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // 다음 블록만 할당된 상태인 경우
    else if (!prev_alloc && next_alloc){
        // free 상태였던 다음 블록을 free 리스트에서 제거한다.
        removeBlock(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        

    }
    // 어느 블록도 할당되지 않은 경우
    else{
        // free 상태였던 다음 블록과 이전 블록을 free 리스트에서 제거한다.
        removeBlock(NEXT_BLKP(bp));
        removeBlock(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
    }

    // 연결되어진 새로운 free 블록을 free 리스트에 추가한다.
    putFreeBlock(bp);


    return bp;
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

    // size가 8보다 크다면 size에 헤더와 푸터의 공간인 8을 더한 후 그것보다 큰 8의 배수 중 최소값이 asize가 된다.
    // asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);
    // 위의 식과 효과가 같다.
    asize = ALIGN(size + SIZE_T_SIZE);

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


// first fit 방식으로 asize가 들어갈 수 있는 가용 공간을 찾는다.
static void *find_fit(size_t asize){

    void* bp;
    
    // free 리스트의 맨 마지막은 할당되어진 prologue 블록(정확히는 payload를 가리키는, free 블록이었으면 prev이었을 워드를 가리키고 있다)이다.
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    
    return NULL;

}


// 가용 블록을 allocate 처리한다.
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    // 해당 블록을 할당해야 하므로 free 리스트에서 제거한다.
    removeBlock(bp);

    // 분할이 가능한 경우
    // 할당하고 남은 메모리가 free 블록을 만들 수 있는 4개의 word가 되느냐
    // header/footer/prec/next가 필요하니 최소 4개의 word는 필요하다.
    if ((csize - asize) >= (2*DSIZE)){
        // 앞의 블록은 할당시킨다.
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // 뒤의 블록은 free시킨다.
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        // free 리스트의 첫 번째에 분할된, 즉 새롭게 수정된 free 블록이 추가된다.
        putFreeBlock(bp);
    }
    // 분할이 불가능한 경우
    // csize - asize가 2 * DSIZE보다 작다는 것은 할당되고 남은 공간에 header/footer/prec/next가 들어갈 자리가 충분치 않음을 의미한다. 
    // 최소한의 크기를 가지는 free 블록을 만들 수 없으므로 어쩔 수 없이 주소 정렬을 위해 내부 단편화를 진행한다.
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


/*
 * removeBlock - 할당되거나, 이전 혹은 다음 블록과 연결되어지는 free 블록은 free 리스트에서 제거해야 한다.
 */
void removeBlock(void *bp) {
    // free 리스트의 첫 번째 블록을 없앨 때
    if (bp == free_listp) {
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
        
    // bp가 free 리스트의 맨 처음을 가리키는 것이 아니라, free 리스트 안의 블록을 가리키고 있을 때, 해당 블록을 없앴다고 가정하고 (free 리스트 안에서) 앞 뒤의 블록을 이어주면 된다.
    } else {
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
}

/*
 * putFreeBlock - free 되거나, 연결되어 새롭게 수정된 free 블록을 free 리스트의 맨 처음에 넣는다.
 */
void putFreeBlock(void* bp) {
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(bp) = NULL;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
//  할당한 블록의 크기를 바꾼다.
void *mm_realloc(void *bp, size_t size)
{

    // 크기를 조절하고 싶은 힙의 시작 포인터
    void *oldptr = ptr;
    // 크기 조절 뒤의 새 힙의 시작 포인터
    void *newptr;
    // 복사할 힙의 크기
    size_t copySize;
    
    // place를 통해 header, footer가 배정된다.
    newptr = mm_malloc(size);
    // malloc 수행을 실패했다면
    if (newptr == NULL) {
        return NULL;
    }
    

    // 예전 size와 현재 size를 비교하여
    copySize = GET_SIZE(HDRP(oldptr));
    // 현재 바꾸고자 하는 size가 예전 사이즈보다 작다면
    if (size < copySize) {    
        // 추후 메모리를 이만큼만 복사해 갈 것이기 때문에 copySize size로 갱신한다.
        copySize = size;
    }
    // 원래 있던 메모리를 복사하여 새로운 곳에 할당한다.
    memcpy(newptr, oldptr, copySize);
    // 원래 있던 메모리를 free해준다.
    mm_free(oldptr); 

    return newptr;

}














