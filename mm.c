
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"


// 더블워드 정렬을 수행한다.
#define ALIGNMENT 8
// size(변수)보다 크면서 가장 가까운 8(ALIGNMENT)의 배수로 만들어주는 것.
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define WSIZE 4
#define DSIZE 8

// 초기 가용 블록과 힙 확장을 위한 기본 크기
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE (1<<12)

#define LISTLIMIT 20

// x가 크면 x리턴, t가 크면 y리턴
#define MAX(x, y) ((x) > (y) ? (x) : (y)) 

// 크기와 할당 비트를 통합해서 헤더와 푸터에 저장할 수 있는 값을 리턴한다.
// 비트 OR 연산자 |
// 각 자리수를 비교하여 하나라도 1이 있으면 1이 된다.
#define PACK(size, alloc) ((size) | (alloc))

// 인자 p가 참조하는 워드를 읽어서 리턴한다.
#define GET(p) (*(unsigned int *)(p))
// 인자 p가 가리키는 워드에 val을 저장한다.
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// 주소 p에 있는 헤더/푸터의 사이즈를 리턴한다.
#define GET_SIZE(p)  (GET(p) & ~0x7)
// 주소 p에 있는 헤더/푸터의 할당 비트를 리턴한다.
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp(블록 포인터)가 주어지면
// 블록 헤더를 가리키는 포인터를 리턴한다.
#define HDRP(ptr) ((char *)(ptr) - WSIZE)
// 푸터를 가리키는 포인터를 리턴한다.
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

// 다음 블록의 포인터 리턴
// 지금 위치 + GET_SIZE(본인 헤더 -> 본인 크기)
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
// 이전 블록의 포인터 리턴
// 지금 위치 - GET_SIZE(이전 블록 풋터 -> 이전 블록 크기)
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))


team_t team = {
    "team5",
    "Jiwoo Lim",
    "dlawldn10@gmail.com",
    "",
    "",
};

void *segregated_free_lists[LISTLIMIT]; 


static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);


// size만큼 힙을 늘려준다.
static void *extend_heap(size_t size)
{
    void *ptr;
    // Adjusted size
    size_t asize;
    
    asize = ALIGN(size);
    
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    PUT(HDRP(ptr), PACK(asize, 0));  
    PUT(FTRP(ptr), PACK(asize, 0));   
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); 
    insert_node(ptr, asize);

    return coalesce(ptr);
}


// segregated_free_list에 free block을 추가한다.
static void insert_node(void *ptr, size_t size) {
    int idx = 0;
    void *search_ptr = ptr;
    void *insert_ptr = NULL;
    
    // block의 크기에 따라 들어갈 리스트를 찾는다.
    // next 포인터를 참조해야 하므로 에러를 막기 위해 LISTLIMIT - 1까지만 돈다.
    while ((idx < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        idx++;
    }
    
    // 오름차순 정렬을 유지하면서 들어갈 자리를 찾는다.
    search_ptr = segregated_free_lists[idx];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        // 다음 블록 포인터
        insert_ptr = search_ptr;
        // 이전 블록으로 이동
        search_ptr = PRED(search_ptr);
    }
    
    // pred가 있고
    if (search_ptr != NULL) {
        // next도 있을때
        // 중간에 들어가는 형태
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } 
        // next는 없을 때
        // 리스트의 마지막에 들어가는 경우
        else {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[idx] = ptr;
        }
    } 
    // pred가 없고
    else {
        // next는 있을때
        // 리스트의 맨 처음에 들어가는 경우(리스트에서 가장 작음.)
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } 
        // next도 없을 때
        // 리스트의 맨 처음에 들어가는 경우(리스트에 블록이 아무것도 없음.)
        else {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[idx] = ptr;
        }
    }
    
    return;
}


// segregated_free_list에 free block을 삭제한다.
static void delete_node(void *ptr) {
    int idx = 0;
    size_t size = GET_SIZE(HDRP(ptr));
    
    // Select segregated list 
    while ((idx < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        idx++;
    }
    
    // insert_node와 비슷하게 경우가 나누어진다.
    if (PRED(ptr) != NULL) {
        if (SUCC(ptr) != NULL) {
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        } else {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[idx] = PRED(ptr);
        }
    } else {
        if (SUCC(ptr) != NULL) {
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        } else {
            segregated_free_lists[idx] = NULL;
        }
    }
    
    return;
}


// 주변의 가용 블럭을 합쳐준다.
static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    
    if (prev_alloc && next_alloc) {                         // Case 1
        return ptr;
    }
    else if (prev_alloc && !next_alloc) {                   // Case 2
        delete_node(ptr);
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {                 // Case 3 
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    } else {                                                // Case 4
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    
    insert_node(ptr, size);
    
    return ptr;
}


// 가용 블록에 데이터를 할당해준다. 남는 부분은 분할한다.
static void *place(void *ptr, size_t asize)
{

    size_t ptr_size = GET_SIZE(HDRP(ptr));
    size_t remainder = ptr_size - asize;
    
    delete_node(ptr);

    /*
        split할 때 aszie 기준 최적은 73부터이고,  120 초과시 core dumped error 발생. 
        asize가 120이면, 
        remainder = ptr_size - 120
        ptr_size는 120이상일 것이다 (seglist에서 찾아왔으므로)
        remainder는 0이상일 것이다 
    */
    
    if (remainder <= DSIZE * 2) {
        // Do not split block 
        PUT(HDRP(ptr), PACK(ptr_size, 1)); 
        PUT(FTRP(ptr), PACK(ptr_size, 1)); 
    }
    
    else if (asize >= 120) { 

        // Split block
        PUT(HDRP(ptr), PACK(remainder, 0)); 
        PUT(FTRP(ptr), PACK(remainder, 0));

        PUT(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        insert_node(ptr, remainder);
        return NEXT_BLKP(ptr);
    }
    
    else { 
        // Split block
        PUT(HDRP(ptr), PACK(asize, 1)); 
        PUT(FTRP(ptr), PACK(asize, 1)); 
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); 
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); 
        insert_node(NEXT_BLKP(ptr), remainder);
    }
    return ptr;
}




//  힙과 segregated_free_lists을 초기화한다.
int mm_init(void)
{
    int list;         
    char *heap_start;
    
    // segregated free lists 초기화
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    // 힙 메모리 할당
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;
    
    PUT(heap_start, 0);
    PUT(heap_start + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_start + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_start + (3 * WSIZE), PACK(0, 1));
    
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
    
    return 0;
}


// size만큼 메모리를 할당한다.
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void *ptr = NULL;
    
    
    if (size == 0)
        return NULL;
    
    
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size+DSIZE);
    }
    
    int list = 0; 
    size_t searchsize = asize;
    
    while (list < LISTLIMIT) {
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            // 리스트의 맨 끝이거나, (할당받고자 하는 사이즈가 1보다 작으면서 seglist의 현재인덱스 길이 클래스의 가용리스트가 있으면)
            ptr = segregated_free_lists[list];
            // ptr에 현재 길이 클래스 가용리스트를 준다.

            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr)))))
            {
                ptr = PRED(ptr);
            }
            if (ptr != NULL)
                break;
        }
        
        // searchsize를 2로 나누어주면서 
        searchsize >>= 1;
        // searchsize가 2의 몇승인지 구해준다.
        //  ex) 2^list =  searchsize
        list++;
    }
    
    // 적당한 가용 블록이 없으면 힙을 늘려준다.
    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    
    ptr = place(ptr, asize);
    
    return ptr;
}

// 메모리를 free 시킨다.
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
 
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    // 가용블록 리스트에 추가해준다.
    insert_node(ptr, size);
    coalesce(ptr);
    
    return;
}


void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;
    size_t new_size = size;
    int remainder;
    int extendsize;
    
    
    if (size == 0)
        return NULL;
    
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }


    // 옆의 블록이 가용 블록이거나 에필로그 블록 일때
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
        remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
        // 늘리고자 하는 사이즈가 옆의 가용공간의 사이즈 보다 크다면
        if (remainder < 0) {
            // 추가 공간 필요
            extendsize = MAX(-remainder, CHUNKSIZE);
            // 힙을 늘려준다.
            if (extend_heap(extendsize) == NULL)
                return NULL;
            remainder += extendsize;
        }
        
        // 가용 리스트에서 옆의 블록을 제거해준다.
        delete_node(NEXT_BLKP(ptr));
        

        PUT(HDRP(ptr), PACK(new_size + remainder, 1));
        PUT(FTRP(ptr), PACK(new_size + remainder, 1)); 
    }
    // 다음 블록이 가용 블록이 아니라서 같은 주소에서 공간을 늘릴 수 없을 때
    else {
        // 새로운 곳에 malloc을 해주고
        new_ptr = mm_malloc(new_size - DSIZE);
        // 원래 있던 데이터를 새 주소로 옯겨준다.
        memcpy(new_ptr, ptr, size); 
        // 원래 있던 주소 공간은 free시킨다.
        mm_free(ptr);
    }

    return new_ptr;
}
