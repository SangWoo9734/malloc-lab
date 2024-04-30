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

/*
* Basic constants and macros
*/
#define WSIZE     4 // 워드, 헤더(Header), 풋터(Footer) 크기 (bytes)
#define DSIZE     8 // 더블 워드 크기 (bytes)
#define CHUNKSIZE (1 << 12) // 힙 확장 크기 (bytes)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc)) // 메모리 사이즈 정보, 할당 여부를 기록

#define GET(p)        (*(unsigned int *)(p))
#define PUT(p, value) (*(unsigned int *)(p) = (value))

#define GET_SIZE(p)  (GET(p) & ~0x7) // SIZE 영역의 정보만 가져오기
#define GET_ALLOC(p) (GET(p) & 0x1) // ALLOCATED 영역 정보만 가져오기

#define HDRP(bp) ((char *)(bp) - WSIZE) // Header Pointer의 위치 구하기
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // Footer Pointer의 위치 구하기

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 이전 블록 포인터의 위치
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 다음 블록 포인터의 위치

/*
* Function and Variable Declaration
*/
static char *heap_listp; // 항상 프롤로그 블록을 가리키는 블록 포인터.

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);



/*
* coalesce : 메모리 해제시 이전, 다음 블록의 가용 상태를 확인하여 가용 상태인 블록을 서로 연결한다.
*/
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if ( prev_alloc && next_alloc ) { // CASE 1 - 이전 블록과 다음 블록이 모두 할당되어 있는 경우, 현재 블록만 가용 상태로 변경
        return bp; // 현재 블록은 mm_free()에서 가용 상태로 변하기 때문에 bp의 위치만 반환
    }

    else if ( prev_alloc && !next_alloc ) { // CASE 2 - 이전 블록은 할당되어 있고, 다음 블록은 할당되지 않은 상태.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 크기만큼 블록의 크기를 늘려주기
        PUT(HDRP(bp), PACK(size, 0)); // 기존 헤더에 변경된 사이즈로 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 기존 푸터에 변경된 사이즈로 갱신
    }
    
    else if ( !prev_alloc && next_alloc ) { // CASE 3 - 다음 블록은 할당되어 있고, 이전 블록은 할당되지 않은 상태.
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 헤더를 통해 이전 블록의 사이즈만큼 크기를 늘려주기
        PUT(FTRP(bp), PACK(size, 0)); // 기존의 푸터에 변경하려는 크기로 변경.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더로 이동, 변경된 크기만큼 할당하여 헤더 갱신.
        bp = PREV_BLKP(bp); // 합쳐진 가용블록의 헤더는 합치기 전의 이전 블록의 헤더가 되기 때문에 헤더 갱신.
    }

    else { // CASE 4 - 이전, 다음 블록 모두 가용상태.
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록, 다음 블록의 사이즈만큼 기존 사이즈 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더에 새로운 사이즈로 갱신
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록의 푸터에 새로운 사이즈로 갱신
        bp = PREV_BLKP(bp); // 합쳐진 가용블록의 헤더 위치(이전 블록의 헤더 위치)로 포인터 이동.
    }



    return bp;
}

/*
* extend_heap : 새로운 가용 블록으로 힙 확장.
*/
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE  : words * WSIZE; // 데이터 사이즈에 따른 워드 사이즈 계산 및 부족한 워드 추가하기

    if ( (long)(bp = mem_sbrk(size)) == -1 ) { // block pointer를 확장된 영역으로 이동, 이동할 수 없다면 NULL을 반환
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0)); // block header 할당 해제
    PUT(FTRP(bp), PACK(size, 0)); // block footer 할당 해제
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // Epilogue header 할당 해제

    return coalesce(bp); // 메모리 헤제 후 가용 블록과 연결 
}


/*
* find_fit : 요청한 메모리가 들어갈 수 있는 가용 블록을 찾음. 
*/
static void *find_fit(size_t asize)
{
    void *bp;

    // First-Fit search --> 53점 / 100
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { // 프롤로그 블록(heap_listp)부터 가용 블록을 탐색
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) { // 메모리 요청보다 큰 가용 블록이 나오면 해당 블록의 블록 포인터를 반환.
            return bp;
        }
    }


    // No fit.
    return NULL;
}

/*
* extend_heap : 
*/
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록 포인터가 가리키고 있는 블록의 크기를 

    // 내부 단편화가 발생하는지 확인
    if ((csize - asize) >= (2 * DSIZE)) { // 가용 블록의 크기가 2 더블 워드 블록보다 크다면(그대로 넣으면 내부 단편화 발생)
        PUT(HDRP(bp), PACK(asize, 1)); // 가용블록에 요청받은 메모리 만큼 패킹해준 후,
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0 )); /// 가용 블록의 남은 메모리를 새로운 가용 블록으로 분리해준다.
        PUT(FTRP(bp), PACK(csize-asize, 0 ));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1)); // 내부단편화가 발생하지 않는다면 메모리 크기대로 메모리를 패킹
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{   
    heap_listp = mem_sbrk(4 * WSIZE); // 힙 생성을 위한 가용 블록 추가
    if ( heap_listp == (void *)-1 ) return -1;

    PUT(heap_listp, 0); // 정렬 padding block
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // prologue header block 설정
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue footer block 설정
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // Epilogue block
    heap_listp += 2 * WSIZE; // heap_listp를 prologue block의 header로 이동

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) // 초기에 extend_heap을 통해 heap의 크기를 늘림. 늘릴 수 없다면, 함수 종료.
        return -1;

    return 0;
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

    if (size == 0) // 사이즈가 없는 경우 예외처리
        return NULL;

    if (size <= DSIZE) { // 전달 받은 크기가 워드 크기보다 작거나 같을 때,
        asize = 2 * DSIZE; // 2워드만큼 할당 받을 수 있도록 설정
    }
    else { // " 워드 크기보다 클 때,
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE); // 블록의 크기가 2워드(8바이트)의 배수가 되도록 크기 조정
    }

    if ((bp = find_fit(asize)) != NULL) { // 블록을 삽입할 수 있는 위치를 탐색
        place(bp, asize); // 위치를 발견했다면 해당 위치에 블록을 삽입
        return bp; // 블록의 위치 반환
    }
    
    // 적절한 위치를 발견하지 못한 경우
    extendsize = MAX(asize , CHUNKSIZE); // TODO: 모르겠어유
    if ( (bp = extend_heap(extendsize/WSIZE)) == NULL ) {
        return NULL;
    }
    place(bp, asize);
    return bp;

}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0)); // 블록의 헤더 메모리 해제
    PUT(FTRP(ptr), PACK(size, 0)); // 블록의 푸터 메모리 해제
    coalesce(ptr); // 가용 블록 연결
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr;
    size_t copySize;

    if (size <= 0) { // 예외처리: 요청 사이즈가 0보다 작은 경우 반환
        mm_free(bp);
        return 0;
    }

    if (bp == NULL) {
        return mm_malloc(size); // 예외처리 : 위치 값이 없는 경우 새롭게 사이즈 만큼 생성후 반환 ( 위치 값은 시작 값이 됨. )
    }
    
    newptr = mm_malloc(size);

    if (newptr == NULL) // 메모리를 할당 받을 수 없다면 함수 종료.
      return NULL;

    copySize = GET_SIZE(HDRP(bp)); // 카피할 블록의 크기 값


    if (size < copySize) // 만약 새로운 크기가 이전 블록의 크기보다 작은 경우 크기를 제한
      copySize = size;
    
    memcpy(newptr, oldptr, copySize); // newptr에 oldptr의 메모리를 copySize 만큼 복사
    mm_free(oldptr); // 복사에 사용된 블록 메모리 삭제
    return newptr;
}
