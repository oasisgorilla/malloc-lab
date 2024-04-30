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
    "Yongjae is badboy",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

///////////////////////////////////새로 추가된 매크로//////////////////////////////////
/* Basic constants and macros*/
#define WSIZE 4             // 기본 워드사이즈(4byte)
#define DSIZE 8             // 더불 워드 사이즈(8byte)
#define CHUNKSIZE (1 << 12) // 확장 바이트(4096byte)

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 최댓값 구하는 매크로

#define PACK(size, alloc) ((size) | (alloc)) // (사이즈 | 할당여부 비트) 세트 반환 매크로

// unsigned int는 4byte 부호없는 정수
#define GET(p) (*(unsigned int *)(p))              // p주소에 저장된 값 가져오기
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p주소에 값 넣기

// #define GET_SIZE(p) (GET(p) & ~0x7) // p주소의 payload 사이즈 가져오기
#define GET_SIZE(p) ((GET(p) >> 1) << 1) // p주소의 사이즈 가져오기(더블워드)
#define GET_ALLOC(p) (GET(p) & 0x1)      // 할당여부 가져오기

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)                        // 특정 블록주소 bp의 헤더 주소 가져오기
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 특정 블록주소 bp의 푸터 주소 가져오기

/* Given block ptr bp, compute address of next and previous blocks */
// 시작주소는 헤더 다음 블록의 시작주소이다.
#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE))) // 다음블록의 시작 주소 가져오기
#define PREV_BLKP(bp) (((char *)(bp)-GET_SIZE((char *)(bp)-DSIZE)))   // 이전 블록의 시작주소 가져오기

static void *heap_listp; // heap을 증가시키고 증가시킨부분의 시작 주소 반환받을 곳
static void *extend_heap(size_t words);
static void *coalesce(void *ptr);
static void *find_fit(size_t asize);
static void place(void *ptr, size_t asize);
static char *last_allocated; // next fit 사용시
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    { // 16byte요청
        return -1;
    }
    // 824.p 9.42 구조 만들기
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header*/
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
// void *mm_malloc(size_t size)
// {
//     int newsize = ALIGN(size + SIZE_T_SIZE);
//     void *p = mem_sbrk(newsize);
//     if (p == (void *)-1)
//     {
//         return NULL;
//     }
//     else
//     {
//         *(size_t *)p = size;
//         return (void *)((char *)p + SIZE_T_SIZE);
//     }
// }

// 메모리영역에 블록을 배치하는 함수
static void place(void *ptr, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(ptr));

    // 블록 내의 할당 부분을 제외한 나머지 공간의 크기가 16byte(DSIZE * 2) 이상이라면, 해당 블록의 공간을 분할
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        ptr = NEXT_BLKP(ptr);
        PUT(HDRP(ptr), PACK(csize - asize, 0));
        PUT(FTRP(ptr), PACK(csize - asize, 0));
    }
    else // 아닐 경우 분할하지 않음
    {
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
    }
}

// first fit/next fit
static void *find_fit(size_t asize)
{
    void *bp;
    // first fit
    // 에필로그 헤더(힙의 끝) 까지 탐색한다
    // for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    // {
    //     // 가용 가능하고 여유공간이 있다는 조건
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
    //     {
    //         return bp;
    //     }
    // }

    // next fit
    if (last_allocated == NULL)
    {
        last_allocated = heap_listp;
    }

    for (bp = last_allocated; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    { // 마지막으로 할당한 bp 부터 할당된 공간이 없을 때 까지 탐색
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {                        // 할당되지 않고, 적당한 공간을 만나면
            last_allocated = bp; // last_allocated 갱신 후
            return bp;           // bp 반환
        }
    }

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0 && last_allocated > bp; bp = NEXT_BLKP(bp))
    { // heap_listp도 last_allocated까지 이동시켜준다.
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            last_allocated = bp;
            return bp;
        }
    }

    return NULL;
}

// 매크로 활용한 malloc
void *mm_malloc(size_t size)
{
    size_t asize;      // 할당받을 크기
    size_t extendsize; // extend_heap으로 넘길 변수
    char *bp;
    // 빈 size일 경우 return
    if (size == 0)
    {
        return NULL;
    }

    // 블록크기 정하기
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE; // 헤더 4byte, 푸터 4byte + payload 8byte
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // 가용 블록을 가용 리스트에서 검색(find_fit), 할당기(place)는 요청 블록을 배치
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    // 리스트에 들어갈 수 있는 free 리스트가 없을 경우, 메모리를 확장하고 블록을 배치한다.
    extendsize = MAX(asize, CHUNKSIZE); // 기본 확장사이즈보다 클 경우 그만큼 요청
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);

    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;

//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//         return NULL;
//     copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     if (size < copySize)
//         copySize = size;
//     memcpy(newptr, oldptr, copySize);
//     mm_free(oldptr);
//     return newptr;
// }

/////////////////////////realloc//////////////////////////////////
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
    { // 받은 주소가 비어있으면 새로 할당한다.
        return mm_malloc(size);
    }

    if (size == 0)
    {
        mm_free(ptr);
        return 0;
    }

    void *new_ptr = mm_malloc(size);
    if (new_ptr == NULL)
    {
        return NULL;
    }
    size_t csize = GET_SIZE(HDRP(ptr));
    if (size < csize)
    {                 // 기존 블록의 크기가 더 클 경우
        csize = size; // 기존 블록의 크기를 요청받은 크기만큼으로 줄인다.
    }
    memcpy(new_ptr, ptr, csize); // ptr 위치에서 csize만큼의 크기를 new_ptr의 위치에 복사
    mm_free(ptr);                // 기존 ptr은 할당 해제
    return new_ptr;
}

/////////////////////////coalesce/////////////////////////////////
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {                        /*Case 1*/
        last_allocated = bp; // next_fit 사용시
        return bp;
    }

    else if (prev_alloc && !next_alloc)
    { /*Case 2*/
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    { /*Case 3*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else
    { /*Case 4*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    last_allocated = bp;

    return bp; // 합친 블록 포인터 반환
}

/////////////////////////extend_heap//////////////////////////////
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 홀수면 + 1워드 요청, 짝수면 알맞게 요청
    if ((long)(bp = mem_sbrk(size)) == -1)                    // 위에서 결정한 사이즈의 힙 요청
    {
        return NULL;
    }

    // 헤더, 푸터, 에필로그 초기화
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue  header */

    /* Coalesce if the previous block was free */
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
