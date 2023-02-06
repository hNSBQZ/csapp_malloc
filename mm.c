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

#define WSIZE 4

#define DSIZE 8

#define CHUNKSIZE (1 << 12)

#define MAX(x,y) ((x)>(y)?(x):(y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) ((*(unsigned int *)(p)) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define SET_PRED(bp,addr) ((*(unsigned int *)(bp)) = (addr))
#define SET_SUCC(bp,addr) ((*((unsigned int *)(bp)+1))=(addr))
#define SET_HEAD(head,addr) ((*(unsigned int *)(head)) = (addr))

#define GET_PRED(bp) (*(unsigned int *)(bp))
#define GET_HEAD(head) (*(unsigned int *)(head))
#define GET_SUCC(bp) (*((unsigned int *)(bp)+1))

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

static char *heap_list;
static void *set_free_list_ptr(void *bp);
static void delete_free_list_from_head(void *bp);
static void *get_eqclass_head(size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *segregated_fit(size_t size);
static void place(void *bp,size_t size);
/*
 * mm_init - initialize the malloc package.
 */
/*
    segregated fit
    设置到从2的4次方到2的13次方10个等价类
    每个头一个字
*/
int mm_init(void)
{
    //两个序言块，十个等价类，一个起始块，一个结尾块
    if((heap_list = mem_sbrk(14*WSIZE)) == (void *)-1)
        return -1;

    heap_list+=WSIZE;
    for(int i = 0; i < 10; i++){
        PUT(heap_list + i*WSIZE, NULL);
    }               

    PUT(heap_list + (10*WSIZE), PACK(DSIZE, 1));    
    PUT(heap_list + (11*WSIZE), PACK(DSIZE, 1));     
    PUT(heap_list + (12*WSIZE), PACK(0, 1));         

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}


void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));            
    PUT(FTRP(bp), PACK(size, 0));           
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   

    //初始化空闲链表前后地址
    SET_PRED(bp,NULL);
    SET_SUCC(bp,NULL);

    return coalesce(bp);
}

void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));     
    size_t size = GET_SIZE(HDRP(bp));                      

    //从链表中删除要合并的空闲块
    delete_free_list_from_head(NEXT_BLKP(bp));
    delete_free_list_from_head(PREV_BLKP(bp));

    if(prev_alloc && next_alloc){
        return bp;
    }

    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
        PUT(HDRP(bp), PACK(size, 0));           
        PUT(FTRP(bp), PACK(size, 0));           
    }

    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); 
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                    
    }
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    //处理链表
    set_free_list_ptr(bp);

    return bp;
}

/*
    获取对应等价类空闲链表的头指针
    把条件都列出来脑子清楚点
*/
void *get_eqclass_head(size_t size)
{
    if(size==16)
        return heap_list;
    if(size>16&&size<=32)
        return heap_list+1*WSIZE;
    if(size>32&&size<=64)
        return heap_list+2*WSIZE;
    if(size>64&&size<=128)
        return heap_list+3*WSIZE;
    if(size>128&&size<=256)
        return heap_list+4*WSIZE;
    if(size>256&&size<=512)
        return heap_list+5*WSIZE;
    if(size>512&&size<=1024)
        return heap_list+6*WSIZE;
    if(size>1024&&size<=2048)
        return heap_list+7*WSIZE;
    if(size>2048&&size<=4096)
        return heap_list+8*WSIZE;
    return heap_list+9*WSIZE;
}

/*
    更新空余块的时候需要将他从空闲链表中删除
*/
void delete_free_list_from_head(void *bp)
{
    if(bp==NULL)
        return;
    //被分配了
    if(GET_ALLOC(HDRP(bp)))
        return;
    size_t size=GET_SIZE(HDRP(bp));
    void* head_ptr=get_eqclass_head(size);
    void* cur=GET_HEAD(head_ptr);
    while(cur!=NULL)
    {
        //找到了
        if(cur==bp){
            SET_SUCC(GET_PRED(bp),GET_SUCC(bp));
            return;
        }
        cur=GET_SUCC(cur);
    }
}

/*
    设置空闲块指针
*/
void *set_free_list_ptr(void *bp)
{
    //获取size
    size_t size=GET_SIZE(HDRP(bp));
    //头插法
    void* head_ptr=get_eqclass_head(size);
    SET_SUCC(bp,GET_HEAD(head_ptr));
    SET_PRED(bp,head_ptr);
    return;
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if(ptr==0)
        return;
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

void *segregated_fit(size_t size)
{
    void *bp;
    void *head_ptr=get_eqclass_head(size);
    while(head_ptr!=heap_list+10*WSIZE)
    {
        for(bp=GET_HEAD(head_ptr);bp!=NULL;bp=GET_SUCC(bp))
        {
            if(GET_SIZE(HDRP(bp))>size)
                return bp;
        }
        //下一个更大类
        head_ptr+=WSIZE;
    }
    return NULL;
}


void place(void *bp,size_t size)
{
    delete_free_list_from_head(bp);
    size_t origin_size = GET_SIZE(HDRP(bp));
    if((origin_size - size) >= 2*DSIZE) {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(origin_size - size, 0));
        PUT(FTRP(bp), PACK(origin_size - size, 0));
            //初始化空闲链表前后地址
        SET_PRED(bp,NULL);
        SET_SUCC(bp,NULL);
        coalesce(bp);
    }
    else{
        PUT(HDRP(bp), PACK(origin_size, 1));
        PUT(FTRP(bp), PACK(origin_size, 1));
    }
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
    if(size == 0)
        return NULL;
    if(size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if((bp = segregated_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr;
    size_t copy_size;

    new_ptr = mm_malloc(size);
    if (new_ptr == NULL)
      return NULL;
    copy_size = GET_SIZE(HDRP(ptr));
    if (size < copy_size)
      copy_size = size;
    memcpy(new_ptr, ptr, copy_size);
    mm_free(ptr);
    return new_ptr;
}














