#include "mm.h"
#include "memlib.h"

int main()
{
    mem_init();
    mm_init();
    printf_head();
    
    void *ptr1=mm_malloc(500);
    printf("ptr is %x\n",ptr1);
    void *ptr2=mm_malloc(700);
    printf("ptr is %x\n",ptr1);
    void *ptr3=mm_malloc(200);
    printf("ptr is %x\n",ptr1);
    mm_free(ptr2);
    void *ptr4=mm_malloc(1200);
    void *ptr5=mm_malloc(600);
    mm_free(ptr3);
    printf_head();
    }