/* Shubhit Mohan Singh (shubhits)
 * mm.c
 *
 * This is a dynamic memory allocator implemented using the following 
 * techniques:
 * 1) Data Structure: Segregated Free Lists
 * 2) Insertion policy: Last in, first out (LIFO)
 * 3) Finding method: Combination of first fit and best fit
 * 4) Coalescing is done at every call to free.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE  (672)  /* initial heap size (bytes) 128=88%, 672=512=256=91%, 848=1024=90%*/
#define H_SIZE 4 //Header size
#define F_SIZE 4 //Footer size
#define FREE_PTR_SIZE 8 //Pointer size
 /* Overhead of each free block: header + footer + free list pointers */
#define OVERHEAD ((H_SIZE) + (F_SIZE) + (FREE_PTR_SIZE) + (FREE_PTR_SIZE)) 
#define ALLOC_OVERHEAD ((H_SIZE) + (F_SIZE)) //overhead of allocated block

#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/* Double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET4(p) (*(unsigned int *)(p))
#define PUT4(p, val) (*((unsigned int *)(p)) = (val))
/* Read and write a double word at address p */
#define GET(p) (*(unsigned long int *)(p))
#define PUT(p, val) (*((unsigned long int *)(p)) = (val))
/* Writing pointers into a double word */
#define PUTP(p, val) (*((unsigned long int *)(p)) = (unsigned long int)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET4(p) & ~0x7)
#define GET_ALLOC(p) (GET4(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((void *)(bp) - WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(((void *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE(((void *)(bp) - DSIZE)))

/* Given a block pointer, compute the pointer 
to the address of the next free block*/
#define PREV_FREE(bp) ((void *)(bp))
#define NEXT_FREE(bp) ((void *)(bp) + FREE_PTR_SIZE)

/* Given the pointer to the address of a free block, compute the
address of the free block.*/
#define GET_FREE(p) (void *)(*(unsigned long int *)(p))

//Offsets of the start of each linked list from seg_start.
#define SEG1     0
#define SEG2     8
#define SEG3     16
#define SEG4     24
#define SEG5     32
#define SEG6     40
#define SEG7     48
#define SEG8     56
#define SEG9     64
#define SEG10    72
#define SEG11    80
#define SEG12    88
#define SEG13    96
#define SEG14    104

/* Max size of free blocks in each list */
#define MAX1      24
#define MAX2      48
#define MAX3      72
#define MAX4      96
#define MAX5      120
#define MAX6      480
#define MAX7      960
#define MAX8      1920
#define MAX9      3840
#define MAX10     7680
#define MAX11     15360
#define MAX12     30720
#define MAX13     61440
//NOTE: seglist 14 has no upper limit. 
#define NUM_SEGS    14 //Number of seg lists

/* Global variables and Constants */
/* Pointer to the first block */
static void *heap_listp; 
static void *seg_start;


/*
 * Internal Helper Functions.
 */

/*
 * Given a pointer to a free block in the free list, splice the block
 * from the free list and return a pointer to that block.
 */
static void *splice_block(void *bp) {
    /* Get prev and next free blocks of the free list. */
    void *prev_free = GET_FREE(PREV_FREE(bp));
    void *succ_free = GET_FREE(NEXT_FREE(bp));
    size_t size = GET_SIZE(HDRP(bp));
    /* Case 1: bp is the first block in the free list of more than 1 element.
    make the seg list header point to the next free block.*/
    if ((prev_free == NULL) && (succ_free != NULL)) {
        if (size <= MAX1) PUTP(seg_start + SEG1, succ_free);
        else if (size <= MAX2) PUTP(seg_start + SEG2, succ_free);
        else if (size <= MAX3) PUTP(seg_start + SEG3, succ_free);
        else if (size <= MAX4) PUTP(seg_start + SEG4, succ_free);
        else if (size <= MAX5) PUTP(seg_start + SEG5, succ_free);
        else if (size <= MAX6) PUTP(seg_start + SEG6, succ_free);
        else if (size <= MAX7) PUTP(seg_start + SEG7, succ_free);
        else if (size <= MAX8) PUTP(seg_start + SEG8, succ_free);
        else if (size <= MAX9) PUTP(seg_start + SEG9, succ_free);
        else if (size <= MAX10) PUTP(seg_start + SEG10, succ_free);
        else if (size <= MAX11) PUTP(seg_start + SEG11, succ_free);
        else if (size <= MAX12) PUTP(seg_start + SEG12, succ_free);
        else if (size <= MAX13) PUTP(seg_start + SEG13, succ_free);
        else PUTP(seg_start + SEG14, succ_free);

        /* Update the new front's prev pointer to null. */
        PUTP(PREV_FREE(succ_free), 0);
    }
    /* Case 2: bp is the last block in the free list of more than 1 element.
    Simply update the next pointer of the prev free block.*/
    else if ((prev_free != NULL) && (succ_free == NULL)) {
        PUTP(NEXT_FREE(prev_free), 0);
    }
    /* Case 3: bp is the only block in the free list. Make the free list header
    point to NULL. */
    else if ((prev_free == NULL) && (succ_free == NULL)) {
        if (size <= MAX1) PUTP(seg_start + SEG1, 0);
        else if (size <= MAX2) PUTP(seg_start + SEG2, 0);
        else if (size <= MAX3) PUTP(seg_start + SEG3, 0);
        else if (size <= MAX4) PUTP(seg_start + SEG4, 0);
        else if (size <= MAX5) PUTP(seg_start + SEG5, 0);
        else if (size <= MAX6) PUTP(seg_start + SEG6, 0);
        else if (size <= MAX7) PUTP(seg_start + SEG7, 0);
        else if (size <= MAX8) PUTP(seg_start + SEG8, 0);
        else if (size <= MAX9) PUTP(seg_start + SEG9, 0);
        else if (size <= MAX10) PUTP(seg_start + SEG10, 0);
        else if (size <= MAX11) PUTP(seg_start + SEG11, 0);
        else if (size <= MAX12) PUTP(seg_start + SEG12, 0);
        else if (size <= MAX13) PUTP(seg_start + SEG13, 0);
        else PUTP(seg_start + SEG14, 0);
    }
    /* Case 4: bp is somewhere in the middle of a free list
    with more than 2 elements. update next and prev pointers. */
    else {
        PUTP(NEXT_FREE(prev_free), succ_free);
        PUTP(PREV_FREE(succ_free), prev_free);
    }
    return bp;
}



/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    void *ptr;

    /* Case 1: Both prev and next blocks are allocated. So simply return
    the freed block. */
    if (prev_alloc && next_alloc) {            
        return bp;
    }
    /* Case 2: Prev block is allocated but the next block is free.
    Splice the next block from free list, coalesce with current block,
    and return. */
    else if (prev_alloc && !next_alloc) {      
        /* Splice next block from free list*/
        splice_block(NEXT_BLKP(bp));
        /* Fix header and footer, i.e. coalesce current and next blocks.*/
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT4(HDRP(bp), PACK(size, 0));
        PUT4(FTRP(bp), PACK(size, 0));
        return(bp);
    }
    /* Case 3: Next block is allocated but the prev block is free.
    Splice the prev block from free list, coalesce with current block,
    and return. */
    else if (!prev_alloc && next_alloc) {
        /* Splice previous block from free list*/
        ptr = splice_block(PREV_BLKP(bp));
        /* Fix header and footer, i.e. coalesce current and prev blocks.*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT4(FTRP(bp), PACK(size, 0));
        PUT4(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        return ptr;
    }

    /* Case 4: Both the prev and next blocks are free.
    Splice the next and prev blocks from free list, coalesce with 
    current block, and return. */
    else {
        /* Splice previous block from free list*/
        ptr = splice_block(PREV_BLKP(bp));
        /* Splice next block from free list*/
        splice_block(NEXT_BLKP(bp));
        /* Fix header and footer, i.e. coalesce blocks.*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT4(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT4(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        return ptr;
    }
}

/* 
 * seglist_insert - Insert a newly created free block, with appropriate header 
 * and footer, into the beginning of the free list.
 */
static void *seglist_insert(void *bp, void *flist_root, void *root_loc) {
    PUTP(root_loc, bp);
    PUTP(PREV_FREE(bp), 0);
    if (flist_root == NULL) { //then bp is the first free block
        PUTP(NEXT_FREE(bp), 0);
        return bp;
    }
    PUTP(NEXT_FREE(bp), flist_root);
    PUTP(PREV_FREE(flist_root), bp);
    return bp;
}

/* 
 * seglist_insert - Determine which seg list a newly created free block should
 * go into, based on its size. Then call seglist_insert().
 */
static void *flist_insert(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    void *flist_root; //address of seg list pointer.
    void *root_loc; //address of address of seg list pointer.
    if (size <= MAX1) {
        root_loc = seg_start + SEG1;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX2) {
        root_loc = seg_start + SEG2;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX3) {
        root_loc = seg_start + SEG3;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX4) {
        root_loc = seg_start + SEG4;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX5) {
        root_loc = seg_start + SEG5;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX6) {
        root_loc = seg_start + SEG6;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX7) {
        root_loc = seg_start + SEG7;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX8) {
        root_loc = seg_start + SEG8;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX9) {
        root_loc = seg_start + SEG9;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX10) {
        root_loc = seg_start + SEG10;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX11) {
        root_loc = seg_start + SEG11;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX12) {
        root_loc = seg_start + SEG12;
        flist_root = (void *)GET(root_loc);
    }
    else if (size <= MAX13) {
        root_loc = seg_start + SEG13;
        flist_root = (void *)GET(root_loc);
    }
    else {
        root_loc = seg_start + SEG14;
        flist_root = (void *)GET(root_loc);
    }
    //Now that we have the correct, flist_root and root_loc, 
    //call seglist_insert.
    return seglist_insert(bp, flist_root, root_loc);
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    void *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) < 0) 
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT4(HDRP(bp), PACK(size, 0)); /* free block header, which 
    was the old epilogue header */
    PUT4(FTRP(bp), PACK(size, 0)); /* free block footer */
    PUT4(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free, and insert in the seg
    list. */
    return flist_insert(coalesce(bp));
}




/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   
    splice_block(bp); //remove block from seg list
    //If there is enough remaining space, create a free block,
    //coalesce it and insert it into the seg list.
    if ((csize - asize) >= (OVERHEAD)) { 
        PUT4(HDRP(bp), PACK(asize, 1));
        PUT4(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT4(HDRP(bp), PACK(csize-asize, 0));
        PUT4(FTRP(bp), PACK(csize-asize, 0));
        flist_insert(coalesce(bp));
    }
    //If there is not enough remaining space, simply allocate csize 
    //bytes as the allocated block.
    else { 
        PUT4(HDRP(bp), PACK(csize, 1));
        PUT4(FTRP(bp), PACK(csize, 1));
        
    }
}

/* 
 * find - Given an index i to a specific seg list and asize, 
 * find a block of at least asize bytes in the seg list.
 */
static void* find(size_t i, size_t asize) {
    void *this = NULL; //pointer to seg free list
    void *best_bp;
    size_t size;
    long best_diff = -1;
    long this_diff;
    int counter = 0;
    /* Determine which list to search in based on i*/
    switch (i) {
        case 1: 
            this = GET_FREE(seg_start + SEG1);
            break;
        case 2:
            this = GET_FREE(seg_start + SEG2);
            break;
        case 3:
            this = GET_FREE(seg_start + SEG3);
            break;
        case 4:
            this = GET_FREE(seg_start + SEG4);
            break;
        case 5:
            this = GET_FREE(seg_start + SEG5);
            break;
        case 6:
            this = GET_FREE(seg_start + SEG6);
            break;
        case 7:
            this = GET_FREE(seg_start + SEG7);
            break;
        case 8:
            this = GET_FREE(seg_start + SEG8);
            break;
        case 9:
            this = GET_FREE(seg_start + SEG9);
            break;
        case 10:
            this = GET_FREE(seg_start + SEG10);
            break;
        case 11:
            this = GET_FREE(seg_start + SEG11);
            break;
        case 12:
            this = GET_FREE(seg_start + SEG12);
            break;
        case 13:
            this = GET_FREE(seg_start + SEG13);
            break;
        case 14:
            this = GET_FREE(seg_start + SEG14);
            break;
    }
    best_bp = this;
    /*Combination of best fit and first fit. The function starts searching
    form the beginning of the seg list, but does not return the first free 
    block it finds. It searches through 9 consecutive free blocks and returns
    the block that fits best with the given size, i.e., results in the least
    wastage of space. The number 9 was chosen as it was found to have the right
    balance between throughput and utilization.*/
    while (this != NULL) {
        if (counter >= 9) return best_bp;
        size = GET_SIZE(HDRP(this));
        if (asize <= size) {
            counter++;
            this_diff = size - asize;
            if ((this_diff < best_diff) || (best_diff == -1)) {
                best_diff = this_diff;
                best_bp = this;
            }
        }
        this = GET_FREE(NEXT_FREE(this));
    }
    if (best_diff == -1) return NULL; //no block was found
    else return best_bp;
}

/* 
 * find_fit - Find a fit for a block with asize bytes by 
 * traversing the seg list, calling find().
 */
static void *find_fit(size_t asize)
{
    size_t i;
    void *bp = NULL;
    //Determine which seg list to look in.
    if (asize <= MAX1) {
        for (i = 1; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX2) {
        for (i = 2; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX3) {
        for (i = 3; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX4) {
        for (i = 4; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX5) {
        for (i = 5; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX6) {
        for (i = 6; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX7) {
        for (i = 7; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX8) {
        for (i = 8; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX9) {
        for (i = 9; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX10) {
        for (i = 10; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX11) {
        for (i = 11; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX12) {
        for (i = 12; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else if (asize <= MAX13) {
        for (i = 13; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    } else {
        for (i = 14; i < NUM_SEGS + 1; i++) {
            if ((bp = find(i, asize)) != NULL) return bp;
        }
    }
    return bp;
}


/* 
 * printblock - Helper function for checkheap() that prints each block.
 */
static void printblock(void *bp, int free) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }
    if (!free) {
        printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
            (int)hsize, (halloc ? 'a' : 'f'), 
            (int)fsize, (falloc ? 'a' : 'f')); 
    } else {
        printf("%p: header: [%d:%c]; prev: [%p]; next: [%p]; \
            footer: [%d:%c]\n", bp, 
            (int)hsize, (halloc ? 'a' : 'f'), 
            GET_FREE(PREV_FREE(bp)), GET_FREE(NEXT_FREE(bp)),
            (int)fsize, (falloc ? 'a' : 'f')); 
    }
    
}

/* 
 * checkblock - Checks that the header matches the footer of a block
 * and that the block is aligned to ALIGNMENT.
 */
static void checkblock(void *bp) 
{
    //check alignment
    if ((size_t)bp % ALIGNMENT)
        printf("Error: %p is not doubleword aligned\n", bp);
    //check that header == footer
    if (GET4(HDRP(bp)) != GET4(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/* 
 * print_free_list - Helper function for checkheap() that prints
 * each seg free list so it is easier to view what the heap looks like.
 */
static void print_free_list(int offset, int verbose) {
    void *ptr;
    size_t min, max;
    size_t size;
    size_t s;
    int num = 1 + offset/FREE_PTR_SIZE;
    switch (num) {
        case 1: 
            min = 0;
            max = MAX1;
            s = SEG1;
            break;
        case 2:
            min = MAX1;
            max = MAX2;
            s = SEG2;
            break;
        case 3:
            min = MAX2;
            max = MAX3;
            s = SEG3;
            break;
        case 4:
            min = MAX3;
            max = MAX4;
            s = SEG4;
            break;
        case 5:
            min = MAX4;
            max = MAX5;
            s = SEG5;
            break;
        case 6:
            min = MAX5;
            max = MAX6;
            s = SEG6;
            break;
        case 7:
            min = MAX6;
            max = MAX7;
            s = SEG7;
            break;
        case 8:
            min = MAX7;
            max = MAX8;
            s = SEG8;
            break;
        case 9:
            min = MAX8;
            max = MAX9;
            s = SEG9;
            break;
        case 10:
            min = MAX9;
            max = MAX10;
            s = SEG10;
            break;
        case 11:
            min = MAX10;
            max = MAX11;
            s = SEG11;
            break;
        case 12:
            min = MAX11;
            max = MAX12;
            s = SEG12;
            break;
        case 13:
            min = MAX12;
            max = MAX13;
            s = SEG13;
            break;
        case 14:
            min = MAX13;
            max = ~0;
            s = SEG14;
            break;
    }
    printf("%s %d\n", "Start of Free List number", num);
    for (ptr = GET_FREE(seg_start + s); ptr != NULL;
        ptr = GET_FREE(NEXT_FREE(ptr))) {
        size = GET_SIZE(HDRP(ptr));
        //Check that block ptr is in the right seg list.
        if (!(min < size && size <= max)) {
            printf("Free block pointer %p is in the wrong seg list.\n", ptr);
        }
        if (verbose) printblock(ptr, 1);

    }
    printf("%s %d\n", "End of Free List number", num);
    
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    heap_listp = NULL;
    seg_start = NULL;
    void* flist_root;
    /* Create space for seg list pointers. */
    if ((seg_start = mem_sbrk(NUM_SEGS*DSIZE)) == NULL) {
        return -1;
    }

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL) {
        return -1;
    }

    PUT4(heap_listp, 0); /* Alignment padding */
    PUT4(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT4(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT4(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp += (2*WSIZE); //heap pointer points to the space in
    //between the prologue header and prologue footer.

    //Initialize seg list pointers to NULL
    PUT(seg_start + SEG1, (size_t) NULL);
    PUT(seg_start + SEG2, (size_t) NULL);
    PUT(seg_start + SEG3, (size_t) NULL);
    PUT(seg_start + SEG4, (size_t) NULL);
    PUT(seg_start + SEG5, (size_t) NULL);
    PUT(seg_start + SEG6, (size_t) NULL);
    PUT(seg_start + SEG7, (size_t) NULL);
    PUT(seg_start + SEG8, (size_t) NULL);
    PUT(seg_start + SEG9, (size_t) NULL);
    PUT(seg_start + SEG10, (size_t) NULL);
    PUT(seg_start + SEG11, (size_t) NULL);
    PUT(seg_start + SEG12, (size_t) NULL);
    PUT(seg_start + SEG13, (size_t) NULL);
    PUT(seg_start + SEG14, (size_t) NULL);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    flist_root = extend_heap(CHUNKSIZE/WSIZE);
    if (flist_root == NULL) {
        return -1;
    }
    return 0;
}

/*
 * malloc - given a size, malloc allocates size bytes of payload in the 
 * heap and returns a pointer to that block.
 */
void *malloc (size_t size) {
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    void *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= ALIGNMENT) {
        asize = OVERHEAD;
    }
    else {
        asize = ALIGNMENT * ((size + (ALLOC_OVERHEAD) + 
            (ALIGNMENT-1)) / ALIGNMENT);
    }

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        printf("%s\n", "Could not extend heap");
        return NULL;
    }
        
    place(bp, asize);
    return bp;
}

/*
 * free - Given a pointer to a block that was allocated by malloc,
 * free removes it from memory, making it available to use.
 */
void free (void *ptr) {
    if(!ptr) return;

    size_t size = GET_SIZE(HDRP(ptr)); //size of input ptr

    PUT4(HDRP(ptr), PACK(size, 0));
    PUT4(FTRP(ptr), PACK(size, 0));
    flist_insert(coalesce(ptr));
}

/*
 * realloc - Given and oldptr that has already been allocated by malloc
 * or realloc, reallocate the memory in there to a new size bytes. 
 */
void *realloc(void *oldptr, size_t size)
{
  size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return malloc(size);
  }

  newptr = malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
    return 0;
  }

  /* Copy the old data. */
  oldsize = GET_SIZE(HDRP(oldptr));
  if(size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  free(oldptr);

  return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t total_size = nmemb * size;
    void *newptr;
    newptr = malloc(total_size);
    memset(newptr, 0, total_size);
    return newptr;
}

/*
 * mm_checkheap - Function for debugging. Checks the invariants in the 
 * heap and prints out the heap very clearly so it is easy to debug.
 */
void mm_checkheap(int verbose) {
    void *bp = heap_listp;
    void *prev = NULL;

    //In verbose mode, print out the heap block by block.
    if (verbose)
        printf("Heap (%p):\n", heap_listp);
    //Check prologue.
    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);
    //This for loop prints and checks each block in the entire heap.
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) {
            printblock(bp, 0);
        }
        //Check for adjacent free blocks.
        if (prev != NULL) {
            if (!GET_ALLOC(HDRP(prev)) && !GET_ALLOC(HDRP(bp))) {
                printf("Adjacent free blocks: %p and %p\n", 
                    prev, bp);
            }
        }
        prev = bp;
        checkblock(bp);//checks for header/footer mismatch.
        //Check for next/prev pointer inconsistencies in free blocks.
        if (!GET_ALLOC(HDRP(bp))) {
            if (GET_FREE(NEXT_FREE(bp)) != NULL && 
                GET_FREE(PREV_FREE(GET_FREE(NEXT_FREE(bp)))) != bp) {
                printf("Free block %p's next pointer is incorrect\n", bp);
            }
            if (GET_FREE(PREV_FREE(bp)) != NULL && 
                GET_FREE(NEXT_FREE(GET_FREE(PREV_FREE(bp)))) != bp) {
                printf("Free block %p's prev pointer is incorrect\n", bp);
            }
        }
    }
     
    if (verbose)
        printblock(bp, 0);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");

    for (int i = 0; i < NUM_SEGS; i++) {
        print_free_list(i*FREE_PTR_SIZE, 1);
    }
        
}
