#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */


#ifdef TEST_ASSERT
inline static void assert(int e) {
		if (!e) {
				const char * msg = "Assertion Failed!\n";
				write(2, msg, strlen(msg));
				exit(1);
		}
}
#else
#include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;
static void NEW_CHUNK_ADDER();
/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
		return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
		return get_header_from_offset(h, get_block_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
		return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
		set_block_state(fp,FENCEPOST);
		set_block_size(fp, ALLOC_HEADER_SIZE);
		fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
		if (numOsChunks < MAX_OS_CHUNKS) {
				osChunkList[numOsChunks++] = hdr;
		}
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
		// Convert to char * before performing operations
		char * mem = (char *) raw_mem;

		// Insert a fencepost at the left edge of the block
		header * leftFencePost = (header *) mem;
		initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

		// Insert a fencepost at the right edge of the block
		header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
		initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
		void * mem = sbrk(size);
		insert_fenceposts(mem, size);
		header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
		set_block_state(hdr, UNALLOCATED);
		set_block_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
		hdr->left_size = ALLOC_HEADER_SIZE;
		return hdr;
}

// Function to allocate full block
static header * SAME_SIZE_ALLOCATOR(header *block_ptr) {
		// Changing previous pointers and state of block
		block_ptr->next->prev = block_ptr->prev;
		block_ptr->prev->next = block_ptr->next;
		set_block_state(block_ptr, ALLOCATED);
		block_ptr = get_header_from_offset(block_ptr, ALLOC_HEADER_SIZE);
		return block_ptr;
}

// Function to allocate part of a bigger block
static header * LARGER_SIZE_ALLOCATOR(header *block_ptr, size_t actual_size) {
		header *return_ptr;
		size_t diff = get_block_size(block_ptr) - actual_size;
		// If size not big enough, allocating whole block
		if (diff < 2 * ALLOC_HEADER_SIZE) {
				return SAME_SIZE_ALLOCATOR(block_ptr);
		}
		// Setting the values for block
		return_ptr = get_header_from_offset(block_ptr, get_block_size(block_ptr) - actual_size);
		set_block_state(return_ptr, ALLOCATED);
		set_block_size(return_ptr, actual_size);
		set_block_size(block_ptr, diff);
		return_ptr->left_size = diff;
		// Calculating the index
		diff -= ALLOC_HEADER_SIZE;
		diff /= 8;
		diff--;
		header *start_ptr;
		// If not in last index
		if (diff < N_LISTS - 1) {
				// Changing previous pointers
				start_ptr = &freelistSentinels[diff];
				block_ptr->next->prev = block_ptr->prev;
				block_ptr->prev->next = block_ptr->next;
				// Checking if list empty
				if (start_ptr->next == start_ptr && start_ptr->prev == start_ptr) {
						start_ptr->next = block_ptr;
						start_ptr->prev = block_ptr;
						block_ptr->next = start_ptr;
						block_ptr->prev = start_ptr;
				}
				// or not
				else{
						block_ptr->next = start_ptr->next;
						start_ptr->next = block_ptr;
						block_ptr->next->prev = block_ptr;
						block_ptr->prev = start_ptr;
				}
		}
		// Updating values of block to right
		header *right_block = get_header_from_offset(return_ptr, get_block_size(return_ptr));
		right_block->left_size = get_block_size(return_ptr);
		return_ptr = get_header_from_offset(return_ptr, ALLOC_HEADER_SIZE);
		return return_ptr;
}
/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
		size_t actual_size;
		if (raw_size == 0)
				return NULL;
		// Increasing raw_size if less than smallest allocable size
		if (raw_size < ALLOC_HEADER_SIZE)
				raw_size = ALLOC_HEADER_SIZE;
		actual_size = raw_size;
		actual_size += ALLOC_HEADER_SIZE;
		// Making the size a multiple of 8
		size_t remainder;
		remainder = actual_size % 8;
		if (remainder != 0) {
				size_t extra_mem;
				extra_mem = 8 - remainder;
				actual_size += extra_mem; 
		}
		int i;
		bool BREAK = false;
		// Calculating index
		header *block_ptr = NULL;
		i = actual_size - ALLOC_HEADER_SIZE;
		i /= 8;
		i--;
		for (i = i; i < N_LISTS - 1; i++) {
				header *freelist_ptr = &freelistSentinels[i];
				// if not an empty list
				if (freelist_ptr->next != freelist_ptr && freelist_ptr->prev != freelist_ptr) {
						freelist_ptr = freelist_ptr->next;
						// If same size block
						if (get_block_size(freelist_ptr) == actual_size) {
								block_ptr = freelist_ptr;
								return SAME_SIZE_ALLOCATOR(block_ptr);
						}
						// or greater size block
						else if (get_block_size(freelist_ptr) > actual_size) {
								block_ptr = freelist_ptr;
								return LARGER_SIZE_ALLOCATOR(block_ptr, actual_size);
						}
				}
		}
		// If no allocations, check last list
		header *freelist_ptr = &freelistSentinels[N_LISTS - 1];
		// If list empty
		if (freelist_ptr->next == freelist_ptr && freelist_ptr->prev == freelist_ptr) {
				// Add new chunk
				NEW_CHUNK_ADDER(raw_size, actual_size);
				return allocate_object(raw_size);
		}
		header *start_ptr = freelist_ptr;
		freelist_ptr = freelist_ptr->next;
		// Loop to get appropriate sized block
		while (freelist_ptr != start_ptr) {
				// If same size
				if (get_block_size(freelist_ptr) == actual_size) { 
						return SAME_SIZE_ALLOCATOR(freelist_ptr);
				}
				// or larger size
				else if (get_block_size(freelist_ptr) > actual_size) {
						return LARGER_SIZE_ALLOCATOR(freelist_ptr, actual_size);
				}
				freelist_ptr = freelist_ptr->next;
		}
		// If no allocations, check last list
		NEW_CHUNK_ADDER(raw_size, actual_size);
		return allocate_object(raw_size);
}

// Function to allocate new chunk
static void NEW_CHUNK_ADDER(size_t raw_size, size_t actual_size) {
		int numChunks = ARENA_SIZE;
		bool MERGE = false;
		// Getting the number of chunks
		while (numChunks < actual_size + 2 * ALLOC_HEADER_SIZE) {
				numChunks += ARENA_SIZE;
		}
		header *next_chunk;
		numChunks /= ARENA_SIZE;
		// Allocate first chunk
		header *chunk_hdr = allocate_chunk(ARENA_SIZE);
		header *left_FP = get_header_from_offset(chunk_hdr, -ALLOC_HEADER_SIZE);
		header *right_FP = get_header_from_offset(chunk_hdr, get_block_size(chunk_hdr));
		header *last_block = get_header_from_offset(lastFencePost, -(lastFencePost->left_size));
		size_t last_block_size = get_block_size(last_block);
		// Check if both chunks are contigious
		if (get_header_from_offset(lastFencePost, ALLOC_HEADER_SIZE) == left_FP) 
				MERGE = true;
		if (MERGE)
				lastFencePost = right_FP;
		// Allocating remaining chunks
		for(int i = 1; i < numChunks; i++) {
				next_chunk = allocate_chunk(ARENA_SIZE);
				right_FP = get_header_from_offset(right_FP, ARENA_SIZE);
		}
		// If both are contigious
		if (MERGE) {
				lastFencePost = right_FP;
				set_block_state(lastFencePost, FENCEPOST);
				set_block_size(lastFencePost, ALLOC_HEADER_SIZE);
				// If last block in main chunk is UNALLOCATED coalesce
				if (get_block_state(last_block) == UNALLOCATED) {
						size_t init_index = last_block_size;
						init_index -= ALLOC_HEADER_SIZE;
						init_index /= 8;
						init_index--;
						last_block_size += (numChunks * ARENA_SIZE);
						set_block_size(last_block, last_block_size);
						last_block_size -= ALLOC_HEADER_SIZE;
						last_block_size /= 8;
						last_block_size--;
						if (last_block_size >= N_LISTS - 1)
								last_block_size = N_LISTS - 1;
						if (init_index != last_block_size) {
								last_block->next->prev = last_block->prev;
								last_block->prev->next = last_block->next;
								header *sent_ptr = &freelistSentinels[last_block_size];
								if (sent_ptr->next == sent_ptr) {
										sent_ptr->next = last_block;
										sent_ptr->prev = last_block;
										last_block->next = sent_ptr;
										last_block->prev = sent_ptr;
								}
								else {
										last_block->next = sent_ptr->next;
										last_block->prev = sent_ptr;
										last_block->next->prev = last_block;
										sent_ptr->next = last_block;
								}
						}
				}
				// Else add the chunk to freelist
				else {
						chunk_hdr = get_header_from_offset(chunk_hdr, - 2 * ALLOC_HEADER_SIZE);
						set_block_size(chunk_hdr, numChunks * ARENA_SIZE);
						set_block_state(chunk_hdr, UNALLOCATED);
						chunk_hdr->left_size = last_block_size;
						size_t index = get_block_size(chunk_hdr);
						index -= ALLOC_HEADER_SIZE;
						index /= 8;
						index--;
						header * sent_ptr;
						if (index < N_LISTS - 1) {
								sent_ptr = &freelistSentinels[index];
						}
						else {
								sent_ptr = &freelistSentinels[N_LISTS - 1];
						}
						if (sent_ptr->next == sent_ptr) {
								sent_ptr->next = chunk_hdr;
								sent_ptr->prev = chunk_hdr;
								chunk_hdr->next = sent_ptr;
								chunk_hdr->prev = sent_ptr;
						}
						else {
								chunk_hdr->next = sent_ptr->next;
								chunk_hdr->prev = sent_ptr;
								chunk_hdr->next->prev = chunk_hdr;
								sent_ptr->next = chunk_hdr;
						}
				}
		}
		// If the chunks are not contigious
		if (!MERGE) {
				set_block_size(chunk_hdr, (numChunks * ARENA_SIZE) - 2 * ALLOC_HEADER_SIZE);
				set_block_state(chunk_hdr, UNALLOCATED);
				chunk_hdr->left_size = ALLOC_HEADER_SIZE;
				set_block_size(left_FP, ALLOC_HEADER_SIZE);
				set_block_size(right_FP, ALLOC_HEADER_SIZE);
				set_block_state(left_FP, FENCEPOST);
				set_block_state(right_FP, FENCEPOST);
				left_FP->left_size = ALLOC_HEADER_SIZE;
				right_FP->left_size = get_block_size(chunk_hdr);
				// Inserting the chunk in osChunkList
				insert_os_chunk(left_FP);
				header * sent_ptr = &freelistSentinels[N_LISTS - 1];
				// If list is empty
				if (sent_ptr->next == sent_ptr) {
						sent_ptr->next = chunk_hdr;
						sent_ptr->prev = chunk_hdr;
						chunk_hdr->next = sent_ptr;
						chunk_hdr->prev = sent_ptr;
				}
				// Else
				else {
						chunk_hdr->next = sent_ptr->next;
						chunk_hdr->prev = sent_ptr;
						chunk_hdr->next->prev = chunk_hdr;
						sent_ptr->next = chunk_hdr;
				}
		}
}
/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
		return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
		// Doing nothing if pointer is NULL
		if (p == NULL) {
				return; 
		}
		// Terminating if double free
		header *block_ptr = get_header_from_offset(p, -ALLOC_HEADER_SIZE);
		if (get_block_state(block_ptr) == UNALLOCATED) {
				printf("Double Free Detected\n");
				assert(0);
		}
		set_block_state(block_ptr, UNALLOCATED);  
		header *left_block = block_ptr;
		header *right_block = block_ptr;
		left_block =  get_header_from_offset(block_ptr, -(block_ptr->left_size));
		right_block = get_header_from_offset(block_ptr, get_block_size(block_ptr));
		// Covering case of freeing middle block in |F||A||F| or |F||A||A| or |A||A||F| or |A||A||A|
		if ((get_block_state(left_block) == ALLOCATED && get_block_state(right_block) == ALLOCATED ) || (get_block_state(left_block) == FENCEPOST && get_block_state(right_block) == ALLOCATED) || (get_block_state(left_block) == ALLOCATED && get_block_state(right_block) == FENCEPOST) || (get_block_state(left_block) == FENCEPOST && get_block_state(right_block) == FENCEPOST)) {
				size_t size = get_block_size(block_ptr);
				size -= ALLOC_HEADER_SIZE;
				size /= 8;
				size--;
				header *head_ptr;
				if (size < N_LISTS - 1) {
						head_ptr = &freelistSentinels[size];
				}
				else {
						head_ptr = &freelistSentinels[N_LISTS - 1];
				}
				header *next_ptr = block_ptr->next;
				if (head_ptr->next == head_ptr && head_ptr->prev == head_ptr) {
						head_ptr->next = block_ptr;  
						head_ptr->prev = block_ptr;  
						block_ptr->prev = head_ptr;  
						block_ptr->next = head_ptr;  
				}
				else {
						block_ptr->next = head_ptr->next;
						block_ptr->prev = head_ptr;
						head_ptr->next->prev = block_ptr;
						head_ptr->next = block_ptr;
				}
				set_block_state(block_ptr, UNALLOCATED);
		}
		// Covering case of freeing middle block in |U||A||A| or |U||A||F|
		else if ((get_block_state(left_block) == UNALLOCATED && get_block_state(right_block) == ALLOCATED) || (get_block_state(left_block) == UNALLOCATED && get_block_state(right_block) == FENCEPOST)){
				header *head_ptr;
				size_t size = get_block_size(block_ptr);
				size_t left_size = block_ptr->left_size;
				size += left_size;
				right_block->left_size = size;
				set_block_size(left_block, size);
				size -= ALLOC_HEADER_SIZE;
				size /= 8;
				size--;
				if (size < N_LISTS - 1) {
						if (left_block->next != left_block->prev) {
								left_block->next->prev = left_block->prev;
								left_block->prev->next = left_block->next;
						}
						else {
								left_block->prev->prev = left_block->prev;
								left_block->prev->next = left_block->prev;
						}
						head_ptr = &freelistSentinels[size];
						if (head_ptr->prev == head_ptr) {
								head_ptr->next = left_block;
								head_ptr->prev = left_block;
								left_block->prev = head_ptr;
								left_block->next = head_ptr;
						}
						else {
								left_block->next = head_ptr->next;
								head_ptr->next = left_block;
								left_block->next->prev = left_block;
								left_block->prev = head_ptr;
						}
				}
		} 
		// Covering case of freeing middle block in |A||A||U| or |F||A||U|
		else if ((get_block_state(left_block) == ALLOCATED && get_block_state(right_block) == UNALLOCATED) || (get_block_state(left_block) == FENCEPOST && get_block_state(right_block) == UNALLOCATED)) {
				header *head_ptr;
				size_t size = get_block_size(block_ptr);
				size_t right_size = get_block_size(right_block);
				size += right_size;
				set_block_state(block_ptr, UNALLOCATED);
				set_block_size(block_ptr, size);
				header *right_to_right = (header*) ((char *) right_block + right_size);
				right_to_right->left_size = size;
				size -= ALLOC_HEADER_SIZE;
				size /= 8;
				size--;
				if (size < N_LISTS - 1) {
						if (right_block->next != right_block->prev) {
								right_block->prev->next = right_block->next;
								right_block->next->prev = right_block->prev;
						}
						else {
								right_block->prev->prev = right_block->prev;
								right_block->prev->next = right_block->prev;
						}
						head_ptr = &freelistSentinels[size];
						if (head_ptr->prev == head_ptr) {
								head_ptr->next = block_ptr;
								head_ptr->prev = block_ptr;
								block_ptr->prev = head_ptr;
								block_ptr->next = head_ptr;
						}
						else {
								block_ptr->next = head_ptr->next;
								head_ptr->next = block_ptr;
								block_ptr->next->prev = block_ptr;
								block_ptr->prev = head_ptr;
						}
				}
				else {
						head_ptr = &freelistSentinels[N_LISTS - 1];
						right_block->prev->next = block_ptr;
						block_ptr->next = right_block->next;
						block_ptr->prev = right_block->prev;
						block_ptr->next->prev = block_ptr;
				}
		}
		// Covering case of freeing middle block in |U||A||U|
		else if ((get_block_state(left_block) == UNALLOCATED && get_block_state(right_block) == UNALLOCATED)) {
				header *head_ptr;
				size_t size = get_block_size(left_block);
				size += get_block_size(block_ptr);
				size += get_block_size(right_block);
				set_block_size(left_block, size);
				header *right_to_right = get_header_from_offset(right_block, get_block_size(right_block));
				right_to_right->left_size = size;
				size -= ALLOC_HEADER_SIZE;
				size /= 8;
				size--;
				if (right_block->next != right_block->prev) {
						right_block->next->prev = right_block->prev;
						right_block->prev->next = right_block->next;
				}
				else {
						right_block->prev->prev = right_block->prev;
						right_block->prev->next = right_block->prev;
				}
				if (size < N_LISTS - 1){
						if (left_block->next != left_block->prev) {
								left_block->next->prev = left_block->prev;
								left_block->prev->next = left_block->next;
						}
						else {
								left_block->prev->prev = left_block->prev;
								left_block->prev->next = left_block->prev;
						}
						head_ptr = &freelistSentinels[size];
						if (head_ptr->prev == head_ptr) {
								head_ptr->next = left_block;
								head_ptr->prev = left_block;
								left_block->prev = head_ptr;
								left_block->next = head_ptr;
						}
						else {
								left_block->next = head_ptr->next;
								head_ptr->next = left_block;
								left_block->next->prev = left_block;
								left_block->prev = head_ptr;
						}
				}
		}
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
		for (int i = 0; i < N_LISTS; i++) {
				header * freelist = &freelistSentinels[i];
				for (header * slow = freelist->next, * fast = freelist->next->next; 
								fast != freelist; 
								slow = slow->next, fast = fast->next->next) {
						if (slow == fast) {
								return slow;
						}
				}
		}
		return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
		for (int i = 0; i < N_LISTS; i++) {
				header * freelist = &freelistSentinels[i];
				for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
						if (cur->next->prev != cur || cur->prev->next != cur) {
								return cur;
						}
				}
		}
		return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
		header * cycle = detect_cycles();
		if (cycle != NULL) {
				fprintf(stderr, "Cycle Detected\n");
				print_sublist(print_object, cycle->next, cycle);
				return false;
		}

		header * invalid = verify_pointers();
		if (invalid != NULL) {
				fprintf(stderr, "Invalid pointers\n");
				print_object(invalid);
				return false;
		}

		return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
		if (get_block_state(chunk) != FENCEPOST) {
				fprintf(stderr, "Invalid fencepost\n");
				print_object(chunk);
				return chunk;
		}

		for (; get_block_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
				if (get_block_size(chunk)  != get_right_header(chunk)->left_size) {
						fprintf(stderr, "Invalid sizes\n");
						print_object(chunk);
						return chunk;
				}
		}

		return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
		for (size_t i = 0; i < numOsChunks; i++) {
				header * invalid = verify_chunk(osChunkList[i]);
				if (invalid != NULL) {
						return invalid;
				}
		}

		return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
		// Initialize mutex for thread safety
		pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
		// Manually set printf buffer so it won't call malloc when debugging the allocator
		setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

		// Allocate the first chunk from the OS
		header * block = allocate_chunk(ARENA_SIZE);

		header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
		insert_os_chunk(prevFencePost);

		lastFencePost = get_header_from_offset(block, get_block_size(block));

		// Set the base pointer to the beginning of the first fencepost in the first
		// chunk from the OS
		base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

		// Initialize freelist sentinels
		for (int i = 0; i < N_LISTS; i++) {
				header * freelist = &freelistSentinels[i];
				freelist->next = freelist;
				freelist->prev = freelist;
		}

		// Insert first chunk into the free list
		header * freelist = &freelistSentinels[N_LISTS - 1];
		freelist->next = block;
		freelist->prev = block;
		block->next = freelist;
		block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
		pthread_mutex_lock(&mutex);
		header * hdr = allocate_object(size); 
		pthread_mutex_unlock(&mutex);
		return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
		return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
		void * mem = my_malloc(size);
		memcpy(mem, ptr, size);
		my_free(ptr);
		return mem; 
}

void my_free(void * p) {
		pthread_mutex_lock(&mutex);
		deallocate_object(p);
		pthread_mutex_unlock(&mutex);
}

bool verify() {
		return verify_freelist() && verify_tags();
}
