#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "simVM.h"

//
// A virtual memory simulation.
//
// Virtual memory is a sequence of 32-bit words.
//
// Physical memory is a shorter sequence of 32-bit words.
//
// Virtual memory addresses are 32 bits.
//
// Virtual and physical memory is managed in fixed-size pages.
//
// A page table, which is logically in physical memory, maps virtual
// memory addresses to physical memory addresses. Since physical
// memory is smaller than virtual memory, the page table might indicate
// that a particular page is not currently present in physical memory,
// and that it is logically stored on disk.
//
// However this is a simulation, so all memory words are actually stored
// in the memory of this program, and disk is not used. Similarly the page
// table does not actually exist in the simulated physical memory, but
// rather exists only in the data structures of the simulation.
//
// A translation lookaside buffer (TLB) is simulated. The TLB stores
// recent virtual-to-physical address translations.
//
// The following properties of the virtual memory are set when it is
// created:
//   1. size of the virtual memory in pages
//   2. size of the physical memory in pages
//   3. size of a page in words
//   4. number of TLB entries
//   5. page replacement algorithm
//   6. TLB replacement algorithm
//
// The size of the virtual memory must be larger than the size of the
// physical memory.
//
// The size of a page must be a power of two.
//
// The size of the virtual memory times the size of a page must be less
// than or equal to 2^32.
//
// The size of the TLB should be less than or equal to the size of physical
// memory.
//
// The replacement algorithms are either 0 for round-robin replacement or
// 1 for LRU replacement.
//
// A virtual memory system is initialized to have the first K pages
// of virtual memory loaded into physical memory, where K is the
// number of pages in the physical memory. Initially the virtual
// memory system contains arbitrary values (i.e. not necessarily
// zeros).
//
// The TLB is initialized to have the VM to PM mapping for the
// first N pages loaded into physical pages (i.e. starting at physical
// page 0), where N is the number of TLB entries.
//
// The goal of the simulation is to report the number of page misses,
// the number of TLB misses, and the number of disk writes.
//

#define VM_ROUNDROBIN_REPLACEMENT 0
#define VM_LRU_REPLACEMENT 1

struct VM {
  int pagesize, vpage;
  int ppage, palg, *pvirt, *ptime, *dirty;
  int tlb, tlbalg, *ptlb, *vtlb, *tlbtime; 
  int rrp, rrt, timestamp;
  int pc, tc, dc;
  void *mem, *disk;
};


#define INTS(n) ((int*)calloc((n), sizeof(int)))
#define WORDS(n) (calloc((n), sizeof(int)))
#define VM(a) ((struct VM *)(a))
// createVM
//
// Create the virtual memory system and return a "handle" for it.
//
// If there is a violation of any of the constraints on the properties
// of the virtual memory system, this function will return NULL.
//
// If this function fails for any other reason (e.g. malloc returns NULL),
// an error message will be printed to stderr and the program will be
// terminated.
//
void *createVM(
  unsigned int sizeVM,   // size of the virtual memory in pages
  unsigned int sizePM,   // size of the physical memory in pages
  unsigned int pageSize, // size of a page in words
  unsigned int sizeTLB,  // number of translation lookaside buffer entries
  char pageReplAlg,      // page replacement alg.: 0 is Round Robin, 1 is LRU
  char tlbReplAlg        // TLB replacement alg.: 0 is Round Robin, 1 is LRU
  ) 
{
  struct VM model = {
	  .pagesize = pageSize, .vpage = sizeVM,
	  .ppage = sizePM, .palg = pageReplAlg, .pvirt = INTS(sizePM), .ptime = INTS(sizePM), .dirty = INTS(sizePM),
	  .tlb = sizeTLB,  .tlbalg = tlbReplAlg,  .ptlb = INTS(sizeTLB), .vtlb = INTS(sizeTLB), .tlbtime = INTS(sizeTLB),
	  .pc = 0, .tc = 0, .dc = 0,
	  .rrp = 0, .rrt = 0, .timestamp = 0,
	  .mem = WORDS(sizePM * pageSize), 
	  .disk = WORDS(sizeVM * pageSize),
  };
  
  for (int i = 0; i < sizePM; i++) {
	  model.pvirt[i] = i;
  }
  for (int i = 0; i < sizeTLB; i++) {
	  model.ptlb[i] = i;
	  model.vtlb[i] = i;
  }
  struct VM *ret = (struct VM*)malloc(sizeof(model));
  *ret = model;
  return ret;
}

int lookup_in_tlb_and_mark(struct VM *model, int pte) {
	for (int i = 0; i < model->tlb; i++) {
		if (model->vtlb[i] == pte) {
			model->tlbtime[i] = model->timestamp;
			return model->ptlb[i];
		}
	}
	return -1;
}

int lookup_in_mem(struct VM *model, int pte) {
	for (int i = 0; i < model->ppage; i++) {
		if (model->pvirt[i] == pte) {
			return i;
		}
	}
	return -1;
}

void *make_address(struct VM *model, int index, int add) {
	return model->mem + index * model->pagesize * 4 + add * 4;
}

void mark(struct VM *model, int pte, int dirty) {
	if (dirty) {
		model->dirty[pte] = 1;
	}
	model->ptime[pte] = model->timestamp;
}

int minindex(int *p, int n) {
	int value = 2147483647, index = -1;
	for (int i = 0; i < n; i++) {
		if (p[i] < value) {
			value = p[i];
			index = i;
		}
	}
	return index;
}

int choose_page(struct VM *model) {
	if (model->palg == 0) {
		model->rrp++;
		model->rrp %= model->ppage;
		return (model->rrp + model->ppage - 1) % model->ppage;
	} else {
		return minindex(model->ptime, model->ppage);
	}
}

int choose_tlb(struct VM *model) {
	if (model->tlbalg == 0) {
		model->rrt++;
		model->rrt %= model->tlb;
		return (model->rrt + model->tlb - 1) % model->tlb;
	} else {
		return minindex(model->tlbtime, model->tlb);
	}
}

void addtlb(struct VM *model, int mem, int pte) {
	int index = choose_tlb(model);
	model->ptlb[index] = mem;
	model->vtlb[index] = pte;
	model->tlbtime[index] = model->timestamp;
}

void flushtlb(struct VM *model, int mem, int pte) {
	for (int i = 0; i < model->tlb; i++) {
		if (model->ptlb[i] == mem) {
			model->vtlb[i] = pte;
			return;
		}
	}
	addtlb(model, mem, pte);
}

void *real_address(struct VM *model, unsigned int address, int dirty) {
	model->timestamp++;
	int pte  = address / model->pagesize;
	int add  = address % model->pagesize;
	int mem = lookup_in_tlb_and_mark(model, pte);
	if (mem != -1) {
		mark(model, mem, dirty);
		return make_address(model, mem, add);
	}
	model->tc++;
	mem = lookup_in_mem(model, pte);
	if (mem != -1) {
		mark(model, mem, dirty);
		addtlb(model, mem, pte);
		return make_address(model, mem, add);
	}
	model->pc++;
	mem = choose_page(model);
	if (model->dirty[mem]) {
		model->dc++;
		memcpy(model->disk + model->pvirt[mem] * model->pagesize * 4,
		       model->mem  + mem * model->pagesize * 4,
			   model->pagesize * 4);
	}
	model->pvirt[mem] = pte;
	model->ptime[mem] = model->timestamp;
	model->dirty[mem] = 0;
	memcpy(model->mem  + mem * model->pagesize * 4,
	       model->disk + model->pvirt[mem] * model->pagesize * 4,
		   model->pagesize * 4);
	flushtlb(model, mem, pte);
	mark(model, mem, dirty);
	return make_address(model, mem, add);
}

void *read_address(struct VM *model, unsigned int address) {
	return real_address(model, address, 0);
}

void write_address(struct VM *model, unsigned int address, void *value) {
	memcpy(real_address(model, address, 1), value, 4);
}

// readInt
//
// Read an int from virtual memory.
//
// If the handle is not one returned by createVM, the behavior is
// undefined.
//
// If the address is out of range, an error message will be printed to
// stderr and the program will be terminated.
//
int readInt(void *handle, unsigned int address) {
	return *(int *)read_address(VM(handle), address);
}

// readFloat
//
// Read a float from virtual memory.
//
// If the handle is not one returned by createVM, the behavior is
// undefined.
//
// If the address is out of range, an error message will be printed to
// stderr and the program will be terminated.
//
float readFloat(void *handle, unsigned int address) {
	return *(float *)read_address(VM(handle), address);
}

// writeInt
//
// Write an int to virtual memory.
//
// If the handle is not one returned by createVM, the behavior is
// undefined.
//
// If the address is out of range, an error message will be printed to
// stderr and the program will be terminated.
//
void writeInt(void *handle, unsigned int address, int value) {
	write_address(VM(handle), address, &value);
}

// writeFloat
//
// Write a float to virtual memory.
//
// If the handle is not one returned by createVM, the behavior is
// undefined.
//
// If the address is out of range, an error message will be printed to
// stderr and the program will be terminated.
//
void writeFloat(void *handle, unsigned int address, float value) {
	write_address(VM(handle), address, &value);
}

// printStatistics
//
// Print the total number of page faults, the total number of TLB misses
// and the total number of disk writes.
//
// If the handle is not one returned by createVM, the behavior is
// undefined.
//
// Here is a sample output:
//
//   Number of page faults: 123
//   Number of TLB misses: 125
//   Number of disk writes: 64
//
void printStatistics(void *handle) {
	printf("Number of page faults: %d\n"
		   "Number of TLB misses: %d\n"
           "Number of disk writes: %d\n", 
	       VM(handle)->pc, 
	       VM(handle)->tc,
	       VM(handle)->dc);

}

// cleanupVM
//
// Cleanup the memory used by the simulation of the virtual memory system.
//
// If the handle is not one returned by createVM, the behavior is
// undefined.
//
void cleanupVM(void *handle) {
	free(VM(handle)->pvirt);
	free(VM(handle)->ptime);
	free(VM(handle)->dirty);
	free(VM(handle)->ptlb);
	free(VM(handle)->vtlb);
	free(VM(handle)->tlbtime);
	free(VM(handle)->mem);
	free(VM(handle)->disk);
	free(handle);
}
