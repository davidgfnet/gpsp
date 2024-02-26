#ifndef _MEMMAP_H
#define _MEMMAP_H

#ifdef __cplusplus
extern "C" {
#endif

void *map_jit_block(unsigned size);
void unmap_jit_block(void *bufptr, unsigned size);

#ifdef __cplusplus
}
#endif

#endif
