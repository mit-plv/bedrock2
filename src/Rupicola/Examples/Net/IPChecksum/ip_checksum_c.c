// http://www.microhowto.info/howto/calculate_an_internet_protocol_checksum_in_c.html
#include <stdint.h>
#include <memory.h>

uint16_t ip_checksum(void* vdata,uintptr_t length) {
    // Cast the data pointer to one that can be indexed.
    char* data=(char*)vdata;

    // Initialise the accumulator.
    uint32_t acc=0xffff;

    // Handle complete 16-bit blocks.
    for (size_t i=0;i+1<length;i+=2) {
        acc += (255 & data[i]) | (255 & data[i+1]) << 8;
        acc = (acc & 0xffff) + (acc >> 16);
    }

    // Handle any partial block at the end of the data.
    if (length&1) {
        acc += data[length - 1];
        acc = (acc & 0xffff) + (acc >> 16);
    }

    // Return the checksum in network byte order.
    return ~acc;
}
