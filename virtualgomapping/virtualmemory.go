//go:build darwin
// +build darwin

package virtualgomapping

/*
#cgo LDFLAGS: -L${SRCDIR}/rust_lib -lvirtualmem
#include <stdbool.h>
#include <stdint.h>

bool allocate_page(size_t page_index);
void free_page(size_t page_index);
int32_t read_memory(size_t page_index, size_t offset);
bool write_memory(size_t page_index, size_t offset, uint8_t value);
*/
import "C"
import (
	"fmt"
)

const PageSize = 4096

type VirtualMemory struct{}

func (vm *VirtualMemory) AllocatePage(pageIndex uint) bool {
	return bool(C.allocate_page(C.size_t(pageIndex)))
}

func (vm *VirtualMemory) FreePage(pageIndex uint) {
	C.free_page(C.size_t(pageIndex))
}

func (vm *VirtualMemory) Read(pageIndex, offset uint) (byte, error) {
	result := C.read_memory(C.size_t(pageIndex), C.size_t(offset))
	if result == -1 {
		return 0, fmt.Errorf("failed to read memory")
	}
	return byte(result), nil
}

func (vm *VirtualMemory) Write(pageIndex, offset uint, value byte) error {
	success := C.write_memory(C.size_t(pageIndex), C.size_t(offset), C.uint8_t(value))
	if !success {
		return fmt.Errorf("failed to write memory")
	}
	return nil
}
