package virtualgomapping

import (
	"fmt"
)

type Container struct {
	vm *VirtualMemory
}

func NewContainer() *Container {
	return &Container{
		vm: &VirtualMemory{},
	}
}

func (c *Container) AllocateMemory(size uint) (uint, error) {
	pages := (size + PageSize - 1) / PageSize
	for i := uint(0); i < pages; i++ {
		if !c.vm.AllocatePage(i) {
			return 0, fmt.Errorf("failed to allocate page %d", i)
		}
	}
	return 0, nil // Return the starting virtual address (in this case, always 0)
}

func (c *Container) WriteMemory(address uint, data []byte) error {
	for i, b := range data {
		pageIndex := (address + uint(i)) / PageSize
		offset := (address + uint(i)) % PageSize
		if err := c.vm.Write(pageIndex, offset, b); err != nil {
			return err
		}
	}
	return nil
}

func (c *Container) ReadMemory(address uint, size uint) ([]byte, error) {
	fmt.Printf("ReadMemory called with address %d, size %d\n", address, size)
	result := make([]byte, size)
	for i := uint(0); i < size; i++ {
		pageIndex := (address + i) / PageSize
		offset := (address + i) % PageSize
		fmt.Printf("Reading byte at address %d (page %d, offset %d)\n", address+i, pageIndex, offset)
		b, err := c.vm.Read(pageIndex, offset)
		if err != nil {
			return nil, fmt.Errorf("error reading at address %d (page %d, offset %d): %v", address+i, pageIndex, offset, err)
		}
		result[i] = b
		fmt.Printf("Read byte 0x%02x\n", b)
	}
	fmt.Printf("ReadMemory returning %d bytes: %v\n", len(result), result)
	return result, nil
}
