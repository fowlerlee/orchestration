package virtualgomapping

import (
	// "reflect"
	"testing"
)

func TestNewContainer(t *testing.T) {
	c := NewContainer()
	if c == nil {
		t.Fatal("func NewContainer returned nil err")
	}
	if c.vm == nil {
		t.Fatal("container's VirtualMemory is nil")
	}
	// num, err := c.AllocateMemory(10)
	// if err != nil {
	// 	t.Fatal("could not allocate the page")
	// }
	// dataIn := []byte{'A', 'B'}
	// err = c.WriteMemory(10, dataIn)
	// if err != nil {
	// 	t.Fatalf("error writing to the memory %v", err)
	// }
	// _, errOut := c.ReadMemory(10, num)
	// if errOut != nil {
	// 	t.Fatalf("error reading the memory address, %v", err)
	// }
	// if !reflect.DeepEqual(dataIn, dataOut[:len(dataIn)]) {
	// 	t.Errorf("data written does not match the data read from virtual memory. Expected: %v, Actual: %v", dataIn, dataOut)
	// }
}

func TestAllocateMemory(t *testing.T) {
	c := NewContainer()
	_, err := c.AllocateMemory(10)
	if err != nil {
		t.Fatalf("failed to allocate memory, %v", err)
	}

}
