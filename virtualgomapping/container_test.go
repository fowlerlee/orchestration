package virtualgomapping

import (
	"reflect"
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
	num, err := c.AllocateMemory(5)
	if err != nil {
		t.Fatalf("could not allocate the page: %v", num)
	}
	t.Logf("Allocated %d bytes of memory", num)
	dataIn := []byte{'A', 'B'}
	err = c.WriteMemory(1, dataIn)
	if err != nil {
		t.Fatalf("error writing to the memory %v", err)
	}
	t.Log("Data written successfully")

	t.Logf("Attempting to read %d bytes from address 0", num)
	dataOut, errOut := c.ReadMemory(1, num)
	if errOut != nil {
		t.Fatalf("error reading the memory address, %v", err)
	}
	t.Logf("Read %d bytes: %v", len(dataOut), dataOut)
	if !reflect.DeepEqual(dataIn, dataOut) {
		t.Errorf("data written does not match the data read from virtual memory. Expected: %v, Actual: %v", dataIn, dataOut)
	}
}

func TestAllocateMemory(t *testing.T) {
	c := NewContainer()
	_, err := c.AllocateMemory(10)
	if err != nil {
		t.Fatalf("failed to allocate memory, %v", err)
	}

}
