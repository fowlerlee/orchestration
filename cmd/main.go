package main

import "fmt"
import "virtualgomapping"


func main() {
	container := virtualgomapping.NewContainer()

	// Allocate memory in the container
	_, err := container.AllocateMemory(PageSize)
	if err != nil {
		fmt.Println("Error allocating memory:", err)
		return
	}

	// Write data to the allocated memory
	data := []byte("Hello, virtualized memory!")
	err = container.WriteMemory(0, data)
	if err != nil {
		fmt.Println("Error writing memory:", err)
		return
	}

	// Read data from the allocated memory
	readData, err := container.ReadMemory(0, uint(len(data)))
	if err != nil {
		fmt.Println("Error reading memory:", err)
		return
	}

	fmt.Println(string(readData))
}
