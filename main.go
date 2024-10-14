package main

import (
	"fmt"
	"time"

	"github.com/fowlerlee/orchestration/common"
	"github.com/fowlerlee/orchestration/manager"
	"github.com/fowlerlee/orchestration/worker"
)

func main() {
	fmt.Println("Enter commands for number of workers: ")
	var m *manager.Manager
	addressManager := "localhost:8081"
	addressWorker1 := "localhost:8082"
	addressWorker2 := "localhost:8083"
	// addressClient := "localhost:8084"

	m = manager.MakeManager(addressManager)

	m.StartManagerRPC()

	w1 := worker.CreateWorker(addressWorker1)
	w2 := worker.CreateWorker(addressWorker2)

	w1.StartWorkerRPC()
	w2.StartWorkerRPC()

	args := &common.AssignWorkArgs{ImageName: "alpine: 1"}
	reply := &common.AssignWorkResults{}

	args = &common.AssignWorkArgs{ImageName: "alpine: 2"}

	time.Sleep(time.Second * 5)

	m.AssignWorkToWorker(addressWorker1, args, reply)

	m.AssignWorkToWorker(addressWorker2, args, reply)

	fmt.Printf("worker 1 given work image: %s \n", w1.DockerImage)
	fmt.Printf("worker 2 given work image: %s \n", w2.DockerImage)

	// close all resources manually
	w1.StopWorkerRPC()
	w2.StopWorkerRPC()
	m.StopManagerRPC()

	fmt.Println("program exited from main with all resources cleaned up")

	// client := &Client{
	// 	ID:      uuid.New(),
	// 	Queue:   *queue.New(),
	// 	Channel: sharedChan,
	// 	State:   AssignTask,
	// }

}
