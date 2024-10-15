package main

import (
	"fmt"
	"os"
	"time"

	"github.com/fowlerlee/orchestration/client"
	"github.com/fowlerlee/orchestration/common"
	"github.com/fowlerlee/orchestration/manager"
	"github.com/fowlerlee/orchestration/worker"
)

func main() {
	fmt.Println("Start in format `go run main.go followed by port numbers for client manager and worker(s).")
	fmt.Println("eg. go run main.go 8080 8081 8082 8083 8084")
	localhost := "localhost:"
	addressClient := localhost + "8080"
	addressManager := localhost + "8081"
	addressWorker1 := localhost + "8082"
	addressWorker2 := localhost + "8083"
	addressWorker3 := localhost + "8084"

	if len(os.Args) == 6 {
		addressClient = os.Args[1]
		addressManager = os.Args[2]
		addressWorker1 = os.Args[3]
		addressWorker2 = os.Args[4]
		addressWorker3 = os.Args[5]
	}

	m := manager.MakeManager(addressManager)
	m.StartManagerRPC()

	c := client.MakeClient(addressClient)
	c.StartClientRPC()

	w1 := worker.CreateWorker(addressWorker1)
	w2 := worker.CreateWorker(addressWorker2)
	w3 := worker.CreateWorker(addressWorker3)
	w1.StartWorkerRPC()
	w2.StartWorkerRPC()
	w3.StartWorkerRPC()

	time.Sleep(time.Second * 2)
	argsCl := &common.ClientManagerArgs{}
	replyCl := &common.ClientManageResult{}
	c.AssignWorkToManager(addressManager, argsCl, replyCl)

	args := &common.AssignWorkArgs{ImageName: "alpine: 1"}
	reply := &common.AssignWorkResults{}
	m.AssignWorkToWorker(addressWorker1, args, reply)

	args = &common.AssignWorkArgs{ImageName: "alpine: 2"}
	m.AssignWorkToWorker(addressWorker2, args, reply)

	args = &common.AssignWorkArgs{ImageName: "alpine: 3"}
	m.AssignWorkToWorker(addressWorker3, args, reply)

	fmt.Printf("worker 1 given work image: %s \n", w1.DockerImage)
	fmt.Printf("worker 2 given work image: %s \n", w2.DockerImage)
	fmt.Printf("worker 2 given work image: %s \n", w3.DockerImage)

	// close all resources manually
	w1.StopWorkerRPC()
	w2.StopWorkerRPC()
	w3.StopWorkerRPC()
	m.StopManagerRPC()
	c.StopClientRPC()

	fmt.Println("program exited from main with all resources cleaned up")
}
