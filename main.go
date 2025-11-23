package main

import (
	"fmt"
	"os"
	"strings"
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
		// Normalize addresses: if just a port number, prepend "localhost:"
		normalizeAddress := func(addr string) string {
			if addr != "" && !strings.Contains(addr, ":") {
				return localhost + addr
			}
			return addr
		}
		addressClient = normalizeAddress(os.Args[1])
		addressManager = normalizeAddress(os.Args[2])
		addressWorker1 = normalizeAddress(os.Args[3])
		addressWorker2 = normalizeAddress(os.Args[4])
		addressWorker3 = normalizeAddress(os.Args[5])
	}

	m := manager.MakeManager(addressManager)
	// StartManagerRPC() is already called in MakeManager()

	c := client.MakeClient(addressClient)
	c.StartClientRPC()

	w1 := worker.CreateWorker(addressWorker1)
	w2 := worker.CreateWorker(addressWorker2)
	w3 := worker.CreateWorker(addressWorker3)
	// StartWorkerRPC() is already called in CreateWorker()
	if err := w1.RegisterWithManager(addressManager); err != nil {
		fmt.Printf("failed to register worker 1 with manager: %v", err)
	}
	if err := w2.RegisterWithManager(addressManager); err != nil {
		fmt.Printf("failed to register worker 2 with manager: %v", err)
	}
	if err := w3.RegisterWithManager(addressManager); err != nil {
		fmt.Printf("failed to register worker 3 with manager: %v", err)
	}
	if err := w3.RegisterWithManager(addressManager); err != nil {
		fmt.Printf("failed to register worker 3 with manager: %v", err)
	}

	time.Sleep(2 * time.Millisecond)
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

	w1.SetKV("k1", "v1")
	w1.ReplicateKVStores()
	// close all resources manually
	m.StopManagerRPC()
	c.StopClientRPC()

	fmt.Println("program exited from main with all resources cleaned up")
}
