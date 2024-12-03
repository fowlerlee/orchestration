package worker

import (
	"log"
	"reflect"
	"testing"

	"github.com/fowlerlee/orchestration/manager"
)

func TestWorkerStartStop(t *testing.T) {
	localhost := "localhost:"
	addressManager := localhost + "8081"
	m := manager.MakeManager(addressManager)
	m.StartManagerRPC()

	addressWorker1 := localhost + "8082"
	addressWorker2 := localhost + "8083"
	addressWorker3 := localhost + "8084"
	w1 := CreateWorker(addressWorker1)
	w1.RegisterWithManager(addressManager)
	w2 := CreateWorker(addressWorker2)
	w2.RegisterWithManager(addressManager)
	w3 := CreateWorker(addressWorker3)
	w3.RegisterWithManager(addressManager)

	w1.initKVStore()
	w2.initKVStore()
	w1.SetKV("1", "lee")
	w1.saveToFile()
	w2.SetKV("2", "Jack")
	w2.saveToFile()

	// test workers: w1 and w3
	w3.ReplicateKVStores()
	val, ok := w1.GetKV("1")
	w3.loadFromFile()
	result, okResult := w3.GetKV("1") // FIXME: error in reading from file for worker 8084, both vals in file exist=true
	if !ok && !okResult {
		log.Fatalf("failed to get the value")
	}
	if !reflect.DeepEqual(val, result) {
		log.Fatalf("Failed to replicate data")
	}

	// test workers: w2 and w3
	val, ok = w2.GetKV("2")
	result, okResult = w3.GetKV("2") 
	if !ok && !okResult {
		log.Fatalf("failed to get the value")
	}
	if !reflect.DeepEqual(val, result) {
		log.Fatalf("Failed to replicate data")
	}


	// shutdown registered workers and self
	m.StopManagerRPC()



}
