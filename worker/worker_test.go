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
	// addressWorker2 := localhost + "8083"
	addressWorker3 := localhost + "8084"
	w1 := CreateWorker(addressWorker1)
	w1.RegisterWithManager(addressManager)
	// w2 := CreateWorker(addressWorker2)
	w3 := CreateWorker(addressWorker3)
	w3.RegisterWithManager(addressManager)


	w1.initKVStore()
	w1.SetKV("1", "lee")
	// w2.SetKV("2", "Jack")

	w3.ReplicateKVStores()
	val, ok := w1.GetKV("1")
	result, okResult := w3.GetKV("1") // result is not correctly read, #FIXME
	if !ok && !okResult {
		log.Fatalf("failed to get the value")
	}
	if !reflect.DeepEqual(val, result) {
		log.Fatalf("Failed to replicate data")
	}

	// test the second worker ...

}
