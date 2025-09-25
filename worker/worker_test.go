package worker

import (
	"fmt"
	"log"
	"reflect"
	"testing"

	porc "github.com/anishathalye/porcupine"
	"github.com/fowlerlee/orchestration/manager"
)

type WorkerHarness struct {
	key int
	value int
	op    bool // read = true, write = false
}


var registerModel = porc.Model{

	Init: func() interface{} {
		return 0
	},

	// step function: takes a state, input, and output, and returns whether it
	// was a legal operation, along with a new state
	Step: func(state, input, output interface{}) (bool, interface{}) {
		regInput := input.(WorkerHarness)
		if regInput.op == false {
			return true, regInput.value // always ok to execute a write
		} else {
			readCorrectValue := output == state
			return readCorrectValue, state // state is unchanged
		}
	},
	DescribeOperation: func(input, output interface{}) string {
		inp := input.(WorkerHarness)
		switch inp.op {
		case true:
			return fmt.Sprintf("get() -> '%d'", output.(int))
		case false:
			return fmt.Sprintf("put('%d')", inp.value)
		}
		return "<invalid>" // unreachable
	},
}

func TestWorkerLinearizability(t *testing.T) {

	ops := []porc.Operation{
		{0, WorkerHarness{0,0,true}, 0, 0, 100},
		{1, WorkerHarness{0,0,false}, 25, 100, 75},
		{2, WorkerHarness{0,0,true}, 30, 0, 60},
	}
	res := porc.CheckOperations(registerModel, ops)
	if res != true {
		t.Fatal("expected operations to be linearizable")
	}

	events := []porc.Event{
		{0, porc.CallEvent, WorkerHarness{0,0,false}, 0},
		{1, porc.CallEvent, WorkerHarness{0,0,false}, 1},
		{2, porc.CallEvent, WorkerHarness{0,0,false}, 2},
		{2, porc.ReturnEvent, 0, 2},
		{1, porc.ReturnEvent, 100, 1},
		{0, porc.ReturnEvent, 0, 0},
	}
	res = porc.CheckEvents(registerModel, events)
	if res != true {
		t.Fatal("expected operations to be linearizable")
	}

	ops = []porc.Operation{
		{0, WorkerHarness{0,0,true}, 0, 0, 100},
		{1, WorkerHarness{0,0,true}, 10, 200, 30},
		{2, WorkerHarness{0,0,false}, 40, 0, 90},
	}
	res = porc.CheckOperations(registerModel, ops)
	if res != false {
		t.Fatal("expected operations to not be linearizable")
	}

	// same example as above, but with Event
	events = []porc.Event{
		{0, porc.CallEvent, WorkerHarness{0,0,true}, 0},
		{1, porc.CallEvent, WorkerHarness{0,0,true}, 1},
		{1, porc.ReturnEvent, 200, 1},
		{2, porc.CallEvent, WorkerHarness{0,0,true}, 2},
		{2, porc.ReturnEvent, 0, 2},
		{0, porc.ReturnEvent, 0, 0},
	}
	res = porc.CheckEvents(registerModel, events)
	if res != false {
		t.Fatal("expected operations to not be linearizable")
	}
}

func TestWorkerStartStop(t *testing.T) {
	localhost := "localhost:"
	// manager
	addressManager := localhost + "8081"
	m := manager.MakeManager(addressManager)
	// worker 1
	addressWorker1 := localhost + "8082"
	w1 := CreateWorker(addressWorker1)
	w1.RegisterWithManager(addressManager)
	// worker 2
	addressWorker2 := localhost + "8083"
	w2 := CreateWorker(addressWorker2)
	w2.RegisterWithManager(addressManager)
	// worker 3
	addressWorker3 := localhost + "8084"
	w3 := CreateWorker(addressWorker3)
	w3.RegisterWithManager(addressManager)

	w1.SetKV("1", "lee")
	w1.saveToFile()
	w2.SetKV("2", "Jack")
	w2.saveToFile()

	w3.ReplicateKVStores()
	// test workers: w1 and w3
	val, ok := w1.GetKV("1")
	result, okResult := w3.GetKV("1")
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
