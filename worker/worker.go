package worker

import (
	"context"
	"encoding/json"
	"fmt"
	"log"
	"net"
	"net/rpc"
	"os"
	"path/filepath"

	"sync"

	"github.com/fowlerlee/orchestration/common"
	"github.com/google/uuid"
)

type wState string

const (
	Waiting wState = "1"
	Working wState = "2"
)

// Config holds configuration for the worker node
type Config struct {
	Name          string
	Cmd           []string
	Memory        int64
	Disk          int64
	Env           []string
	RestartPolicy string
	Image         string
}

type Docker struct {
	Config Config
}

type Worker struct {
	ctx context.Context
	sync.Mutex
	ID          uuid.UUID
	Queue       common.Queue
	Channel     chan string
	State       wState
	D           Docker
	DockerImage string
	Address     string
	l           net.Listener
	shutdown    chan struct{}
	kVStore     map[string]string
	storageFile string
}

func CreateWorker(address string) (wk *Worker) {
	wk = new(Worker)
	wk.Channel = make(chan string)
	wk.ID = uuid.New()
	wk.State = Waiting
	wk.Queue = common.Queue{Items: make([]string, 0, 5)}
	wk.Address = address
	wk.shutdown = make(chan struct{}, 1)
	wk.initKVStore()
	wk.loadFromFile()
	return
}

func (w *Worker) initKVStore() {
	w.kVStore = make(map[string]string)
	tempDir := os.TempDir()
	w.storageFile = filepath.Join(tempDir, fmt.Sprintf("worker_%s_store.json", w.ID))

}

func (w *Worker) SetKV(key, value string) error {
	w.Lock()
	defer w.Unlock()
	w.kVStore[key] = value
	err := w.saveToFile()
	if err != nil {
		return fmt.Errorf("failed to save KVStore to file")
	}
	return nil
}

func (w *Worker) GetKV(key string) (string, bool) {
	w.Lock()
	defer w.Unlock()
	value, exists := w.kVStore[key]
	return value, exists
}

func (w *Worker) Delete(key string) {
	w.Lock()
	defer w.Unlock()
	delete(w.kVStore, key)
	w.saveToFile()
}

func (w *Worker) saveToFile() error {
	data, err := json.Marshal(w.kVStore)
	if err != nil {
		return fmt.Errorf("error performing json marshalling of kvstore")
	}
	return os.WriteFile(w.storageFile, data, 0644)
}

func (w *Worker) loadFromFile() error {
	data, err := os.ReadFile(w.storageFile)
	if err != nil {
		if os.IsNotExist(err) {
			return nil
		}
		return err
	}
	return json.Unmarshal(data, &w.kVStore)
}

func (w *Worker) CleanupKVStore() {
	os.Remove(w.storageFile)
}

func (w *Worker) StartWorkerRPC() {
	rpcs := rpc.NewServer()
	errX := rpcs.Register(w)
	if errX != nil {
		log.Fatalf("failed to register worker with rpc server: %v", errX)
	}
	os.Remove(w.Address)
	l, err := net.Listen(common.Protocol, w.Address)
	if err != nil {
		log.Fatalf("worker RPC server not initiated: %v", err)
	}
	w.l = l
	fmt.Println("worker rpc seems to be live!")

	go func() {
	loop:
		for {
			select {
			case <-w.shutdown:
				break loop
			default:
			}
			conn, err := w.l.Accept()
			if err == nil {
				go func() {
					rpcs.ServeConn(conn)
					conn.Close()
				}()
			} else {
				fmt.Printf("error accepting request from client, %v", err)
			}
			fmt.Println("worker successfully handled RPC call")
		}
	}()
}

func (w *Worker) StopWorkerRPC() error {
	args := &common.WorkerShutdownArgs{}
	reply := &common.WorkerShutdownReply{}
	rpcName := "Worker.Shutdown"

	ok := common.RpcCall(w.Address, rpcName, args, reply)
	if !ok {
		return fmt.Errorf("failed to call %v rpc method", rpcName)
	}
	return nil
}

func (w *Worker) RegisterWithManager(address string) error {
	w.Lock()
	defer w.Unlock()
	args := &common.RegisterArgs{WorkerAddress: w.Address}
	reply := &common.RegisterResult{}
	rpcName := "Manager.Register"
	ok := common.RpcCall(address, rpcName, args, reply)
	if !ok {
		return fmt.Errorf("failed to call %v rpc method\n", rpcName)
	}
	return nil
}

func (w *Worker) Shutdown(args *common.WorkerShutdownArgs, reply *common.WorkerShutdownReply) error {
	w.shutdown <- struct{}{}
	close(w.shutdown)
	w.l.Close()
	w.CleanupKVStore()
	fmt.Printf("worker at address %v was stopped and cleaned up\n", w.Address)
	return nil
}

type DockerResult struct {
	Error       error
	Action      string
	ContainerId string
	Result      string
}

func (wk *Worker) AssignWork(args *common.AssignWorkArgs, result *common.AssignWorkResults) error {
	wk.Mutex.Lock()
	defer wk.Mutex.Unlock()
	wk.DockerImage = args.ImageName
	wk.ContainerCreate(wk.ctx)
	result.WorkIsGiven = true
	fmt.Printf("work was assigned to the Worker at %v\n", wk.Address)
	return nil
}

func (w *Worker) Run() DockerResult {
	// func to use Docker containers
	return DockerResult{Result: "performed an image pull"}
}

func (w *Worker) ContainerCreate(ctx context.Context) bool {
	fmt.Println("create container for the worker and do Task")
	// func to create Docker container from image
	return true
}
