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

type wState int

const (
	Unrecovered wState = iota + 1
	Waiting
	Recovered
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
	AllWorkerAddresses []string
	ID                 uuid.UUID
	Queue              common.Queue
	Channel            chan string
	State              wState
	D                  Docker
	DockerImage        string
	Address            string
	l                  net.Listener
	managerIP          string
	shutdown           chan struct{}
	kVStore            map[string]interface{}
	storageFile        string
	EncodedData        [][]byte
}

func CreateWorker(address string) (wk *Worker) {
	wk = new(Worker)
	wk.Channel = make(chan string)
	wk.ID = uuid.New()
	wk.State = Unrecovered
	wk.Queue = common.Queue{Items: make([]string, 0, 5)}
	wk.Address = address
	wk.shutdown = make(chan struct{}, 1)
	wk.initKVStore()
	wk.loadFromFile()
	return
}

func (w *Worker) initKVStore() {
	w.kVStore = make(map[string]interface{})
	tempDir := os.TempDir()
	w.storageFile = filepath.Join(tempDir, fmt.Sprintf("worker_%s_store.json", w.Address))

	err := w.loadFromFile()
	if err != nil {
		if os.IsNotExist(err) {
			recoverErr := w.RecoverDataFromManager()
			if recoverErr != nil {
				log.Printf("failed to recover data from manager: %v", recoverErr)
				w.kVStore = make(map[string]interface{})
			}
		} else {
			log.Printf("error loading from file: %v", err)
			w.kVStore = make(map[string]interface{})
		}
	}
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

func (w *Worker) GetKV(key string) (any, bool) {
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
	w.managerIP = address
	args := &common.RegisterArgs{WorkerAddress: w.Address}
	reply := &common.RegisterResult{}
	rpcName := "Manager.Register"
	ok := common.RpcCall(address, rpcName, args, reply)
	if !ok {
		return fmt.Errorf("failed to call %v rpc method", rpcName)
	}
	return nil
}

func (w *Worker) Shutdown(args *common.WorkerShutdownArgs, reply *common.WorkerShutdownReply) error {
	w.Lock()
	defer w.Unlock()

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
	wk.Lock()
	defer wk.Unlock()
	wk.DockerImage = args.ImageName
	wk.ContainerCreate(wk.ctx)
	result.WorkIsGiven = true
	fmt.Printf("work was assigned to the Worker at %v\n", wk.Address)
	return nil
}

func (w *Worker) getListOfWorkersKVStores() []string {
	args := &common.WorkerIPAddressArgs{}
	reply := &common.WorkerIPAddressResult{}
	rpcName := "Manager.GetListOfWorkersIP"
	ok := common.RpcCall(w.managerIP, rpcName, args, reply)
	if !ok {
		fmt.Printf("failed to call the %v rpc method", rpcName)
	}
	w.AllWorkerAddresses = reply.WorkersIP
	fmt.Println("GOT ALL WORKER ADDRESSES from MANAGER")
	return w.AllWorkerAddresses
}

func (w *Worker) RequestData(args *common.BackupDataArgs, reply *common.BackupDataReply) error {
	w.Lock()
	defer w.Unlock()
	info, err := json.Marshal(w.kVStore)
	if err != nil {
		return fmt.Errorf("failed to marshall the kvStore data for the worker: %s", w.Address)
	}
	reply.EncodedData = info
	reply.Success = true
	return nil
}

func (w *Worker) ReplicateKVStores() error {
	destinationFileName := filepath.Join(os.TempDir(), fmt.Sprintf("worker_%s_store.json", w.Address))
	destinationFile, err := os.Create(destinationFileName)
	if err != nil {
		fmt.Println("Failed to created destination file for Worker")
	}
	defer destinationFile.Close()

	workersKVStores := w.getListOfWorkersKVStores()
	for _, v := range workersKVStores {
		if w.Address != v {
			// send msg to workers
			rpcName := "Worker.RequestData"
			args := &common.BackupDataArgs{}
			reply := &common.BackupDataReply{}

			ok := common.RpcCall(v, rpcName, args, reply)
			if !ok {
				return fmt.Errorf("failed to call the %v rpc method", rpcName)
			}
			// get back msg from workers
			json.Unmarshal(reply.EncodedData, &w.kVStore)
			// write data into this Workers KVstore
			// !! FIXME: can delete the below !!
			// path := filepath.Join(os.TempDir(), fmt.Sprintf("worker_%s_store.json", v))
			// file, err := os.OpenFile(path, os.O_RDWR, 0644)
			// if err != nil {
			// 	return err
			// }
			// defer file.Close()
			// fmt.Printf("replicate worker %v KVStore by handling file: %v \n", k, file)

			// write
			_, err = destinationFile.Write(reply.EncodedData)
			if err != nil {
				fmt.Println("Error writing to the destination file")
			}
		}
	}
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
