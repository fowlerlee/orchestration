package manager

import (
	"fmt"
	"log"
	"net"
	"net/rpc"
	"os"
	"sync"

	"github.com/fowlerlee/orchestration/common"
	"github.com/google/uuid"
)

type MState int

const (
	Ready MState = iota + 1
	Busy
	JobComplete
)

type Manager struct {
	sync.Mutex
	address         string
	doneChannel     chan bool
	ID              uuid.UUID
	Queue           common.Queue
	RegisterChannel chan string
	Workers         []string
	WorkerTaskMap   map[string][]uuid.UUID
	State           MState
	l               net.Listener
	shutdown        chan struct{}
}

func MakeManager(address string) *Manager {
	return &Manager{
		address:         address,
		ID:              uuid.New(),
		Queue:           common.Queue{Items: make([]string, 5)},
		RegisterChannel: make(chan string),
		Workers:         make([]string, 0, 5),
		WorkerTaskMap:   make(map[string][]uuid.UUID),
		State:           Ready,
		shutdown:        make(chan struct{}, 1),
	}
}

func (m *Manager) Register(args *common.RegisterArgs, reply *common.RegisterResult) error {
	m.Lock()
	defer m.Unlock()
	m.Workers = append(m.Workers, args.WorkerAddress)
	go func() {
		m.RegisterChannel <- args.WorkerAddress
	}()
	fmt.Printf("WORKER %v registered with the MANAGER", args.WorkerAddress)
	reply.Success = true
	return nil
}

func (m *Manager) StartManagerRPC() {
	rpcs := rpc.NewServer()
	errX := rpcs.Register(m)
	if errX != nil {
		fmt.Println("failed to register manager with rpc server")
	}
	os.Remove(m.address)
	l, err := net.Listen(common.Protocol, m.address)
	if err != nil {
		log.Fatalf("manager RPC Server not created at %v", m.address)
	}
	m.l = l
	fmt.Println("manager rpc seems to be live!")

	go func() {
	loop:
		for {
			select {
			case <-m.shutdown:
				break loop
			default:
			}
			conn, err := m.l.Accept()
			if err == nil {
				go func() {
					rpcs.ServeConn(conn)
					conn.Close()
				}()
			} else {
				fmt.Printf("error accepting request from client: %v", err)
			}
			fmt.Println("manager successfully handled RPC call")
		}
	}()
}

func (m *Manager) AssignWorkToWorker(address string, args *common.AssignWorkArgs, reply *common.AssignWorkResults) error {
	fmt.Printf("attempting to connect to worker at address: %s\n", address)
	rpcName := "Worker.AssignWork"

	ok := common.RpcCall(address, rpcName, args, reply)
	if !ok {
		return fmt.Errorf("failed to call the %v rpc method", rpcName)
	}
	return nil
}

// manager stops the workers that are registered to it
func (m *Manager) StopManagerRPC() error {
	err := m.stopWorkers()
	if err != nil {
		return err
	}
	reply := &common.MasterShutdownReply{}
	args := &common.MasterShutdownArgs{}
	rpcMethod := "Manager.Shutdown"

	ok := common.RpcCall(m.address, rpcMethod, args, reply)
	if !ok {
		return fmt.Errorf("failed to call the %v rpc method \n", rpcMethod)
	}
	return nil
}

func (m *Manager) Shutdown(args *common.MasterShutdownReply, reply *common.MasterShutdownArgs) error {

	// todo - get workers ip address then close resources
	m.shutdown <- struct{}{}
	close(m.shutdown)

	m.l.Close()
	fmt.Println("manager was stopped and cleaned up")
	return nil
}

func (m *Manager) stopWorkers() error {
	args := &common.WorkerShutdownArgs{}
	reply := &common.WorkerShutdownReply{}
	for _, v := range m.Workers {
		ok := common.RpcCall(v, "Worker.Shutdown", args, reply)
		if !ok {
			return fmt.Errorf("failed to shutdown Worker at: %v \n", v)
		}
	}
	return nil
}

func (m *Manager) GiveManagerWork(args *common.ClientManagerArgs, reply *common.ClientManageResult) error {
	m.Queue.Items = append(m.Queue.Items, args.JobName)
	reply.Reply = args.JobName
	reply.StatusCode = 200
	return nil
}
