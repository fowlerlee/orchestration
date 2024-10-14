package manager

import (
	"encoding/json"
	"fmt"
	"log"
	"net"
	http "net/http"
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
		Workers:         make([]string, 5),
		WorkerTaskMap:   make(map[string][]uuid.UUID),
		State:           Ready,
		shutdown:        make(chan struct{}, 1),
	}
}

func (m *Manager) Register(args *common.RegisterArgs, reply *int) error {
	m.Lock()
	defer m.Unlock()
	m.Workers = append(m.Workers, args.WorkerName)
	go func() {
		m.RegisterChannel <- args.WorkerName
	}()
	*reply = 200
	return nil
}

func (m *Manager) StartManagerRPC() {
	rpcs := rpc.NewServer()
	errX := rpcs.Register(m)
	if errX != nil {
		fmt.Println("failed to register manager with rpc server")
	}
	os.Remove(m.address)
	l, err := net.Listen("tcp", m.address)
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
			fmt.Println("successfully handled RPC call")
		}
	}()
}

func (m *Manager) AssignWorkToWorker(address string, args *common.AssignWorkArgs, reply *common.AssignWorkResults) error {
	fmt.Printf("attempting to connect to worker at address: %s\n", address)
	c, err := rpc.Dial("tcp", address)
	if err != nil {
		return fmt.Errorf("failed to dial worker: %v", err)
	}
	defer c.Close()

	err = c.Call("Worker.AssignWork", args, reply)
	if err != nil {
		return fmt.Errorf("rpc call to Worker.AssignWork failed: %v", err)
	}
	return nil
}

func (m *Manager) StopManagerRPC() error {
	reply := &common.MasterShutdownReply{}
	args := &common.MasterShutdownArgs{}
	c, err := rpc.Dial("tcp", m.address)
	if err != nil {
		return err
	}
	err = c.Call("Manager.Shutdown", args, reply)
	if err != nil {
		return err
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

func (m *Manager) GiveManagerWork(args *common.DoTaskArgs, reply *common.ResultArgs) error {
	m.Queue.Items = append(m.Queue.Items, args.JobName)
	reply.JobName = args.JobName
	reply.StatusCode = 200
	return nil
}

func submitHandler(w http.ResponseWriter, r *http.Request) {
	// Check request method (optional but recommended)
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Parse request body
	err := r.ParseForm()
	if err != nil {
		http.Error(w, "Failed to parse request body", http.StatusBadRequest)
		return
	}

	// Access form data (replace "data" with the actual field name)
	data := r.FormValue("data")

	// Process the data (replace with your logic)
	result := processData(data)

	// Respond with JSON (or your preferred format)
	response := map[string]interface{}{"message": result}
	w.Header().Set("Content-Type", "application/json")
	err = json.NewEncoder(w).Encode(response)
	if err != nil {
		http.Error(w, "Failed to encode response", http.StatusInternalServerError)
		return
	}
}

// processData function (replace with your actual data processing logic)
func processData(data string) string {
	// Perform actions on the data
	// ...
	return "Data processed successfully!"
}

func (m *Manager) SendMessagesToWorkers(s []string) string {
	for _, i := range s {
		if i == " " || i == "." {
			fmt.Println("The Message from the Manager is empty: ")
		}
		if m.RegisterChannel != nil { // ensure it doesnt panic
			fmt.Printf("sending on channel: %s", i)
			m.RegisterChannel <- i
		}
	}
	return "Messages sent to workers"
}
