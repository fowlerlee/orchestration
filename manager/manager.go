package manager

import (
	"encoding/json"
	"fmt"
	"net"
	http "net/http"
	"sync"

	"github.com/fowlerlee/orchestration/common"
	Q "github.com/golang-collections/collections/queue"
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
	Queue           Q.Queue
	RegisterChannel chan string
	Workers         []string
	WorkerTaskMap   map[string][]uuid.UUID
	State           MState
	l               net.Listener
}

func MakeManager(address string) *Manager {
	return &Manager{
		address:         address,
		ID:              uuid.New(),
		Queue:           Q.Queue{},
		RegisterChannel: make(chan string),
		Workers:         make([]string, 5),
		WorkerTaskMap:   make(map[string][]uuid.UUID),
		State:           Ready,
	}
}

func (m *Manager) Register(args *common.RegisterArgs, reply *int) error {
	m.Workers = append(m.Workers, args.WorkerName)
	*reply = 200
	return nil
}

func (m *Manager) GiveManagerWork(args *common.DoTaskArgs, reply *common.ResultArgs) error {
	m.Queue.Enqueue(args)
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
