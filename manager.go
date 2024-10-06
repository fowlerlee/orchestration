package main

import (
	"encoding/json"
	"fmt"
	"net"
	http "net/http"
	"sync"

	Q "github.com/golang-collections/collections/queue"
	"github.com/google/uuid"
)

type MState int

const (
	Ready = iota
	Busy
	JobComplete
)

type Manager struct {
	sync.Mutex
	address         string
	doneChannel     chan bool
	ID              uuid.UUID
	Queue           Q.Queue
	registerChannel chan string
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
		registerChannel: make(chan string),
		Workers:         make([]string, 5),
		WorkerTaskMap:   make(map[string][]uuid.UUID),
		State:           Ready,
	}
}

func (m *Manager) Register(args *RegisterArgs, reply *int) error {
	*reply = 200
	return nil
}

func (m *Manager) GiveManagerWork(args *DoTaskArgs, reply *ResultArgs) error {
	m.Queue.Enqueue(args)
	*&reply.JobName = args.JobName
	*&reply.statusCode = 200
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
		if m.registerChannel != nil { // ensure it doesnt panic
			fmt.Printf("sending on channel: %s", i)
			m.registerChannel <- i
		}
	}
	return "Messages sent to workers"
}
