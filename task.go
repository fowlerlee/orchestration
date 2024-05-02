package main

import (
	"fmt"
	"time"

	"github.com/docker/go-connections/nat"
	"github.com/google/uuid"
)

type TaskEvent struct {
	ID        uuid.UUID
	State     fmt.State
	TimeStamp time.Time
	Task      Task
}

// Task represents a unit of work
type Task struct {
	ID           uuid.UUID
	Name         string    `json:"name"`  // Name of the task
	State        TaskState `json:"state"` // Current state of the task
	Image        string
	ExposedPorts nat.PortSet
	PortBindings map[string]string
	StartTime    time.Time
	FinishTime   time.Time
}

// TaskState represents the possible states of a Task
type TaskState int

const (
	Pending TaskState = iota // Task is waiting to be executed
	Running                  // Task is currently running
	Dead                     // Task has finished or encountered an error
)

func (s TaskState) String() string {
	switch s {
	case Pending:
		return "Pending"
	case Running:
		return "Running"
	case Dead:
		return "Dead"
	default:
		return fmt.Sprintf("Unknown state: %d", s)
	}
}
