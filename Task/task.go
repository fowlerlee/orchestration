package task

import (
	"context"
	"fmt"
	"time"

	"github.com/docker/docker/api/types/container"
	"github.com/docker/docker/client"
	Q "github.com/golang-collections/collections/queue"
	"github.com/google/uuid"
)

type TaskEvent struct {
	ID uuid.UUID
	State fmt.State
	TimeStamp time.Time
	task Task
}

type Task struct {
	id     uuid.UUID
	Name string
	
	
}
