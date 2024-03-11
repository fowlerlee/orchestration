package client

import (
	Q "github.com/golang-collections/collections/queue"
	uuid "github.com/google/uuid"
)

type Client struct {
	id         uuid.UUID
	sendStream chan<- string
	queue      Q.Queue
}
