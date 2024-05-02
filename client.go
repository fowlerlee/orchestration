package main

import (
	Q "github.com/golang-collections/collections/queue"
	uuid "github.com/google/uuid"
)

type Client struct {
	ID         uuid.UUID
	Queue      Q.Queue
	Channel chan string
}
