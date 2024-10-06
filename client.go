package main

import (
	Q "github.com/golang-collections/collections/queue"
	uuid "github.com/google/uuid"
)

type CState int

const (
	AssignTask = iota
	Idle
)

type Client struct {
	ID      uuid.UUID
	Queue   Q.Queue
	Channel chan string
	State   CState
}

func MakeClient() *Client {
	ch := make(chan string)
	return &Client{
		ID:      uuid.New(),
		Queue:   Q.Queue{},
		Channel: ch,
		State:   Idle,
	}
}

func (c *Client) SendWorkToManager() {
	// rpc call to Manager
}
