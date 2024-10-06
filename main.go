package main

import (
	"fmt"

	"github.com/golang-collections/collections/queue"
	"github.com/google/uuid"
	"strconv"
)

func main() {
	fmt.Println("running main")

	sharedChan := make(chan string, 3)

	manager := &Manager {
		ID:      uuid.New(),
		Queue:   queue.Queue{},
		Channel: sharedChan,
		State: Ready,
	}

	client := &Client{
		ID: uuid.New(),
		Queue: *queue.New(),
		Channel: sharedChan,
		State: AssignTask,
	}


	manager.SendMessagesToWorkers([]string {"sms1", "sms2", "sms3"})
	fmt.Println("value ‰v ", manager)

	readChan := client.Channel

	for _, v := range <-readChan {
		fmt.Println("Print out messages received")
		fmt.Printf("value :%s ",  strconv.QuoteRune(v))
	}
}
