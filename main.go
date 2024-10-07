package main

import (
	"fmt"

	"strconv"

	"github.com/fowlerlee/orchestration/manager"
	"github.com/golang-collections/collections/queue"
	"github.com/google/uuid"
)

func main() {
	fmt.Println("running main")

	sharedChan := make(chan string, 10)

	manager := &manager.Manager{
		ID:              uuid.New(),
		Queue:           queue.Queue{},
		RegisterChannel: sharedChan,
		State:           manager.MState(manager.Ready),
	}

	client := &Client{
		ID:      uuid.New(),
		Queue:   *queue.New(),
		Channel: sharedChan,
		State:   AssignTask,
	}

	manager.SendMessagesToWorkers([]string{"sms1", "sms2", "sms3"})
	fmt.Println("value ‰v ", manager)

	readChan := client.Channel

	for _, v := range <-readChan {
		fmt.Println("Print out messages received")
		fmt.Printf("value :%s ", strconv.QuoteRune(v))
	}
}
