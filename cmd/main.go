package main

import (
	// "fmt"
	"fmt"
	"log"
	"time"

	"github.com/fowlerlee/orchestration/worker"
)

func main() {
	w := worker.NewNeonStore()
	acc := &worker.Account{
		FirstName: "Lee",
		LastName:  "Fowler",
		Number:    123456,
		EncryptedPassword: "hsoihsdfonsd",
		Balance:   200,
		CreatedAt: time.Now(),
	}
	w.CreateAccount(acc)

	time.Sleep(1 * time.Second)

	acc = &worker.Account{
		FirstName: "Josefin",
		LastName:  "Vestman",
		EncryptedPassword: "cldhoshnsond",
		Number:    54321,
		Balance:   799,
		CreatedAt: time.Now(),
	}
	w.CreateAccount(acc)

	time.Sleep(1 * time.Second)

	account, err := w.GetAccountByName(54321)
	if err != nil {
		log.Printf("error getting account: %v", err)
		return
	}
	fmt.Printf("found account: %+v\n", account)
}
