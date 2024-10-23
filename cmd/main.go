package main

import (
	"fmt"
	"log"
	"time"

	"github.com/fowlerlee/orchestration/worker"
)

func main() {
	w := worker.NewNeonStore()
	acc := &worker.Account{
		FirstName:         "James",
		LastName:          "Kat",
		Number:            223232,
		EncryptedPassword: "dfgdfgdf",
		Balance:           2000,
		CreatedAt:         time.Now(),
	}
	w.CreateAccount(acc)

	time.Sleep(1 * time.Second)

	acc = &worker.Account{
		FirstName:         "Luke",
		LastName:          "Matick",
		EncryptedPassword: "sdfsdsdsdfdf",
		Number:            4346346346,
		Balance:           1200,
		CreatedAt:         time.Now(),
	}
	w.CreateAccount(acc)

	time.Sleep(1 * time.Second)

	account, err := w.GetAccountByNumber(54321)
	if err != nil {
		log.Printf("error getting account: %v", err)
		return
	}
	fmt.Printf("found account: %+v\n", account)

	acc = &worker.Account{
		FirstName:         "Jake",
		LastName:          "Cupid",
		EncryptedPassword: "hdfhdfhd",
		Number:            34344543,
		Balance:           500,
		CreatedAt:         time.Now(),
	}

	w.UpdateAccountForNumber(123252, acc)
}
