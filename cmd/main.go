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
		FirstName:         "Cate",
		LastName:          "Becks",
		Number:            345345,
		EncryptedPassword: "dsdhrthsfgb",
		Balance:           180,
		CreatedAt:         time.Now(),
	}
	w.CreateAccount(acc)

	time.Sleep(1 * time.Second)

	acc = &worker.Account{
		FirstName:         "Pete",
		LastName:          "Cooty",
		EncryptedPassword: "dfgdfbdyfgn",
		Number:            4654756,
		Balance:           900,
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

	// acc = &worker.Account{
	// 	FirstName:         "Jake",
	// 	LastName:          "Cupid",
	// 	EncryptedPassword: "hdfhdfhd",
	// 	Number:            34344543,
	// 	Balance:           500,
	// 	CreatedAt:         time.Now(),
	// }

	// w.UpdateAccountForNumber(123252, acc)

	data, err := w.GetBalanceForUsersInXOrder("ASC")
	if err != nil {
		fmt.Printf("error occured getting the balances: %s", err)
	}

	for _, val := range data {
		fmt.Printf("Name: %s\t Balance: %d\n", val.FirstName, val.Balance)
	}
}
