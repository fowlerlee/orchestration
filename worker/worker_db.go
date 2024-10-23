package worker

import (
	"database/sql"
	"fmt"
	"log"
	"os"
	"strings"
	"time"

	"github.com/joho/godotenv"
	_ "github.com/lib/pq"
)

type NeonStore struct {
	db *sql.DB
}

func NewNeonStore() *NeonStore {
	err := godotenv.Load(".env")
	if err != nil {
		log.Fatal("error loading .env file")
	}
	host := os.Getenv("DB_HOST")
	user := os.Getenv("DB_USER")
	password := os.Getenv("DB_PASSWORD")
	dbname := os.Getenv("DB_NAME")
	_ = os.Getenv("DB_PORT") //keep for own postgres

	connStr := fmt.Sprintf("postgresql://%s:%s@%s/%s?sslmode=require", user, password, host, dbname)
	db, err := sql.Open("postgres", connStr)
	if err != nil {
		fmt.Println("failed to open DB connection")
	}

	fmt.Printf("connect string: %s", connStr)

	neon := new(NeonStore)
	neon.db = db
	if err := neon.initTable(); err != nil {
		fmt.Printf("failed to initialize the tables: %v \n", err)
	}
	return neon
}

func (neon *NeonStore) CloseNeonConnection() error {
	if err := neon.db.Close(); err != nil {
		return fmt.Errorf("failed to close neondb connection: %v ", err)
	}
	return nil
}

func (neon *NeonStore) initTable() error {
	if err := neon.createAccountTable(); err != nil {
		return fmt.Errorf("failed to create a table for accounts: %v \n", err)
	}
	var version string
	if err := neon.db.QueryRow("select version()").Scan(&version); err != nil {
		panic(err)
	}
	fmt.Printf("neon version: %s", version)
	return nil
}

func (neon *NeonStore) createAccountTable() error {
	query := `create table if not exists account (
		id serial primary key,
		first_name varchar(100),
		last_name varchar(100), 
		number serial,
		encrypted_password varchar(100),
		balance serial,
		created_at timestamp
	)`
	_, err := neon.db.Exec(query)
	return err
}

type Account struct {
	FirstName         string
	LastName          string
	Number            int
	EncryptedPassword string
	Balance           int
	CreatedAt         time.Time
}

func (neon *NeonStore) CreateAccount(acc *Account) error {
	query := `INSERT INTO account (
		first_name, last_name, number, encrypted_password,
		balance, created_at)
		values ($1, $2, $3, $4, $5, $6)`

	_, err := neon.db.Exec(
		query,
		acc.FirstName,
		acc.LastName,
		acc.Number,
		acc.EncryptedPassword,
		acc.Balance,
		acc.CreatedAt)

	if err != nil {
		return fmt.Errorf("failed to insert an Account: %v\nQuery: %s\nValues: %+v", err, query, acc)
	}
	return nil
}

func (neon *NeonStore) GetAccountByNumber(number int) (*Account, error) {
	var acc Account
	query := "SELECT first_name, last_name, number, encrypted_password, balance, created_at FROM account where number = $1"
	err := neon.db.QueryRow(query, number).Scan(
		&acc.FirstName,
		&acc.LastName,
		&acc.Number,
		&acc.EncryptedPassword,
		&acc.Balance,
		&acc.CreatedAt,
	)
	if err != nil {
		if err == sql.ErrNoRows {
			return nil, fmt.Errorf("no account found with first name: %v", number)
		}
		return nil, fmt.Errorf("error querying account: %v", err)
	}
	return &acc, nil
}

func (neon *NeonStore) DelecteAccount(firstname string) error {
	if _, err := neon.db.Exec("DELETE FROM account where first_name = $1", firstname); err != nil {
		return fmt.Errorf("failed to delete Account with first name %v", err)
	}
	return nil
}

func (neon *NeonStore) UpdateAccountForNumber(number int, update *Account) error {
	query := `UPDATE account 
		SET first_name = $1, last_name = $2, encrypted_password = $3, balance = $4
		WHERE number = $5`

	result, err := neon.db.Exec(query,
		update.FirstName,
		update.LastName,
		update.EncryptedPassword,
		update.Balance,
		number)

	if err != nil {
		return fmt.Errorf("failed to update account: %v", err)
	}

	rowsAffected, err := result.RowsAffected()
	if err != nil {
		return fmt.Errorf("error getting rows affected: %v", err)
	}

	if rowsAffected == 0 {
		return fmt.Errorf("no account found with number: %v", number)
	}
	return nil
}

func (neon *NeonStore) CreateIndexFor(columnName string) error {
	query := fmt.Sprintf("CREATE INDEX IF NOT EXISTS idx_%s ON account (%s)", columnName, columnName)

	_, err := neon.db.Exec(query)
	if err != nil {
		return fmt.Errorf("error creating index for column %s: %v", columnName, err)
	}
	return nil
}

type BalanceInfo struct {
	Balance   int
	FirstName string
}

func (neon *NeonStore) GetBalanceForUsersInXOrder(order string) ([]BalanceInfo, error) {
	
	orderUpper := strings.ToUpper(order)
	if orderUpper != "ASC" && orderUpper != "DESC" {
		return nil, fmt.Errorf("given order is not valid: %s", order)
	}
	
	query := fmt.Sprintf("SELECT first_name, balance FROM account GROUP BY balance, first_name ORDER BY balance %s", orderUpper)
	rows, err := neon.db.Query(query)
	if err != nil {
		return nil, fmt.Errorf("error querying accounts: %v", err)
	}
	defer rows.Close()

	var balanceInfos []BalanceInfo
	for rows.Next() {
		var bi BalanceInfo
		err := rows.Scan(&bi.FirstName, &bi.Balance)
		if err != nil {
			return nil, fmt.Errorf("error scanning balance info row: %v", err)
		}
		balanceInfos = append(balanceInfos, bi)
	}

	if err = rows.Err(); err != nil {
		return nil, fmt.Errorf("error iterating balance info rows: %v", err)
	}

	return balanceInfos, nil
}
