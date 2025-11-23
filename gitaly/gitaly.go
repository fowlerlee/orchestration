package gitaly


import (
	"fmt"
	"net"
	"net/rpc"
	"os"
	"sync"

	"github.com/google/uuid"
	"log"
	"github.com/fowlerlee/orchestration/common"
	
)

type Gitaly struct {
	sync.Mutex
	Address string
	Listener net.Listener
	Shutdown chan struct{}
	Workers []string
	WorkerTaskMap map[string][]uuid.UUID
	WorkerBackups map[string][][]byte
	WorkerIPAddressMap map[string]string
	WorkerIPAddressLock sync.Mutex
	WorkerIPAddressMapLock sync.Mutex

}

func CreateGitaly(address string) *Gitaly {
	gitaly := &Gitaly{
		Address: address,
		Listener: nil,
		Shutdown: make(chan struct{}),
		Workers: make([]string, 0),
		WorkerTaskMap: make(map[string][]uuid.UUID),
		WorkerBackups: make(map[string][][]byte),
		WorkerIPAddressMap: make(map[string]string),
		WorkerIPAddressLock: sync.Mutex{},
		WorkerIPAddressMapLock: sync.Mutex{},
	}
	return gitaly
}

func (g *Gitaly) StartGitalyRPC() {
	rpcs := rpc.NewServer()
	errX := rpcs.Register(g)
	if errX != nil {
		log.Fatalf("failed to register gitaly with rpc server: %v", errX)
	}
	os.Remove(g.Address)
	l, err := net.Listen(common.Protocol, g.Address)
	if err != nil {
		log.Fatalf("gitaly RPC server not initiated: %v", err)
	}
	g.Listener = l
	fmt.Println("gitaly rpc seems to be live!")

	go func() {
	loop:
		for {
			select {
			case <-g.Shutdown:
				break loop
			default:
			}
			conn, err := g.Listener.Accept()
			if err == nil {
				go func() {
					rpcs.ServeConn(conn)
					conn.Close()
				}()
			} else {
				fmt.Printf("error accepting request from client, %v", err)
			}
			fmt.Println("worker successfully handled RPC call")
		}
	}()
}