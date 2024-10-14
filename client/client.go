package client

import (
	"fmt"
	"net"
	"net/rpc"
	"os"

	"github.com/fowlerlee/orchestration/common"
	uuid "github.com/google/uuid"
)

type CState int

const (
	AssignTask = iota
	Idle
)

type Client struct {
	ID       uuid.UUID
	address  string
	Queue    common.Queue
	shutdown chan struct{}
	State    CState
	l        net.Listener
}

func MakeClient(address string) *Client {
	c := new(Client)
	c.address = address
	c.ID = uuid.New()
	c.Queue = common.Queue{Items: make([]string, 5)}
	c.shutdown = make(chan struct{}, 1)
	c.State = Idle
	return c
}

func (c *Client) StartClientRPC() {
	rpcs := rpc.NewServer()
	err := rpcs.Register(c)
	if err != nil {
		fmt.Errorf("failed to register client to the rpc: %v", err)
	}
	os.Remove(c.address)
	l, err := net.Listen("tcp", c.address)
	if err != nil {
		fmt.Errorf("failed to create listener for the client server")
	}
	c.l = l

	go func() {
	loop:
		for {
			select {
			case <-c.shutdown:
				break loop
			default:
			}
			conn, err := c.l.Accept()
			if err == nil {
				go func() {
					rpcs.ServeConn(conn)
					conn.Close()
				}()
			} else {
				fmt.Errorf("failed to accept request from the manager: %v\n", err)
			}
			fmt.Println("client successfully handled the RPC call")
		}
	}()
}

func (c *Client) AssignWorkToManager(address string,
	args *common.ClientManagerArgs,
	reply *common.ClientManageResult) error {

	fmt.Printf("attempting to connect to the manager from address %v\n", c.address)
	clientrpc, err := rpc.Dial("tpc", address)
	if err != nil {
		return fmt.Errorf("error dialing ")
	}
	defer clientrpc.Close()

	err = clientrpc.Call("Manager.GiveManagerWork", args, reply)
	if err != nil {
		return fmt.Errorf("rpc call to Manager.GiveManagerWork failed: %v\n", err)
	}
	return nil
}

func (c *Client) SendWorkToManager() {
	work := []string{"alpine 1", "alpine 2", "alpine 3"}
	c.Queue.Items = append(c.Queue.Items, work...)
}

func (client *Client) StopClientRPC() error {
	reply := &common.ClientShutdownReply{}
	args := &common.ClientShutdownArgs{}

	rpcClient, err := rpc.Dial("tcp", client.address)
	if err != nil {
		return err
	}
	err = rpcClient.Call("Client.Shutdown", args, reply)
	if err != nil {
		return err
	}
	return nil
}

func (c *Client) Shutdown(args *common.ClientShutdownArgs, reply *common.ClientShutdownReply) error {
	c.shutdown <- struct{}{}
	close(c.shutdown)
	c.l.Close()
	fmt.Println("client was stopped and cleaned up")
	return nil
}
