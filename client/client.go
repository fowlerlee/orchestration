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
	c.Queue = common.Queue{Items: make([]string, 0, 5)}
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
	l, err := net.Listen(common.Protocol, c.address)
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
	rpcMethod := "Manager.GiveManagerWork"

	ok := common.RpcCall(address, rpcMethod, args, reply)
	if !ok {
		return fmt.Errorf("failed call to %v", rpcMethod)
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
	rpcName := "Client.Shutdown"

	ok := common.RpcCall(client.address, rpcName, args, reply)
	if !ok {
		return fmt.Errorf("failed to call %v rpc method", rpcName)
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
