package common

import (
	"fmt"
	"net/rpc"
	"sync"
)

const (
	Protocol = "tcp"
)

type LogEntry struct {
	Index   int
	Term    int
	Command string
}

type DoTaskArgs struct {
	JobName    string
	TaskNumber int
}

type RegisterArgs struct {
	WorkerAddress string
}

type RegisterResult struct {
	Success bool
}

type ResultArgs struct {
	JobName    string
	StatusCode int
}

type AssignWorkArgs struct {
	ImageName string
}

type AssignWorkResults struct {
	WorkIsGiven bool
}

type MasterShutdownArgs struct {
}

type MasterShutdownReply struct {
	Shutdown bool
}

type WorkerShutdownArgs struct {
}

type WorkerShutdownReply struct {
	Shutdown bool
}

type ClientManagerArgs struct {
	JobName string
}

type ClientManageResult struct {
	Reply      string
	StatusCode int
}

type ClientShutdownArgs struct {
}

type ClientShutdownReply struct {
	Shutdown bool
}

// type KVArgs struct {
// 	Input string
// }

// type KVResults struct {
// 	WorkersIP []string
// }

type WorkerIPAddressArgs struct {
}

type WorkerIPAddressResult struct {
	WorkersIP []string
}

type RequestVoteArgs struct {
	CandidateID string
	CurrentTerm        int
	LogLength int
	LastTerm int
}

type RequestVoteReply struct {
	VoteGranted bool
	Term        int
}

type Queue struct {
	Items []string
	lock  sync.Mutex
}

type WorkerInfoArgs struct {
}

type WorkerInfoReply struct {
	WorkersIPs []string
}

type HeartbeatArgs struct {
	Term     int
	LeaderID string
}

type HeartbeatReply struct {
	Term int
}

type LeaderInfoArgs struct {
	Term int
}

type LeaderInfoReply struct {
	HasLeader bool
	LeaderID  string
	Term      int
}

func (q *Queue) Enqueue(item string) {
	q.lock.Lock()
	defer q.lock.Lock()
	q.Items = append(q.Items, item)
}

func (q *Queue) Dequeue() (string, bool) {
	q.lock.Lock()
	defer q.lock.Unlock()
	if len(q.Items) == 0 {
		return "", false
	}
	item := q.Items[0]
	q.Items = q.Items[1:]
	return item, true
}

func RpcCall(srv string, rpcname string,
	args interface{}, reply interface{}) bool {
	c, errx := rpc.Dial(Protocol, srv)
	if errx != nil {
		return false
	}
	defer c.Close()

	err := c.Call(rpcname, args, reply)
	if err != nil {
		return false
	}

	fmt.Printf("CALLED RPC %v FROM COMMON \n", rpcname)
	return true
}
