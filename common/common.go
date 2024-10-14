package common

import "sync"

type DoTaskArgs struct {
	JobName    string
	TaskNumber int
}

type RegisterArgs struct {
	WorkerName string
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

type Queue struct {
	Items []string
	lock  sync.Mutex
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
