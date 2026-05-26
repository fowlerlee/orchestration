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
	// IONIA-specific fields
	Type  string // message type: write, apply, order, etc.
	Value int    // value for write/apply operations
	From  string // sender (for client requests)
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
	CurrentTerm int
	LogLength   int
	LastTerm    int
}

type RequestVoteReply struct {
	VoteGranted bool
	Term        int
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

// IONIA port variables

// IONIA message types
const (
	IoniaMsgOrder    = "order"
	IoniaMsgAckOrder = "ackOrder"
	IoniaMsgCommit   = "commit"
	IoniaMsgWrite    = "write"
	IoniaMsgApply    = "apply"
	IoniaMsgAckWrite = "ackWrite"
	IoniaMsgRead     = "read"
	IoniaMsgRespRead = "respRead"
	IoniaMsgRequest  = "request"
	IoniaMsgMetadata = "metadata"
)

// IoniaMessage represents a message in the IONIA protocol
type IoniaMessage struct {
	Type  string // order, ackOrder, commit, write, apply, ackWrite, read, respRead, request, metadata
	From  string // sender node/client ID
	To    string // receiver node/client ID
	Val   int    // value for write/apply operations
	Term  int    // term number for the message
	Index int    // log index for ordering
}

// ClientRequest represents a client request in IONIA
type ClientRequest struct {
	ClientID  string
	Type      string // "write" or "read"
	Value     int    // value for write operations
	RequestID string // unique request identifier
}

// ClientResponse represents a response to a client in IONIA
type ClientResponse struct {
	ClientID  string
	RequestID string
	Type      string // "ackWrite" or "respRead"
	Value     int    // value for read responses
	Success   bool
}

// IONIA RPC types

// IoniaWriteArgs - arguments for write request
type IoniaWriteArgs struct {
	ClientID  string
	RequestID string
	Value     int
	Term      int
}

// IoniaWriteReply - reply for write request
type IoniaWriteReply struct {
	Success bool
	Term    int
}

// IoniaOrderArgs - arguments for order message (leader to follower)
type IoniaOrderArgs struct {
	LeaderID string
	Term     int
	Entry    LogEntry
	Index    int
}

// IoniaOrderReply - reply for order message (ackOrder)
type IoniaOrderReply struct {
	Success    bool
	Term       int
	FollowerID string
	Index      int
}

// IoniaCommitArgs - arguments for commit message
type IoniaCommitArgs struct {
	LeaderID string
	Term     int
	Index    int
}

// IoniaCommitReply - reply for commit message
type IoniaCommitReply struct {
	Success bool
	Term    int
}

// IoniaReadArgs - arguments for read request
type IoniaReadArgs struct {
	ClientID  string
	RequestID string
}

// IoniaReadReply - reply for read request
type IoniaReadReply struct {
	Value     int
	Success   bool
	RequestID string
}

// Gitaly RPC types for git operations

// GitalyGetBlobArgs - arguments for getting a blob
type GitalyGetBlobArgs struct {
	RepositoryPath string
	ObjectID       string // SHA-1 hash
}

// GitalyGetBlobReply - reply for getting a blob
type GitalyGetBlobReply struct {
	Content []byte
	Size    int64
	Success bool
	Error   string
}

// GitalyWriteBlobArgs - arguments for writing a blob
type GitalyWriteBlobArgs struct {
	RepositoryPath string
	Content        []byte
}

// GitalyWriteBlobReply - reply for writing a blob
type GitalyWriteBlobReply struct {
	ObjectID string // SHA-1 hash
	Success  bool
	Error    string
}

// GitalyGetTreeArgs - arguments for getting a tree
type GitalyGetTreeArgs struct {
	RepositoryPath string
	TreeID         string // SHA-1 hash
	Recursive      bool
}

// GitalyGetTreeReply - reply for getting a tree
type GitalyGetTreeReply struct {
	Entries []TreeEntry
	Success bool
	Error   string
}

// TreeEntry represents a single entry in a git tree
type TreeEntry struct {
	Name string
	Mode string
	Hash string
	Type string // "blob" or "tree"
}

// GitalyCreateTreeArgs - arguments for creating a tree
type GitalyCreateTreeArgs struct {
	RepositoryPath string
	Entries        []TreeEntry
	BaseTreeID     string // optional base tree
}

// GitalyCreateTreeReply - reply for creating a tree
type GitalyCreateTreeReply struct {
	TreeID  string // SHA-1 hash
	Success bool
	Error   string
}

// GitalyGetCommitArgs - arguments for getting a commit
type GitalyGetCommitArgs struct {
	RepositoryPath string
	CommitID       string // SHA-1 hash or ref name
}

// GitalyGetCommitReply - reply for getting a commit
type GitalyGetCommitReply struct {
	CommitID  string
	TreeID    string
	ParentIDs []string
	Author    Signature
	Committer Signature
	Message   string
	Success   bool
	Error     string
}

// Signature represents a git signature (author/committer)
type Signature struct {
	Name  string
	Email string
	When  string // RFC3339 timestamp
}

// GitalyCreateCommitArgs - arguments for creating a commit
type GitalyCreateCommitArgs struct {
	RepositoryPath string
	TreeID         string
	ParentIDs      []string
	Author         Signature
	Committer      Signature
	Message        string
}

// GitalyCreateCommitReply - reply for creating a commit
type GitalyCreateCommitReply struct {
	CommitID string // SHA-1 hash
	Success  bool
	Error    string
}

// GitalyGetRefArgs - arguments for getting a ref
type GitalyGetRefArgs struct {
	RepositoryPath string
	RefName        string // e.g., "refs/heads/main"
}

// GitalyGetRefReply - reply for getting a ref
type GitalyGetRefReply struct {
	RefName  string
	CommitID string
	Success  bool
	Error    string
}

// GitalyUpdateRefArgs - arguments for updating a ref
type GitalyUpdateRefArgs struct {
	RepositoryPath string
	RefName        string
	CommitID       string
	Force          bool
}

// GitalyUpdateRefReply - reply for updating a ref
type GitalyUpdateRefReply struct {
	Success bool
	Error   string
}

// GitalyListRefsArgs - arguments for listing refs
type GitalyListRefsArgs struct {
	RepositoryPath string
	Pattern        string // optional pattern to filter refs
}

// GitalyListRefsReply - reply for listing refs
type GitalyListRefsReply struct {
	Refs    []RefInfo
	Success bool
	Error   string
}

// RefInfo represents a git reference
type RefInfo struct {
	Name     string
	CommitID string
	Type     string // "branch", "tag", etc.
}

// GitalyAddWorkerArgs - arguments for adding a worker node
type GitalyAddWorkerArgs struct {
	WorkerID string
	Address  string
	RepoPath string
}

// GitalyAddWorkerReply - reply for adding a worker
type GitalyAddWorkerReply struct {
	Success bool
	Error   string
}

// QUEUE implementation
type Queue struct {
	Items []string
	lock  sync.Mutex
}

func (q *Queue) Enqueue(item string) {
	q.lock.Lock()
	defer q.lock.Unlock()
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
