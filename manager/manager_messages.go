package manager



type ReceiveVProposer struct {
	Index   int
	Term    int
	Command string
}

type ReplyProposer struct {
	JobName    string
	TaskNumber int
}

type RegisterArgs struct {
	WorkerAddress string
}

type RegisterResult struct {
	Success bool
}