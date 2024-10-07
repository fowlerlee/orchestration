package common

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
