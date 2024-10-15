package worker

import (
	"context"
	"fmt"
	"log"
	"net"
	"net/rpc"
	"os"

	"sync"

	"github.com/fowlerlee/orchestration/common"
	"github.com/google/uuid"
)

type wState string

const (
	Waiting wState = "1"
	Working wState = "2"
)

// Config holds configuration for the worker node
type Config struct {
	Name          string
	Cmd           []string
	Memory        int64
	Disk          int64
	Env           []string
	RestartPolicy string
	Image         string
}

type Worker struct {
	ctx context.Context
	sync.Mutex
	ID          uuid.UUID
	Queue       common.Queue
	Channel     chan string
	State       wState
	D           Docker
	DockerImage string
	Address     string
	l           net.Listener
	shutdown    chan struct{}
}

func CreateWorker(address string) (wk *Worker) {
	wk = new(Worker)
	wk.Channel = make(chan string)
	wk.ID = uuid.New()
	wk.State = Waiting
	wk.Queue = common.Queue{Items: make([]string, 5)}
	wk.Address = address
	wk.shutdown = make(chan struct{}, 1)
	return
}

func (w *Worker) StartWorkerRPC() {
	rpcs := rpc.NewServer()
	errX := rpcs.Register(w)
	if errX != nil {
		log.Fatalf("failed to register worker with rpc server: %v", errX)
	}
	os.Remove(w.Address)
	l, err := net.Listen(common.Protocol, w.Address)
	if err != nil {
		log.Fatalf("worker RPC server not initiated: %v", err)
	}
	w.l = l
	fmt.Println("worker rpc seems to be live!")

	go func() {
	loop:
		for {
			select {
			case <-w.shutdown:
				break loop
			default:
			}
			conn, err := w.l.Accept()
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

type Docker struct {
	Config Config
}

func (w *Worker) StopWorkerRPC() error {
	args := &common.WorkerShutdownArgs{}
	reply := &common.WorkerShutdownReply{}
	rpcName := "Worker.Shutdown"

	ok := common.RpcCall(w.Address, rpcName, args, reply)
	if !ok {
		return fmt.Errorf("failed to call %v rpc method", rpcName)
	}
	return nil
}

func (w *Worker) RegisterWithManager(address string) error {
	w.Lock()
	defer w.Unlock()
	args := &common.RegisterArgs{WorkerAddress: w.Address}
	reply := &common.RegisterResult{}
	rpcName := "Manager.Register"
	ok := common.RpcCall(address, rpcName, args, reply)
	if !ok {
		return fmt.Errorf("failed to call %v rpc method\n", rpcName)
	}
	return nil
}

func (w *Worker) Shutdown(args *common.WorkerShutdownArgs, reply *common.WorkerShutdownReply) error {
	w.shutdown <- struct{}{}
	close(w.shutdown)
	w.l.Close()
	fmt.Printf("worker at address %v was stopped and cleaned up\n", w.Address)
	return nil
}

type DockerResult struct {
	Error       error
	Action      string
	ContainerId string
	Result      string
}

func (wk *Worker) AssignWork(args *common.AssignWorkArgs, result *common.AssignWorkResults) error {
	wk.Mutex.Lock()
	defer wk.Mutex.Unlock()
	wk.DockerImage = args.ImageName
	wk.ContainerCreate(wk.ctx)
	result.WorkIsGiven = true
	fmt.Printf("work was assigned to the Worker at %v\n", wk.Address)
	return nil
}

func (w *Worker) Run() DockerResult {
	// ctx := context.Background()
	// reader, err := w.D.Client.ImagePull(ctx, w.D.Config.Image, image.PullOptions{})
	// if err != nil {
	// 	log.Printf("Error pulling image %s: %v \n", d.Config)
	// 	return DockerResult{Error: err}
	// }
	// io.Copy(os.Stdout, reader)
	return DockerResult{Result: "performed an image pull"}
}

func (w *Worker) ContainerCreate(ctx context.Context) bool {
	fmt.Println("create container for the worker and do Task")
	// config := &Config{}
	// w.D.Client.ContainerExecCreate(
	// 	ctx, w.DockerImage,
	// 	config, config,
	// )
	return true
}

// func main() {
// 	// Load configuration (you can replace this with environment variables, flags etc.)
// 	config := Config{
// 		ServerAddress: "http://localhost:5432",
// 		ContainerImage: "postgres:alpine3.19",
// 		Port:          8081,
// 	}

// 	// Create a new Docker client
// 	cli, err := client.NewClientWithOpts(client.WithHost(config.ServerAddress))
// 	if err != nil {
// 		log.Fatal(err)
// 	}

// 	// Pull the container image
// 	err = pullImage(cli, config.ContainerImage)
// 	if err != nil {
// 		log.Fatal(err)
// 	}

// 	// Run the container
// 	containerID, err := runContainer(cli, config)
// 	if err != nil {
// 		log.Fatal(err)
// 	}

// 	// Start the server on the exposed port
// 	startServer(config.Port)

// 	// Monitor the container for exit and handle gracefully
// 	monitorContainer(cli, containerID)
// }

// func runContainer(cli *client.Client, config Config) (string, error) {
// 	portMapping := fmt.Sprintf("%d:%d", config.Port, config.Port)
// 	config = &docker.ContainerConfig{
// 		Image:        config.ContainerImage,
// 		ExposedPorts: map[string]struct{}{portMapping: {}},
// 		HostConfig: &docker.HostConfig{
// 			PortBindings: map[string][]string{portMapping: {fmt.Sprintf("%d", config.Port)}},
// 		},
// 	}

// 	resp, err := cli.ContainerCreate(ctx, config, nil, nil, "")
// 	if err != nil {
// 		return "", err
// 	}

// 	err = cli.ContainerStart(ctx, resp.ID, nil)
// 	if err != nil {
// 		return "", err
// 	}

// 	return resp.ID, nil
// }

// func startServer(port int) {
// 	// Implement your server logic here.
// 	// This could be a simple HTTP server listening on the port
// 	// or any other kind of server you need.

// 	logrus.Infof("Server listening on port %d", port)
// 	// ... (your server code)
// }

// func monitorContainer(cli *client.Client, containerID string) {
// 	ch := cli.ContainerWait(ctx, containerID, container.WaitConditionNotRunning)
// 	exitCode, err := <-ch
// 	if err != nil {
// 		log.Fatal(err)
// 	}

// 	logrus.Infof("Container exited with code %d", exitCode)
// 	// Handle container exit (e.g., restart, log error)
// }

// var ctx = context.Background()
