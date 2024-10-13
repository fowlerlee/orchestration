package main

import (
	"context"
	"fmt"

	"sync"

	"github.com/fowlerlee/orchestration/common"

	_ "github.com/docker/docker/api/types/network"
	"github.com/docker/docker/client"
	_ "github.com/docker/docker/container"
	"github.com/docker/go-connections/nat"
	"github.com/google/uuid"
	// "github.com/sirupsen/logrus"
)

type wState string

const (
	Waiting wState = "1"
	Working wState = "2"
)

// Config holds configuration for the worker node
type Config struct {
	Name          string
	ExposedPorts  nat.PortSet
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
}

func CreateWorker(address string) (wk *Worker) {
	wk = new(Worker)
	wk.Channel = make(chan string)
	wk.ID = uuid.New()
	wk.State = Waiting
	wk.Queue = common.Queue{Items: make([]string, 5)}
	wk.Address = address
	return
}

func startWorkerRPC() {

}

type Docker struct {
	Client *client.Client
	Config Config
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
