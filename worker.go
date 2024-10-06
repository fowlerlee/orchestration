package main

import (
	"context"
	"fmt"
	"io"
	"log"
	"os"

	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/image"
	"github.com/docker/docker/client"
	"github.com/docker/docker/container"
	"github.com/docker/go-connections/nat"
	"github.com/golang-collections/collections/queue"
	"github.com/google/uuid"
	"github.com/sirupsen/logrus"
)

type wState string

const (
	Waiting wState  = iota
	Working
)

// Config holds configuration for the worker node
type Config struct {
	Name string
	ExposedPorts nat.PortSet
	Cmd [] string
	Memory int64
	Disk int64
	Env []string
	RestartPolicy string
}

type Worker struct {
	ID      uuid.UUID
	Queue   queue.Queue
	Channel chan string
	State wState
}

type Docker struct {
	Client *client.Client
	Config Config
}

type DockerResult struct {
	Error string
	Action string
	ContainerId string
	Result string
}

func (d *Docker) Run() DockerResult  {
	ctx := context.Background()
	reader, err := d.Client.ImagePull(ctx, d.Config.Image, image.PullOptions{})
	if err != nil {
		log.Printf("Error pulling image %s: %v \n",  d.Config)
		return DockerResult{Error: err}
	}
	io.Copy(os.Stdout, reader)
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

func pullImage(cli *client.Client, imageName string) error {
	typePullLatest := image.PullOptions {
		All true,

	}

	_, err := cli.ImagePull(ctx, imageName, typePullLatest)
	return err
}

func runContainer(cli *client.Client, config Config) (string, error) {
	portMapping := fmt.Sprintf("%d:%d", config.Port, config.Port)
	config = &docker.ContainerConfig{
		Image:        config.ContainerImage,
		ExposedPorts: map[string]struct{}{portMapping: {}},
		HostConfig: &docker.HostConfig{
			PortBindings: map[string][]string{portMapping: {fmt.Sprintf("%d", config.Port)}},
		},
	}

	resp, err := cli.ContainerCreate(ctx, config, nil, nil, "")
	if err != nil {
		return "", err
	}

	err = cli.ContainerStart(ctx, resp.ID, nil)
	if err != nil {
		return "", err
	}

	return resp.ID, nil
}

func startServer(port int) {
	// Implement your server logic here.
	// This could be a simple HTTP server listening on the port
	// or any other kind of server you need.

	logrus.Infof("Server listening on port %d", port)
	// ... (your server code)
}

func monitorContainer(cli *client.Client, containerID string) {
	ch := cli.ContainerWait(ctx, containerID, container.WaitConditionNotRunning)
	exitCode, err := <-ch
	if err != nil {
		log.Fatal(err)
	}

	logrus.Infof("Container exited with code %d", exitCode)
	// Handle container exit (e.g., restart, log error)
}

var ctx = context.Background()
