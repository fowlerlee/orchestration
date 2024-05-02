package main

// import (
// 	"context"
// 	"fmt"
// 	"log"

// 	"github.com/docker/docker/client"
// 	"github.com/docker/docker/container"
// 	"github.com/sirupsen/logrus"
// )

// // Config holds configuration for the worker node
// type Config struct {
// 	ServerAddress string `json:"server_address"`  // Address of the Kubernetes API server
// 	ContainerImage string `json:"container_image"` // Image name of the container to run
// 	Port          int    `json:"port"`             // Port to expose for the server
// }

// // func main() {
// // 	// Load configuration (you can replace this with environment variables, flags etc.)
// // 	config := Config{
// // 		ServerAddress: "http://localhost:5432",
// // 		ContainerImage: "postgres:alpine3.19",
// // 		Port:          8081,
// // 	}

// // 	// Create a new Docker client
// // 	cli, err := client.NewClientWithOpts(client.WithHost(config.ServerAddress))
// // 	if err != nil {
// // 		log.Fatal(err)
// // 	}

// // 	// Pull the container image
// // 	err = pullImage(cli, config.ContainerImage)
// // 	if err != nil {
// // 		log.Fatal(err)
// // 	}

// // 	// Run the container
// // 	containerID, err := runContainer(cli, config)
// // 	if err != nil {
// // 		log.Fatal(err)
// // 	}

// // 	// Start the server on the exposed port
// // 	startServer(config.Port)

// // 	// Monitor the container for exit and handle gracefully
// // 	monitorContainer(cli, containerID)
// // }

// func pullImage(cli *client.Client, imageName string) error {
// 	_, err := cli.ImagePull(ctx, imageName, typePullLatest)
// 	return err
// }

// func  runContainer(cli *client.Client, config Config) (string, error) {
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
