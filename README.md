# Orchestration

Welcome to the orchestrator project, specified in TLAplus and coded in Golang.

## Video content

Please visit the Youtube channel where this project is recorded to learn more about TLA+, Go and the orchestrator pattern as used in Borg and Kubernetes (https://www.youtube.com/watch?v=hbVHDbVPPo4). 
This project is a simplified version showing how easy it is to create distributed applications using TLA+ and Golang.

There exists a Client RPC Server that communicates with a Manager RPC Server, which in turn communicates with the Worker RPC Servers (3 in this case) that are required to register with the Manager to receive work. The Manager handles shutdown of the workers when work is complete and itself. The Workers handle cleaup of their own KVStore and data on each. See the image below for the architecture.

A simple XOR erasure code procedure is used to allow a failed Worker to recover its lost data upon start up and after failure. Since Reed-Solomon is not used, failure of several Workers will not allow recovery of all Worker data.

The Worker uses a VirtualMemory via its cgo tooling. The Virtual Memory is made in Rust, then exposed via extern "C" functions in Rust. Note the implementation is unsafe, and its a Pointer to a u8 type. We have Rust tests for this, but its only way to make it happen.

## Goals:

- Create Orchestrator Pattern - done
- Implement XOR erasure codes for Workers on Managers and restore lost data - done
- Rust to C to Go Virtual Memory implementation - done
- Reed-Solomon erasure codes implementation - ongoing 
- Demonstrate Raft consensus between several managers - ongoing
- Demonstrate KVRaft algorithm for the Workers and their KVStore - ongoing
- Demonstrate Lock Service for Manager communicating with several Clients - ongoing
- Change from Raft to the IONIA protocol from Xu et al (IonIa: High-Performance Replication for Modern Disk-based KV Stores) - ongoing
- import the GeeqoDB system with scripts and build for storage on the Master and Worker - done

Note: Reed-Solomon implementation is inspired and ported from the OSS implementation by BackBlaze -> https://www.backblaze.com/blog/reed-solomon/ . The implementation is in Java and can be viewed at https://github.com/Backblaze/JavaReedSolomon

### Run integration test with cleanup

```
    go run main.go 8080 8081 8082 8083 8084

```
### Debug and Test Manager Consensus

````
    dlv test ./manager -- -test.run=TestElectionAndFailure
    
````

### Testing custom Worker VirtualMemory

```
    #rust linux | macOS=libvirtualmemory.dylib | windows=libvirtualmemory.dll
    rustc --crate-type cdylib src/lib.rs -o libvirtualmemory.so

    #or
    cargo build --release

    #go testing
    cd virtualgomapping
    go test

    #if you get problems try
    go clean cache
    go test

    #go
    go build -o container
   ./container
```

### NeonDB connection for the workers

Please make sure you have a .env file for your db settings in the /cmd diretory.

````
# this will seed the db with dummy data where you can add your own
cd cmd
go run main.go

````

### Linting before commit - we dont have lint checks on the ci/cd

make sure you run the following

`````
go install github.com/golangci/golangci-lint/cmd/golangci-lint@v1.54.2

golangci-lint run ./...

`````

<h3 align="center" > <img src="./orchestration.png" width="700" height="600" style="center: 10px;"></h3
