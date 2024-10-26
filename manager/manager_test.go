package manager

import (
	"fmt"
	"testing"
)

func TestElectionAndFailure(t *testing.T) {
	l := "localhost:"
	setManagers := []string{l + "8080", l + "8081", l + "8082", l + "8083", l + "8084"}
	m0 := MakeManager(setManagers[0])
	m1 := MakeManager(setManagers[1])
	m2 := MakeManager(setManagers[2])
	m3 := MakeManager(setManagers[3])
	m0.OtherManagers = setManagers
	m1.OtherManagers = setManagers
	m2.OtherManagers = setManagers
	m3.OtherManagers = setManagers
	m0.StartManagerRPC()
	m1.StartManagerRPC()
	m2.StartManagerRPC()
	m3.StartManagerRPC()

	m0.StartLeaderElection()
	if m0.CheckForLeader() {
		fmt.Printf("State of replica m0: %v\n", m0.State)
		fmt.Printf("State of replica m1: %v\n", m1.State)
		fmt.Printf("State of replica m2: %v\n", m2.State)
		fmt.Printf("State of replica m3: %v\n", m3.State)
	}

	m0.StopManagerRPC()
	m1.StartLeaderElection()
	if m1.CheckForLeader() {
		fmt.Printf("State of replica m0: %v\n", m0.State)
		fmt.Printf("State of replica m1: %v\n", m1.State)
		fmt.Printf("State of replica m2: %v\n", m1.State)
		fmt.Printf("State of replica m3: %v\n", m1.State)
	}

	m1.StopManagerRPC()
	m2.StopManagerRPC()
	m3.StopManagerRPC()
}
