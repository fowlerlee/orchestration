package manager

import (
	"context"
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


// there are bugs in this test, as we debug in one node they other
// nodes in different address spaces send many messages, try fewer msgs
func TestLeaderRecovery(t *testing.T) {
	l := "localhost:"
	setManagers := []string{l + "8080", l + "8081", l + "8082", l + "8083", l + "8084"}
	m0 := MakeManager(setManagers[0])
	m1 := MakeManager(setManagers[1])
	m2 := MakeManager(setManagers[2])
	m3 := MakeManager(setManagers[3])
	group := []*Manager{m0, m1, m2, m3}
	for _, v1 := range group {
		for _, v2 := range setManagers {
			if v1.address != v2 {
				v1.OtherManagers = append(v1.OtherManagers, v2)
			}
		}
	}

	m0.SendHeartbeats(context.Background())
	m1.SendHeartbeats(context.Background())
	m2.SendHeartbeats(context.Background())
	m3.SendHeartbeats(context.Background())

	if m0.CheckForLeader() || m1.CheckForLeader() || m2.CheckForLeader() || m3.CheckForLeader() {
		fmt.Println("Leader exists")

	}

}
