package manager

import (
	"fmt"
	"testing"
)

func TestElectionAndFailure(t *testing.T) {
	setManagers := []string{"8080", "8081", "8082", "8083", "8084"}
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
		fmt.Printf("Leader is : %v", m0)
	}
	if m1.CheckForLeader() {
		fmt.Printf("Leader is : %v", m1)
	}

}
