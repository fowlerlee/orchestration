package manager

import (
	"testing"

	"github.com/fowlerlee/orchestration/common"
	"github.com/google/uuid"
)

// Init == /\ log = [n \in Nodes |-> {}]
//
//	/\ durabilitylog = [n \in Nodes |-> {}]
//	/\ durabilityCommitIndex = [n \in Nodes |-> 0]
//	/\ commitIndex = [n \in Nodes |-> 0]
//	/\ appliedIndex = [n \in Nodes |-> 0]
//	/\ nextIndex = [n \in Nodes |-> [f \in Followers |-> 1]]
//	/\ matchIndex = [n \in Nodes |-> [f \in Followers |-> 0]]
//	/\ currentTerm = [n \in Nodes |-> 0]
//	/\ votedFor = [n \in Nodes |-> NULL]
//	/\ state = [n \in Nodes |-> IF n = Leader THEN "leader" ELSE "follower"]
//	/\ clientRequests = {}
//	/\ clientResponses = {}
func TestIoniaInitState(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Test: log = [n \in Nodes |-> {}]
	for _, node := range nodes {
		if log, exists := m.durabilitylog[node]; !exists || len(log) != 0 {
			t.Errorf("Expected empty log for node %s, got %v", node, log)
		}
	}

	// Test: durabilitylog = [n \in Nodes |-> {}]
	for _, node := range nodes {
		if log, exists := m.durabilitylog[node]; !exists || len(log) != 0 {
			t.Errorf("Expected empty durabilitylog for node %s, got %v", node, log)
		}
	}

	// Test: durabilityCommitIndex = [n \in Nodes |-> 0]
	for _, node := range nodes {
		if idx, exists := m.durabilityCommitIndex[node]; !exists || idx != 0 {
			t.Errorf("Expected durabilityCommitIndex 0 for node %s, got %d", node, idx)
		}
	}

	// Test: commitIndex = [n \in Nodes |-> 0]
	for _, node := range nodes {
		if idx, exists := m.commitIndex[node]; !exists || idx != 0 {
			t.Errorf("Expected commitIndex 0 for node %s, got %d", node, idx)
		}
	}

	// Test: appliedIndex = [n \in Nodes |-> 0]
	for _, node := range nodes {
		if idx, exists := m.appliedIndex[node]; !exists || idx != 0 {
			t.Errorf("Expected appliedIndex 0 for node %s, got %d", node, idx)
		}
	}

	// Test: nextIndex = [n \in Nodes |-> [f \in Followers |-> 1]]
	for _, node := range nodes {
		nextIdx, exists := m.nextIndex[node]
		if !exists {
			t.Errorf("Expected nextIndex map for node %s", node)
			continue
		}
		for _, follower := range nodes {
			if follower != node {
				if idx, ok := nextIdx[follower]; !ok || idx != 1 {
					t.Errorf("Expected nextIndex[%s][%s] = 1, got %d", node, follower, idx)
				}
			}
		}
	}

	// Test: matchIndex = [n \in Nodes |-> [f \in Followers |-> 0]]
	for _, node := range nodes {
		matchIdx, exists := m.matchIndex[node]
		if !exists {
			t.Errorf("Expected matchIndex map for node %s", node)
			continue
		}
		for _, follower := range nodes {
			if follower != node {
				if idx, ok := matchIdx[follower]; !ok || idx != 0 {
					t.Errorf("Expected matchIndex[%s][%s] = 0, got %d", node, follower, idx)
				}
			}
		}
	}

	// Test: currentTerm = [n \in Nodes |-> 0]
	for _, node := range nodes {
		if term, exists := m.currentTerm[node]; !exists || term != 0 {
			t.Errorf("Expected currentTerm 0 for node %s, got %d", node, term)
		}
	}

	// Test: votedFor = [n \in Nodes |-> NULL] (empty string represents NULL)
	for _, node := range nodes {
		if voted, exists := m.votedFor[node]; !exists || voted != "" {
			t.Errorf("Expected votedFor empty for node %s, got %s", node, voted)
		}
	}

	// Test: state = [n \in Nodes |-> IF n = Leader THEN "leader" ELSE "follower"]
	for _, node := range nodes {
		state, exists := m.state[node]
		if !exists {
			t.Errorf("Expected state for node %s", node)
			continue
		}
		if node == leaderID {
			if state != Leader {
				t.Errorf("Expected Leader state for node %s, got %v", node, state)
			}
		} else {
			if state != Follower {
				t.Errorf("Expected Follower state for node %s, got %v", node, state)
			}
		}
	}

	// Test: clientRequests = {}
	if len(m.clientRequests) != 0 {
		t.Errorf("Expected empty clientRequests, got %d entries", len(m.clientRequests))
	}

	// Test: clientResponses = {}
	if len(m.clientResponses) != 0 {
		t.Errorf("Expected empty clientResponses, got %d entries", len(m.clientResponses))
	}
}

// TestClientWriteRequest tests ClientWriteRequest operation
// ClientWriteRequest(c, n) ==
//
//	/\ IsLeader(n) \/ IsFollower(n)
//	/\ clientRequests' = [clientRequests EXCEPT ![c] = [type: "write", val: CHOOSE v \in Values : TRUE]]
//	/\ Send([type: "write", val: CHOOSE v \in Values : TRUE])
func TestClientWriteRequest(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Test write request to leader
	clientID := "client1"
	requestID := "req1"
	value := 42

	err := ClientWriteRequest(m, clientID, requestID, value, leaderID)
	if err != nil {
		t.Fatalf("ClientWriteRequest failed: %v", err)
	}

	// Verify clientRequests was updated
	req, exists := m.clientRequests[requestID]
	if !exists {
		t.Errorf("Expected clientRequest with ID %s", requestID)
	}
	if req.ClientID != clientID {
		t.Errorf("Expected ClientID %s, got %s", clientID, req.ClientID)
	}
	if req.Type != common.IoniaMsgWrite {
		t.Errorf("Expected Type %s, got %s", common.IoniaMsgWrite, req.Type)
	}
	if req.Value != value {
		t.Errorf("Expected Value %d, got %d", value, req.Value)
	}
}

// TestLeaderReceiveWrite tests LeaderReceiveWrite operation
// LeaderReceiveWrite(n) ==
//
//	/\ IsLeader(n)
//	/\ clientRequests /= {}
//	/\ durabilitylog' = [durabilitylog EXCEPT ![n] = Append(durabilitylog[n], [type : {"write"}, val : CHOOSE v \in Values : TRUE])]
//	/\ Send([type : {"ackWrite"}])
func TestLeaderReceiveWrite(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Add a client request first
	requestID := "req1"
	m.clientRequests[requestID] = common.ClientRequest{
		ClientID:  "client1",
		Type:      common.IoniaMsgWrite,
		Value:     42,
		RequestID: requestID,
	}

	// Get initial durability log length
	initialLen := len(m.durabilitylog[leaderID])

	// Execute LeaderReceiveWrite
	err := LeaderReceiveWrite(m, leaderID)
	if err != nil {
		t.Fatalf("LeaderReceiveWrite failed: %v", err)
	}

	// Verify durability log was appended
	if len(m.durabilitylog[leaderID]) != initialLen+1 {
		t.Errorf("Expected durability log length %d, got %d", initialLen+1, len(m.durabilitylog[leaderID]))
	}

	entry := m.durabilitylog[leaderID][len(m.durabilitylog[leaderID])-1]
	if entry.Type != common.IoniaMsgWrite {
		t.Errorf("Expected entry type %s, got %s", common.IoniaMsgWrite, entry.Type)
	}
	if entry.Value != 42 {
		t.Errorf("Expected entry value 42, got %d", entry.Value)
	}
}

// TestFollowerReceiveWrite tests FollowerReceiveWrite operation
// FollowerReceiveWrite(n) ==
//
//	/\ IsFollower(n)
//	/\ clientRequests /= {}
//	/\ durabilitylog' = [durabilitylog EXCEPT ![n] = Append(durabilitylog[n], [type : {"write"}, val : CHOOSE v \in Values : TRUE])]
//	/\ Send([type : {"ackWrite"}])
func TestFollowerReceiveWrite(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"
	followerID := "node2"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Add a client request first
	requestID := "req1"
	m.clientRequests[requestID] = common.ClientRequest{
		ClientID:  "client1",
		Type:      common.IoniaMsgWrite,
		Value:     42,
		RequestID: requestID,
	}

	// Get initial durability log length
	initialLen := len(m.durabilitylog[followerID])

	// Execute FollowerReceiveWrite
	err := FollowerReceiveWrite(m, followerID)
	if err != nil {
		t.Fatalf("FollowerReceiveWrite failed: %v", err)
	}

	// Verify durability log was appended
	if len(m.durabilitylog[followerID]) != initialLen+1 {
		t.Errorf("Expected durability log length %d, got %d", initialLen+1, len(m.durabilitylog[followerID]))
	}

	entry := m.durabilitylog[followerID][len(m.durabilitylog[followerID])-1]
	if entry.Type != common.IoniaMsgWrite {
		t.Errorf("Expected entry type %s, got %s", common.IoniaMsgWrite, entry.Type)
	}
	if entry.Value != 42 {
		t.Errorf("Expected entry value 42, got %d", entry.Value)
	}
}

// TestLeaderBackgroudOrder tests LeaderBackgroudOrder operation
// LeaderBackgroudOrder(n) ==
//
//	/\ IsLeader(n)
//	/\ durabilitylog[n] /= {}
//	/\ \E f \in Nodes :
//	        /\ IsFollower(f)
//	        /\ Send([type : {"order"}])
//	        /\ durabilitylog' = [durabilitylog EXCEPT ![f] = Append(durabilitylog[f], [type : {"order"}])]
//	/\ log' = [log EXCEPT ![n] = Append(log[n], [type : {"write"}, val : CHOOSE v \in Values : TRUE])]
func TestLeaderBackgroudOrder(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"
	followerID := "node2"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		Log:                   []common.LogEntry{},
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Add an entry to leader's durability log
	entry := common.LogEntry{
		Index:   1,
		Term:    0,
		Type:    common.IoniaMsgWrite,
		Value:   42,
		Command: "write:42",
	}
	m.durabilitylog[leaderID] = append(m.durabilitylog[leaderID], entry)

	initialLogLen := len(m.log[leaderID])
	initialFollowerDurabilityLen := len(m.durabilitylog[followerID])

	// Execute LeaderBackgroudOrder
	err := LeaderBackgroudOrder(m, leaderID, followerID)
	if err != nil {
		t.Fatalf("LeaderBackgroudOrder failed: %v", err)
	}

	// Verify leader's log was appended
	if len(m.log[leaderID]) != initialLogLen+1 {
		t.Errorf("Expected leader log length %d, got %d", initialLogLen+1, len(m.log[leaderID]))
	}

	// Verify follower's durability log was appended with order
	if len(m.durabilitylog[followerID]) != initialFollowerDurabilityLen+1 {
		t.Errorf("Expected follower durability log length %d, got %d", initialFollowerDurabilityLen+1, len(m.durabilitylog[followerID]))
	}

	orderEntry := m.durabilitylog[followerID][len(m.durabilitylog[followerID])-1]
	if orderEntry.Type != common.IoniaMsgOrder {
		t.Errorf("Expected order entry type %s, got %s", common.IoniaMsgOrder, orderEntry.Type)
	}
}

// TestFollowerReceiveOrder tests FollowerReceiveOrder operation
// FollowerReceiveOrder(n) ==
//
//	/\ IsFollower(n)
//	/\ durabilitylog[n] /= {}
//	/\ Send([type : {"ackWrite"}])
//	/\ log' = [log EXCEPT ![n] = Append(durabilitylog[n], [type : {"write"}, val : CHOOSE v \in Values : TRUE])]
func TestFollowerReceiveOrder(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"
	followerID := "node2"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		Log:                   []common.LogEntry{},
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Add an entry to follower's durability log
	entry := common.LogEntry{
		Index:   1,
		Term:    0,
		Type:    common.IoniaMsgWrite,
		Value:   42,
		Command: "write:42",
	}
	m.durabilitylog[followerID] = append(m.durabilitylog[followerID], entry)

	initialFollowerLogLen := len(m.log[followerID])

	// Execute FollowerReceiveOrder
	err := FollowerReceiveOrder(m, followerID)
	if err != nil {
		t.Fatalf("FollowerReceiveOrder failed: %v", err)
	}

	// Verify follower's log was appended
	if len(m.log[followerID]) != initialFollowerLogLen+1 {
		t.Errorf("Expected follower log length %d, got %d", initialFollowerLogLen+1, len(m.log[followerID]))
	}

	logEntry := m.log[followerID][len(m.log[followerID])-1]
	if logEntry.Type != common.IoniaMsgWrite {
		t.Errorf("Expected log entry type %s, got %s", common.IoniaMsgWrite, logEntry.Type)
	}
	if logEntry.Value != 42 {
		t.Errorf("Expected log entry value 42, got %d", logEntry.Value)
	}
}

// TestLeaderApply tests LeaderApply operation
// LeaderApply(n) ==
//
//	/\ IsLeader(n)
//	/\ durabilitylog[n] /= {}
//	/\ log' = [log EXCEPT ![n] = Append(log[n], [type : {"apply"}, val : CHOOSE v \in Values : TRUE])]
func TestLeaderApply(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		Log:                   []common.LogEntry{},
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Add an entry to leader's durability log
	entry := common.LogEntry{
		Index:   1,
		Term:    0,
		Type:    common.IoniaMsgWrite,
		Value:   42,
		Command: "write:42",
	}
	m.durabilitylog[leaderID] = append(m.durabilitylog[leaderID], entry)

	initialLogLen := len(m.log[leaderID])

	// Execute LeaderApply
	err := LeaderApply(m, leaderID)
	if err != nil {
		t.Fatalf("LeaderApply failed: %v", err)
	}

	// Verify leader's log was appended with apply entry
	if len(m.log[leaderID]) != initialLogLen+1 {
		t.Errorf("Expected leader log length %d, got %d", initialLogLen+1, len(m.log[leaderID]))
	}

	applyEntry := m.log[leaderID][len(m.log[leaderID])-1]
	if applyEntry.Type != common.IoniaMsgApply {
		t.Errorf("Expected apply entry type %s, got %s", common.IoniaMsgApply, applyEntry.Type)
	}
	if applyEntry.Value != 42 {
		t.Errorf("Expected apply entry value 42, got %d", applyEntry.Value)
	}
}

// TestLeaderCommit tests LeaderCommit operation
// LeaderCommit(n) ==  /\ IsLeader(n)
//
//	/\ state[n] = "leader"
//	/\ Send([type : {"commit"}])
func TestLeaderCommit(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		Log:                   []common.LogEntry{},
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Execute LeaderCommit
	err := LeaderCommit(m, leaderID)
	if err != nil {
		t.Fatalf("LeaderCommit failed: %v", err)
	}

	// Verify commit message was sent (in real implementation, this would be tracked)
	// For now, we just verify the function doesn't error
}

// TestApplyCommitted tests ApplyCommitted operation
// ApplyCommitted(n) ==
//
//	/\ IsFollower(n)
//	/\ durabilitylog[n] /= {}
//	/\ log' = [log EXCEPT ![n] = Append(log[n], [type : {"apply"}, val : CHOOSE v \in Values : TRUE])]
func TestApplyCommitted(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"
	followerID := "node2"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		Log:                   []common.LogEntry{},
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Add an entry to follower's durability log
	entry := common.LogEntry{
		Index:   1,
		Term:    0,
		Type:    common.IoniaMsgWrite,
		Value:   42,
		Command: "write:42",
	}
	m.durabilitylog[followerID] = append(m.durabilitylog[followerID], entry)

	initialLogLen := len(m.log[followerID])

	// Execute ApplyCommitted
	err := ApplyCommitted(m, followerID)
	if err != nil {
		t.Fatalf("ApplyCommitted failed: %v", err)
	}

	// Verify follower's log was appended with apply entry
	if len(m.log[followerID]) != initialLogLen+1 {
		t.Errorf("Expected follower log length %d, got %d", initialLogLen+1, len(m.log[followerID]))
	}

	applyEntry := m.log[followerID][len(m.log[followerID])-1]
	if applyEntry.Type != common.IoniaMsgApply {
		t.Errorf("Expected apply entry type %s, got %s", common.IoniaMsgApply, applyEntry.Type)
	}
	if applyEntry.Value != 42 {
		t.Errorf("Expected apply entry value 42, got %d", applyEntry.Value)
	}
}

// TestLogConsistency tests the LogConsistency invariant
// LogConsistency ==
//
//	/\  \A n1, n2 \in Nodes:
//	        \A i \in 1..Min(Len(log[n1]), Len(log[n2])) :
//	            /\   commitIndex[n1] >= i
//	            /\   commitIndex[n2] >= i
//	            /\   log[n1][i].term = log[n2][i].term
func TestLogConsistency(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		Log:                   []common.LogEntry{},
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Initially, logs are empty, so consistency should hold
	if !CheckLogConsistency(m, nodes) {
		t.Error("LogConsistency should hold for empty logs")
	}
}

// TestCommitIndexMonotonic tests the CommitIndexMonotonic invariant
// CommitIndexMonotonic ==
//
//	/\  \A n \in Nodes : commitIndex[n] >= 0
//	/\  \A n \in Nodes : durabilityCommitIndex[n] >= 0
func TestCommitIndexMonotonic(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	if !CheckCommitIndexMonotonic(m, nodes) {
		t.Error("CommitIndexMonotonic should hold after initialization")
	}
}

// TestAppliedIndexBounded tests the AppliedIndexBounded invariant
// AppliedIndexBounded ==
//
//	/\  \A n \in Nodes : appliedIndex[n] <= commitIndex[n]
//	/\  \A n \in Nodes : appliedIndex[n] <= durabilityCommitIndex[n]
func TestAppliedIndexBounded(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	if !CheckAppliedIndexBounded(m, nodes) {
		t.Error("AppliedIndexBounded should hold after initialization")
	}
}

// TestLeaderUniqueness tests the LeaderUniqueness invariant
// LeaderUniqueness == Cardinality({n \in Nodes : IsLeader(n)}) <= 1
func TestLeaderUniqueness(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	if !CheckLeaderUniqueness(m, nodes) {
		t.Error("LeaderUniqueness should hold after initialization")
	}
}

// TestIoniaEndToEndWriteFlow tests the complete IONIA write flow:
// 1. Client sends write request
// 2. Leader receives write and adds to durability log
// 3. Leader sends order to follower
// 4. Follower receives order and adds to log
// 5. Leader commits
// 6. Follower applies committed entry
func TestIoniaEndToEndWriteFlow(t *testing.T) {
	nodes := []string{"node1", "node2", "node3"}
	leaderID := "node1"
	followerID := "node2"
	clientID := "client1"
	requestID := "req1"
	value := 42

	m := &Manager{
		address:               "localhost:8080",
		ID:                    uuid.New(),
		Log:                   []common.LogEntry{},
		log:                   make(map[string][]common.LogEntry),
		durabilitylog:         make(map[string][]common.LogEntry),
		durabilityCommitIndex: make(map[string]int),
		commitIndex:           make(map[string]int),
		appliedIndex:          make(map[string]int),
		nextIndex:             make(map[string]map[string]int),
		matchIndex:            make(map[string]map[string]int),
		currentTerm:           make(map[string]int),
		votedFor:              make(map[string]string),
		state:                 make(map[string]ManagerElectionState),
		clientRequests:        make(map[string]common.ClientRequest),
		clientResponses:       make(map[string]common.ClientResponse),
	}

	InitIoniaState(m, nodes, leaderID)

	// Step 1: Client sends write request
	err := ClientWriteRequest(m, clientID, requestID, value, leaderID)
	if err != nil {
		t.Fatalf("ClientWriteRequest failed: %v", err)
	}

	// Verify client request was added
	if _, exists := m.clientRequests[requestID]; !exists {
		t.Error("Client request was not added")
	}

	// Step 2: Leader receives write and adds to durability log
	err = LeaderReceiveWrite(m, leaderID)
	if err != nil {
		t.Fatalf("LeaderReceiveWrite failed: %v", err)
	}

	// Verify durability log was updated
	if len(m.durabilitylog[leaderID]) != 1 {
		t.Errorf("Expected durability log length 1, got %d", len(m.durabilitylog[leaderID]))
	}

	// Step 3: Leader sends order to follower
	err = LeaderBackgroudOrder(m, leaderID, followerID)
	if err != nil {
		t.Fatalf("LeaderBackgroudOrder failed: %v", err)
	}

	// Verify follower's durability log has order entry
	if len(m.durabilitylog[followerID]) != 1 {
		t.Errorf("Expected follower durability log length 1, got %d", len(m.durabilitylog[followerID]))
	}

	// Verify leader's replicated log was updated
	if len(m.log[leaderID]) != 1 {
		t.Errorf("Expected leader log length 1, got %d", len(m.log[leaderID]))
	}

	// Step 4: Follower receives order and adds to log
	err = FollowerReceiveOrder(m, followerID)
	if err != nil {
		t.Fatalf("FollowerReceiveOrder failed: %v", err)
	}

	// Verify follower's replicated log was updated
	if len(m.log[followerID]) != 1 {
		t.Errorf("Expected follower log length 1, got %d", len(m.log[followerID]))
	}

	// Step 5: Leader commits
	err = LeaderCommit(m, leaderID)
	if err != nil {
		t.Fatalf("LeaderCommit failed: %v", err)
	}

	// Step 6: Follower applies committed entry
	err = ApplyCommitted(m, followerID)
	if err != nil {
		t.Fatalf("ApplyCommitted failed: %v", err)
	}

	// Verify follower's log has apply entry
	if len(m.log[followerID]) != 2 {
		t.Errorf("Expected follower log length 2 (write + apply), got %d", len(m.log[followerID]))
	}

	applyEntry := m.log[followerID][len(m.log[followerID])-1]
	if applyEntry.Type != common.IoniaMsgApply {
		t.Errorf("Expected apply entry, got %s", applyEntry.Type)
	}

	// Verify invariants still hold
	if !CheckLogConsistency(m, nodes) {
		t.Error("LogConsistency invariant violated")
	}
	if !CheckCommitIndexMonotonic(m, nodes) {
		t.Error("CommitIndexMonotonic invariant violated")
	}
	if !CheckAppliedIndexBounded(m, nodes) {
		t.Error("AppliedIndexBounded invariant violated")
	}
	if !CheckLeaderUniqueness(m, nodes) {
		t.Error("LeaderUniqueness invariant violated")
	}
}
