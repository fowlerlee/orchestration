package manager

import (
	"fmt"

	"github.com/fowlerlee/orchestration/common"
)

// InitIoniaState initializes IONIA state according to the TLA+ Init formula
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
func InitIoniaState(m *Manager, nodes []string, leaderID string) {
	m.Lock()
	defer m.Unlock()

	// Initialize log = [n \in Nodes |-> {}] - replicated log per node
	m.Log = []common.LogEntry{} // local node's log (for backward compatibility)
	for _, node := range nodes {
		m.log[node] = []common.LogEntry{}
	}

	// Initialize durabilitylog = [n \in Nodes |-> {}]
	for _, node := range nodes {
		m.durabilitylog[node] = []common.LogEntry{}
	}

	// Initialize durabilityCommitIndex = [n \in Nodes |-> 0]
	for _, node := range nodes {
		m.durabilityCommitIndex[node] = 0
	}

	// Initialize commitIndex = [n \in Nodes |-> 0]
	for _, node := range nodes {
		m.commitIndex[node] = 0
	}

	// Initialize appliedIndex = [n \in Nodes |-> 0]
	for _, node := range nodes {
		m.appliedIndex[node] = 0
	}

	// Initialize nextIndex = [n \in Nodes |-> [f \in Followers |-> 1]]
	for _, node := range nodes {
		m.nextIndex[node] = make(map[string]int)
		for _, follower := range nodes {
			if follower != node {
				m.nextIndex[node][follower] = 1
			}
		}
	}

	// Initialize matchIndex = [n \in Nodes |-> [f \in Followers |-> 0]]
	for _, node := range nodes {
		m.matchIndex[node] = make(map[string]int)
		for _, follower := range nodes {
			if follower != node {
				m.matchIndex[node][follower] = 0
			}
		}
	}

	// Initialize currentTerm = [n \in Nodes |-> 0]
	for _, node := range nodes {
		m.currentTerm[node] = 0
	}

	// Initialize votedFor = [n \in Nodes |-> NULL] (empty string = NULL)
	for _, node := range nodes {
		m.votedFor[node] = ""
	}

	// Initialize state = [n \in Nodes |-> IF n = Leader THEN "leader" ELSE "follower"]
	for _, node := range nodes {
		if node == leaderID {
			m.state[node] = Leader
		} else {
			m.state[node] = Follower
		}
	}

	// Initialize clientRequests = {}
	m.clientRequests = make(map[string]common.ClientRequest)

	// Initialize clientResponses = {}
	m.clientResponses = make(map[string]common.ClientResponse)
}

// Helper functions for IONIA

// IsLeader checks if a node is a leader
func IsLeader(m *Manager, nodeID string) bool {
	m.Lock()
	defer m.Unlock()
	state, exists := m.state[nodeID]
	return exists && state == Leader
}

// IsFollower checks if a node is a follower
func IsFollower(m *Manager, nodeID string) bool {
	m.Lock()
	defer m.Unlock()
	state, exists := m.state[nodeID]
	return exists && state == Follower
}

// GetLastLogIndex returns the last log index for a node
func GetLastLogIndex(m *Manager, nodeID string) int {
	m.Lock()
	defer m.Unlock()
	// For local node, use m.Log
	if nodeID == m.ID.String() {
		return len(m.Log)
	}
	// For other nodes, we'd need to track their logs
	// For now, return from durabilitylog as a proxy
	if log, exists := m.durabilitylog[nodeID]; exists {
		return len(log)
	}
	return 0
}

// GetLastLogTerm returns the last log term for a node
func GetLastLogTerm(m *Manager, nodeID string) int {
	m.Lock()
	defer m.Unlock()
	// For local node, use m.Log
	if nodeID == m.ID.String() {
		if len(m.Log) == 0 {
			return 0
		}
		return m.Log[len(m.Log)-1].Term
	}
	// For other nodes, check durabilitylog
	if log, exists := m.durabilitylog[nodeID]; exists && len(log) > 0 {
		return log[len(log)-1].Term
	}
	return 0
}

type IoniaNode struct {
	IoniaManager Manager
}

func (i *IoniaNode) ListenForClient() {
	var address = i.IoniaManager.address
	fmt.Printf("Address: %s", address)
	i.IoniaManager.StartManagerRPC()

	i.IoniaManager.BecomeLeader()
}

func NewIoniaNode() *IoniaNode {
	fmt.Println("creating an ionia node")
	return &IoniaNode{}
}

// ClientWriteRequest implements the ClientWriteRequest operation from the TLA+ spec
// ClientWriteRequest(c, n) ==
//
//	/\ IsLeader(n) \/ IsFollower(n)
//	/\ clientRequests' = [clientRequests EXCEPT ![c] = [type: "write", val: CHOOSE v \in Values : TRUE]]
//	/\ Send([type: "write", val: CHOOSE v \in Values : TRUE])
func ClientWriteRequest(m *Manager, clientID string, requestID string, value int, nodeID string) error {
	m.Lock()
	defer m.Unlock()

	// Check if node is leader or follower
	state, exists := m.state[nodeID]
	if !exists {
		return fmt.Errorf("node %s does not exist", nodeID)
	}
	if state != Leader && state != Follower {
		return fmt.Errorf("node %s is not a leader or follower", nodeID)
	}

	// Add client request
	m.clientRequests[requestID] = common.ClientRequest{
		ClientID:  clientID,
		Type:      common.IoniaMsgWrite,
		Value:     value,
		RequestID: requestID,
	}

	// In a real implementation, we would send the message here
	// For now, we just record that the request was made
	return nil
}

// LeaderReceiveWrite implements the LeaderReceiveWrite operation from the TLA+ spec
// LeaderReceiveWrite(n) ==
//
//	/\ IsLeader(n)
//	/\ clientRequests /= {}
//	/\ durabilitylog' = [durabilitylog EXCEPT ![n] = Append(durabilitylog[n], [type : {"write"}, val : CHOOSE v \in Values : TRUE])]
//	/\ Send([type : {"ackWrite"}])
func LeaderReceiveWrite(m *Manager, nodeID string) error {
	m.Lock()
	defer m.Unlock()

	// Check if node is leader
	state, exists := m.state[nodeID]
	if !exists || state != Leader {
		return fmt.Errorf("node %s is not a leader", nodeID)
	}

	// Check if clientRequests is not empty
	if len(m.clientRequests) == 0 {
		return fmt.Errorf("no client requests to process")
	}

	// Get the first client request (in real implementation, we'd process them in order)
	var req common.ClientRequest
	for _, r := range m.clientRequests {
		req = r
		break
	}

	// Append to durability log
	entry := common.LogEntry{
		Index:   len(m.durabilitylog[nodeID]) + 1,
		Term:    m.currentTerm[nodeID],
		Type:    common.IoniaMsgWrite,
		Value:   req.Value,
		From:    req.ClientID,
		Command: fmt.Sprintf("write:%d", req.Value),
	}
	m.durabilitylog[nodeID] = append(m.durabilitylog[nodeID], entry)

	// In a real implementation, we would send ackWrite message here
	// For now, we create a response
	m.clientResponses[req.RequestID] = common.ClientResponse{
		ClientID:  req.ClientID,
		RequestID: req.RequestID,
		Type:      common.IoniaMsgAckWrite,
		Success:   true,
	}

	return nil
}

// FollowerReceiveWrite implements the FollowerReceiveWrite operation from the TLA+ spec
// FollowerReceiveWrite(n) ==
//
//	/\ IsFollower(n)
//	/\ clientRequests /= {}
//	/\ durabilitylog' = [durabilitylog EXCEPT ![n] = Append(durabilitylog[n], [type : {"write"}, val : CHOOSE v \in Values : TRUE])]
//	/\ Send([type : {"ackWrite"}])
func FollowerReceiveWrite(m *Manager, nodeID string) error {
	m.Lock()
	defer m.Unlock()

	// Check if node is follower
	state, exists := m.state[nodeID]
	if !exists || state != Follower {
		return fmt.Errorf("node %s is not a follower", nodeID)
	}

	// Check if clientRequests is not empty
	if len(m.clientRequests) == 0 {
		return fmt.Errorf("no client requests to process")
	}

	// Get the first client request
	var req common.ClientRequest
	for _, r := range m.clientRequests {
		req = r
		break
	}

	// Append to durability log
	entry := common.LogEntry{
		Index:   len(m.durabilitylog[nodeID]) + 1,
		Term:    m.currentTerm[nodeID],
		Type:    common.IoniaMsgWrite,
		Value:   req.Value,
		From:    req.ClientID,
		Command: fmt.Sprintf("write:%d", req.Value),
	}
	m.durabilitylog[nodeID] = append(m.durabilitylog[nodeID], entry)

	// In a real implementation, we would send ackWrite message here
	// For now, we create a response
	m.clientResponses[req.RequestID] = common.ClientResponse{
		ClientID:  req.ClientID,
		RequestID: req.RequestID,
		Type:      common.IoniaMsgAckWrite,
		Success:   true,
	}

	return nil
}

// LeaderBackgroudOrder implements the LeaderBackgroudOrder operation from the TLA+ spec
// LeaderBackgroudOrder(n) ==
//
//	/\ IsLeader(n)
//	/\ durabilitylog[n] /= {}
//	/\ \E f \in Nodes :
//	        /\ IsFollower(f)
//	        /\ Send([type : {"order"}])
//	        /\ durabilitylog' = [durabilitylog EXCEPT ![f] = Append(durabilitylog[f], [type : {"order"}])]
//	/\ log' = [log EXCEPT ![n] = Append(log[n], [type : {"write"}, val : CHOOSE v \in Values : TRUE])]
func LeaderBackgroudOrder(m *Manager, leaderID string, followerID string) error {
	m.Lock()
	defer m.Unlock()

	// Check if node is leader
	state, exists := m.state[leaderID]
	if !exists || state != Leader {
		return fmt.Errorf("node %s is not a leader", leaderID)
	}

	// Check if durability log is not empty
	if len(m.durabilitylog[leaderID]) == 0 {
		return fmt.Errorf("durability log for leader %s is empty", leaderID)
	}

	// Check if follower exists and is a follower
	followerState, exists := m.state[followerID]
	if !exists || followerState != Follower {
		return fmt.Errorf("node %s is not a follower", followerID)
	}

	// Get the last entry from leader's durability log
	lastEntry := m.durabilitylog[leaderID][len(m.durabilitylog[leaderID])-1]

	// Append order to follower's durability log
	orderEntry := common.LogEntry{
		Index:   len(m.durabilitylog[followerID]) + 1,
		Term:    m.currentTerm[leaderID],
		Type:    common.IoniaMsgOrder,
		Value:   lastEntry.Value,
		From:    leaderID,
		Command: fmt.Sprintf("order:%d", lastEntry.Value),
	}
	m.durabilitylog[followerID] = append(m.durabilitylog[followerID], orderEntry)

	// Append write entry to leader's replicated log
	writeEntry := common.LogEntry{
		Index:   len(m.log[leaderID]) + 1,
		Term:    m.currentTerm[leaderID],
		Type:    common.IoniaMsgWrite,
		Value:   lastEntry.Value,
		From:    lastEntry.From,
		Command: fmt.Sprintf("write:%d", lastEntry.Value),
	}
	m.log[leaderID] = append(m.log[leaderID], writeEntry)
	// Also update local log for backward compatibility
	if leaderID == m.ID.String() {
		m.Log = append(m.Log, writeEntry)
	}

	return nil
}

// FollowerReceiveOrder implements the FollowerReceiveOrder operation from the TLA+ spec
// FollowerReceiveOrder(n) ==
//
//	/\ IsFollower(n)
//	/\ durabilitylog[n] /= {}
//	/\ Send([type : {"ackWrite"}])
//	/\ log' = [log EXCEPT ![n] = Append(durabilitylog[n], [type : {"write"}, val : CHOOSE v \in Values : TRUE])]
func FollowerReceiveOrder(m *Manager, followerID string) error {
	m.Lock()
	defer m.Unlock()

	// Check if node is follower
	state, exists := m.state[followerID]
	if !exists || state != Follower {
		return fmt.Errorf("node %s is not a follower", followerID)
	}

	// Check if durability log is not empty
	if len(m.durabilitylog[followerID]) == 0 {
		return fmt.Errorf("durability log for follower %s is empty", followerID)
	}

	// Get the last entry from follower's durability log
	lastEntry := m.durabilitylog[followerID][len(m.durabilitylog[followerID])-1]

	// Append write entry to follower's replicated log
	writeEntry := common.LogEntry{
		Index:   len(m.log[followerID]) + 1,
		Term:    lastEntry.Term,
		Type:    common.IoniaMsgWrite,
		Value:   lastEntry.Value,
		From:    lastEntry.From,
		Command: fmt.Sprintf("write:%d", lastEntry.Value),
	}
	m.log[followerID] = append(m.log[followerID], writeEntry)
	// Update local log if this is the local node
	if followerID == m.ID.String() {
		m.Log = append(m.Log, writeEntry)
	}

	// In a real implementation, we would send ackWrite message here
	return nil
}

// LeaderApply implements the LeaderApply operation from the TLA+ spec
// LeaderApply(n) ==
//
//	/\ IsLeader(n)
//	/\ durabilitylog[n] /= {}
//	/\ log' = [log EXCEPT ![n] = Append(log[n], [type : {"apply"}, val : CHOOSE v \in Values : TRUE])]
func LeaderApply(m *Manager, nodeID string) error {
	m.Lock()
	defer m.Unlock()

	// Check if node is leader
	state, exists := m.state[nodeID]
	if !exists || state != Leader {
		return fmt.Errorf("node %s is not a leader", nodeID)
	}

	// Check if durability log is not empty
	if len(m.durabilitylog[nodeID]) == 0 {
		return fmt.Errorf("durability log for leader %s is empty", nodeID)
	}

	// Get the last entry from durability log
	lastEntry := m.durabilitylog[nodeID][len(m.durabilitylog[nodeID])-1]

	// Append apply entry to leader's replicated log
	applyEntry := common.LogEntry{
		Index:   len(m.log[nodeID]) + 1,
		Term:    m.currentTerm[nodeID],
		Type:    common.IoniaMsgApply,
		Value:   lastEntry.Value,
		From:    lastEntry.From,
		Command: fmt.Sprintf("apply:%d", lastEntry.Value),
	}
	m.log[nodeID] = append(m.log[nodeID], applyEntry)
	// Also update local log for backward compatibility
	if nodeID == m.ID.String() {
		m.Log = append(m.Log, applyEntry)
	}

	return nil
}

// LeaderCommit implements the LeaderCommit operation from the TLA+ spec
// LeaderCommit(n) ==  /\ IsLeader(n)
//
//	/\ state[n] = "leader"
//	/\ Send([type : {"commit"}])
func LeaderCommit(m *Manager, nodeID string) error {
	m.Lock()
	defer m.Unlock()

	// Check if node is leader
	state, exists := m.state[nodeID]
	if !exists || state != Leader {
		return fmt.Errorf("node %s is not a leader", nodeID)
	}

	// Verify state is leader
	if state != Leader {
		return fmt.Errorf("node %s state is not leader", nodeID)
	}

	// In a real implementation, we would send commit message here
	// For now, we just verify the preconditions are met
	return nil
}

// ApplyCommitted implements the ApplyCommitted operation from the TLA+ spec
// ApplyCommitted(n) ==
//
//	/\ IsFollower(n)
//	/\ durabilitylog[n] /= {}
//	/\ log' = [log EXCEPT ![n] = Append(log[n], [type : {"apply"}, val : CHOOSE v \in Values : TRUE])]
func ApplyCommitted(m *Manager, nodeID string) error {
	m.Lock()
	defer m.Unlock()

	// Check if node is follower
	state, exists := m.state[nodeID]
	if !exists || state != Follower {
		return fmt.Errorf("node %s is not a follower", nodeID)
	}

	// Check if durability log is not empty
	if len(m.durabilitylog[nodeID]) == 0 {
		return fmt.Errorf("durability log for follower %s is empty", nodeID)
	}

	// Get the last entry from follower's durability log
	lastEntry := m.durabilitylog[nodeID][len(m.durabilitylog[nodeID])-1]

	// Append apply entry to follower's replicated log
	applyEntry := common.LogEntry{
		Index:   len(m.log[nodeID]) + 1,
		Term:    lastEntry.Term,
		Type:    common.IoniaMsgApply,
		Value:   lastEntry.Value,
		From:    lastEntry.From,
		Command: fmt.Sprintf("apply:%d", lastEntry.Value),
	}
	m.log[nodeID] = append(m.log[nodeID], applyEntry)
	// Update local log if this is the local node
	if nodeID == m.ID.String() {
		m.Log = append(m.Log, applyEntry)
	}

	return nil
}

// RPC Handlers for IONIA operations

// IoniaWrite handles write requests from clients
func (m *Manager) IoniaWrite(args *common.IoniaWriteArgs, reply *common.IoniaWriteReply) error {
	nodeID := m.ID.String()

	// Check if this node is leader or follower
	if !IsLeader(m, nodeID) && !IsFollower(m, nodeID) {
		reply.Success = false
		reply.Term = m.currentTerm[nodeID]
		return fmt.Errorf("node is not a leader or follower")
	}

	// Create client request
	req := common.ClientRequest{
		ClientID:  args.ClientID,
		Type:      common.IoniaMsgWrite,
		Value:     args.Value,
		RequestID: args.RequestID,
	}

	// Add to client requests
	m.Lock()
	m.clientRequests[args.RequestID] = req
	m.Unlock()

	// Process the write request
	if IsLeader(m, nodeID) {
		err := LeaderReceiveWrite(m, nodeID)
		if err != nil {
			reply.Success = false
			reply.Term = m.currentTerm[nodeID]
			return err
		}
	} else {
		err := FollowerReceiveWrite(m, nodeID)
		if err != nil {
			reply.Success = false
			reply.Term = m.currentTerm[nodeID]
			return err
		}
	}

	reply.Success = true
	reply.Term = m.currentTerm[nodeID]
	return nil
}

// IoniaOrder handles order messages from leader to follower
func (m *Manager) IoniaOrder(args *common.IoniaOrderArgs, reply *common.IoniaOrderReply) error {
	followerID := m.ID.String()

	// Verify this is a follower
	if !IsFollower(m, followerID) {
		reply.Success = false
		reply.Term = m.currentTerm[followerID]
		return fmt.Errorf("node is not a follower")
	}

	// Add order entry to durability log
	m.Lock()
	orderEntry := common.LogEntry{
		Index:   len(m.durabilitylog[followerID]) + 1,
		Term:    args.Term,
		Type:    common.IoniaMsgOrder,
		Value:   args.Entry.Value,
		From:    args.LeaderID,
		Command: fmt.Sprintf("order:%d", args.Entry.Value),
	}
	m.durabilitylog[followerID] = append(m.durabilitylog[followerID], orderEntry)
	m.Unlock()

	// Process the order
	err := FollowerReceiveOrder(m, followerID)
	if err != nil {
		reply.Success = false
		reply.Term = m.currentTerm[followerID]
		return err
	}

	reply.Success = true
	reply.Term = m.currentTerm[followerID]
	reply.FollowerID = followerID
	reply.Index = args.Index
	return nil
}

// IoniaAckOrder handles order acknowledgments from followers
func (m *Manager) IoniaAckOrder(args *common.IoniaOrderReply, reply *common.IoniaOrderReply) error {
	leaderID := m.ID.String()

	// Verify this is a leader
	if !IsLeader(m, leaderID) {
		reply.Success = false
		reply.Term = m.currentTerm[leaderID]
		return fmt.Errorf("node is not a leader")
	}

	// Update match index for the follower
	m.Lock()
	if m.matchIndex[leaderID] == nil {
		m.matchIndex[leaderID] = make(map[string]int)
	}
	m.matchIndex[leaderID][args.FollowerID] = args.Index
	m.Unlock()

	reply.Success = true
	reply.Term = m.currentTerm[leaderID]
	return nil
}

// IoniaCommit handles commit messages from leader
func (m *Manager) IoniaCommit(args *common.IoniaCommitArgs, reply *common.IoniaCommitReply) error {
	followerID := m.ID.String()

	// Verify this is a follower
	if !IsFollower(m, followerID) {
		reply.Success = false
		reply.Term = m.currentTerm[followerID]
		return fmt.Errorf("node is not a follower")
	}

	// Update commit index
	m.Lock()
	if args.Index > m.commitIndex[followerID] {
		m.commitIndex[followerID] = args.Index
	}
	m.Unlock()

	// Apply committed entries
	err := ApplyCommitted(m, followerID)
	if err != nil {
		reply.Success = false
		reply.Term = m.currentTerm[followerID]
		return err
	}

	reply.Success = true
	reply.Term = m.currentTerm[followerID]
	return nil
}

// IoniaRead handles read requests from clients
func (m *Manager) IoniaRead(args *common.IoniaReadArgs, reply *common.IoniaReadReply) error {
	nodeID := m.ID.String()

	// Verify this is a leader (reads go to leader in IONIA)
	if !IsLeader(m, nodeID) {
		reply.Success = false
		return fmt.Errorf("node is not a leader")
	}

	// For now, return a default value
	// In a real implementation, this would read from the state machine
	reply.Value = 0
	reply.Success = true
	reply.RequestID = args.RequestID
	return nil
}

// Invariant checking functions

// CheckLogConsistency checks the LogConsistency invariant
// LogConsistency ==
//
//	/\  \A n1, n2 \in Nodes:
//	        \A i \in 1..Min(Len(log[n1]), Len(log[n2])) :
//	            /\   commitIndex[n1] >= i
//	            /\   commitIndex[n2] >= i
//	            /\   log[n1][i].term = log[n2][i].term
func CheckLogConsistency(m *Manager, nodes []string) bool {
	m.Lock()
	defer m.Unlock()

	// Check replicated log consistency
	for i, n1 := range nodes {
		for j, n2 := range nodes {
			if i >= j {
				continue
			}
			log1 := m.log[n1]
			log2 := m.log[n2]
			minLen := len(log1)
			if len(log2) < minLen {
				minLen = len(log2)
			}
			for idx := 0; idx < minLen; idx++ {
				// Check commitIndex bounds
				if m.commitIndex[n1] <= idx || m.commitIndex[n2] <= idx {
					continue // Not committed yet, skip
				}
				// Check term consistency
				if log1[idx].Term != log2[idx].Term {
					return false
				}
			}
		}
	}

	// Check durability log consistency
	for i, n1 := range nodes {
		for j, n2 := range nodes {
			if i >= j {
				continue
			}
			log1 := m.durabilitylog[n1]
			log2 := m.durabilitylog[n2]
			minLen := len(log1)
			if len(log2) < minLen {
				minLen = len(log2)
			}
			for idx := 0; idx < minLen; idx++ {
				// Check durabilityCommitIndex bounds
				if m.durabilityCommitIndex[n1] <= idx || m.durabilityCommitIndex[n2] <= idx {
					continue // Not committed yet, skip
				}
				// Check term consistency
				if log1[idx].Term != log2[idx].Term {
					return false
				}
			}
		}
	}

	return true
}

// CheckCommitIndexMonotonic checks the CommitIndexMonotonic invariant
// CommitIndexMonotonic ==
//
//	/\  \A n \in Nodes : commitIndex[n] >= 0
//	/\  \A n \in Nodes : durabilityCommitIndex[n] >= 0
func CheckCommitIndexMonotonic(m *Manager, nodes []string) bool {
	m.Lock()
	defer m.Unlock()

	for _, node := range nodes {
		if m.commitIndex[node] < 0 {
			return false
		}
		if m.durabilityCommitIndex[node] < 0 {
			return false
		}
	}

	return true
}

// CheckAppliedIndexBounded checks the AppliedIndexBounded invariant
// AppliedIndexBounded ==
//
//	/\  \A n \in Nodes : appliedIndex[n] <= commitIndex[n]
//	/\  \A n \in Nodes : appliedIndex[n] <= durabilityCommitIndex[n]
func CheckAppliedIndexBounded(m *Manager, nodes []string) bool {
	m.Lock()
	defer m.Unlock()

	for _, node := range nodes {
		if m.appliedIndex[node] > m.commitIndex[node] {
			return false
		}
		if m.appliedIndex[node] > m.durabilityCommitIndex[node] {
			return false
		}
	}

	return true
}

// CheckLeaderUniqueness checks the LeaderUniqueness invariant
// LeaderUniqueness == Cardinality({n \in Nodes : IsLeader(n)}) <= 1
func CheckLeaderUniqueness(m *Manager, nodes []string) bool {
	m.Lock()
	defer m.Unlock()

	leaderCount := 0
	for _, node := range nodes {
		if state, exists := m.state[node]; exists && state == Leader {
			leaderCount++
		}
	}

	return leaderCount <= 1
}
