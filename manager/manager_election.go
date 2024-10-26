package manager

import (
	"time"

	"github.com/fowlerlee/orchestration/common"
)

type LogEntry struct {
	Index   int
	Term    int
	Command string
}

func (m *Manager) CheckForLeader() bool {
	rpcMethod := "Manager.GetLeaderInfo"
	for _, managerAddr := range m.OtherManagers {
		args := &common.LeaderInfoArgs{
			Term: m.Term,
		}
		reply := &common.LeaderInfoReply{}

		ok := common.RpcCall(managerAddr, rpcMethod, args, reply)
		if ok && reply.HasLeader {
			m.LeaderAddress = reply.LeaderID
			m.Term = reply.Term
			m.State = Follower
			return true
		}
	}
	return false
}

func (m *Manager) GetLeaderInfo(args *common.LeaderInfoArgs, reply *common.LeaderInfoReply) error {
	if m.State == Leader {
		reply.HasLeader = true
		reply.LeaderID = m.ID.String()
	} else if m.LeaderAddress != "" {
		reply.HasLeader = true
		reply.LeaderID = m.LeaderAddress
	} else {
		reply.HasLeader = false
	}
	reply.Term = m.Term
	return nil
}

func (m *Manager) StartLeaderElection() {
	rpcMethod := "Manager.RequestVote"
	m.State = Candidate
	m.Term++
	votesReceived := 1

	for _, managerAddr := range m.OtherManagers {
		args := &common.RequestVoteArgs{
			Term:        m.Term,
			CandidateID: m.ID.String(),
		}
		reply := &common.RequestVoteReply{}

		ok := common.RpcCall(managerAddr, rpcMethod, args, reply)
		if ok && reply.VoteGranted {
			votesReceived++
		}
	}

	if votesReceived > len(m.OtherManagers)/2 {
		m.BecomeLeader()
	} else {
		m.State = Follower
	}
}

func (m *Manager) RequestVote(args *common.RequestVoteArgs, reply *common.RequestVoteReply) error {
	if args.Term > m.Term {
		m.Term = args.Term
		m.State = Follower
		m.LeaderAddress = ""
	}

	if m.Term > args.Term {
		reply.VoteGranted = false
	} else if m.LeaderAddress == "" || m.LeaderAddress == args.CandidateID {
		reply.VoteGranted = true
		m.LeaderAddress = args.CandidateID
	} else {
		reply.VoteGranted = false
	}

	reply.Term = m.Term
	return nil
}

func (m *Manager) BecomeLeader() {
	m.State = Leader
	m.LeaderAddress = m.ID.String()
	m.CollectWorkerInfo()
	go m.SendHeartbeats()
}

func (m *Manager) CollectWorkerInfo() {
	rpcMethod := "Manager.GetWorkerInfo"
	allWorkers := make(map[string][]string)
	for _, managerAddr := range m.OtherManagers {
		args := &common.WorkerInfoArgs{}
		reply := &common.WorkerInfoReply{}

		ok := common.RpcCall(managerAddr, rpcMethod, args, reply)
		if ok {
			allWorkers[managerAddr] = reply.WorkersIPs
		}
	}
	//dont think this is correct - check if it works as it should!!!
	m.Workers = allWorkers[string(m.ID.String())]
}

func (m *Manager) SendHeartbeats() {
	rpcMethod := "Manager.ReceiveHeartbeat"
	for {
		for _, managerAddr := range m.OtherManagers {
			args := &common.HeartbeatArgs{
				Term:     m.Term,
				LeaderID: m.ID.String(),
			}
			reply := &common.HeartbeatReply{}

			common.RpcCall(managerAddr, rpcMethod, args, reply)
		}
		time.Sleep(time.Second)
	}
}

func (m *Manager) ReceiveHeartbeat(args *common.HeartbeatArgs, reply *common.HeartbeatReply) error {
	if args.Term >= m.Term {
		m.Term = args.Term
		m.State = Follower
		m.LeaderAddress = args.LeaderID
		m.LastHeartbeat = time.Now()
	}
	reply.Term = m.Term
	return nil
}
