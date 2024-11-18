package manager

import (
	"context"
	"math/rand"
	"time"

	"github.com/fowlerlee/orchestration/common"
)



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
	if m.Term < args.Term {
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
	go m.SendHeartbeats(context.Background())
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

func (m *Manager) SendHeartbeats(c context.Context) {
	rpcMethod := "Manager.ReceiveHeartbeat"
	duration := time.Duration(rand.Intn(300))
	ticker := time.NewTicker(duration)
	defer ticker.Stop()
	for {
		select {
		case <-ticker.C:
			for _, managerAddr := range m.OtherManagers {
				go func(managerAddr string) {
					args := &common.HeartbeatArgs{
						Term:     m.Term,
						LeaderID: m.ID.String(),
					}
					reply := &common.HeartbeatReply{}

					ok := common.RpcCall(managerAddr, rpcMethod, args, reply)
					m.Lock()
					defer m.Unlock()
					if ok {
						if m.Term > reply.Term {
							// m has higher term so starts another election.
							m.StartLeaderElection()
						}
					}
				}(managerAddr)
			}
		case <-m.shutdown:
			return
		}
	}
}

func (m *Manager) ReceiveHeartbeat(args *common.HeartbeatArgs, reply *common.HeartbeatReply) error {
	m.Lock()
	defer m.Unlock()
	if m.Term <= args.Term {
		m.State = Follower
		m.Term = args.Term
		m.LeaderAddress = args.LeaderID
		m.LastHeartbeat = time.Now()
	} else {
		reply.Term = m.Term
	}
	return nil
}
