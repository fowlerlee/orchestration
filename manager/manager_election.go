package manager

import "github.com/fowlerlee/orchestration/common"

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

func (m *Manager) BecomeLeader() {
	m.State = Leader
	m.LeaderAddress = m.ID.String()
	m.CollectWorkerInfo()
	go m.SendHeartbeats()
}

func (m *Manager) CollectWorkerInfo() {

}

func (m *Manager) SendHeartbeats() {

}
