package manager

import (
	"fmt"

)

type PaxosManager struct {
	Manager
	k int
	crand int
	vrand int 
	vval int
	cval int
}

// 2: Task 1 (coordinator)
// 3: upon receiving value v from proposer
// 4: increase c-rnd to an arbitrary unique value
// 5: for all q ∈Qa do send (q, (PHASE 1A, c-rnd))
func (m *PaxosManager) UponReceiveVProposer()  {

}

// 11: Task 3 (coordinator)
// 12: upon receiving (PHASE 1B, rnd, v-rnd, v-val) from Qa
// such that rnd= c-rnd
// 13: 14: let k be the largest v-rnd value received
// let V be the set of (v-rnd,v-val) received with v-rnd= k
// 15: if k= 0 then let c-val be v
// 16: else let c-val be the only v-val in V
// 17: let c-vid be a unique identifier for c-val
// 18: ip-multicast (Qa ∪Nl, (PHASE 2A, c-rnd, c-val, c-vid))
func (m *PaxosManager) CoordinatorMultiCast(msg string, rand int, vrand int, vval int) ()  {
	m.k = vrand
	if m.k == 0 {
		m.cval = vval + vrand
	} else {
		m.cval = vval
	}
	for _, v := range m.OtherManagers {
		m.Send(v, []interface{}{"PHASE 2A", m.crand, m.cval, m.vrand})
	}

}

func (m *PaxosManager) Send(address string, msg []interface{}) () {

}

// 19: Task 4 (acceptor)
// 20: upon ip-delivering (PHASE 2A, c-rnd, c-val, c-vid)
// 21: if c-rnd ≥rnd then
// 22: let rnd be c-rnd
// 23: let v-rnd be c-rnd
// 24: let v-val be c-val
// 25: let v-vid be c-vid
// 26: if p = f irst(ring) then
// 27: send (successor(p, ring), (PHASE 2B, c-rnd, c-vid))
func (m *PaxosManager) AcceptorSend(msg string, crnd int, cval int, cvid int) ()  {

}



// receive value from proposer
func (m *PaxosManager) ReceiveVFromProposer(args *ReceiveVProposer, reply *ReplyProposer) error {

	return fmt.Errorf("not implemented")
}

