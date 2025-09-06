---- MODULE ionia ----

(* The following is a spec to describe Inonia from the work of Xu et al. 2024 and all credit goes the authors*)
(* IonIa: High-Performance Replication for Modern Disk-based KV Stores *)

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Clients, MaxLogSize, NULL, Values

ASSUME Cardinality(Nodes) >= 3  \* Need majority for consensus
ASSUME NULL \notin Nat \* Null is not a natural number
ASSUME Values \subseteq Nat /\ Cardinality(Values) > 0  \* Finite set of possible values

(* State variables *)
VARIABLES 
    log,                   \* Replicated log: [node -> sequence of operations]
    durabilitylog,         \* Durability log: [node -> sequence of operations]
    durabilityCommitIndex, \* [node -> Nat] - highest durability committed index per node
    commitIndex,           \* [node -> Nat] - highest committed index per node
    appliedIndex,          \* [node -> Nat] - highest applied index per node
    nextIndex,             \* [leader -> [follower -> Nat]] - next log entry to send
    matchIndex,            \* [leader -> [follower -> Nat]] - highest known match
    currentTerm,           \* [node -> Nat] - current term per node
    votedFor,              \* [node -> Nodes \cup {NULL}] - candidate voted for
    state,                 \* [node -> {"leader", "follower", "candidate"}]
    clientRequests,        \* Pending client requests
    clientResponses,        \* Responses to send to clients
    msgs                   \* set of all messages sent

(* Process types *)
Leader == CHOOSE n \in Nodes: TRUE  \* Single leader
Followers == Nodes \ {Leader}

(* Helpful definitions *)
AllActors == Nodes \cup Clients
(* Common module not importable - change later *)
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a <= b THEN b ELSE a

(* this is used as in the Paxos description and Leslie's recommendation *)
Send(m) == msgs' = msgs \cup {m}

Message ==  [type : {"order"}, from : Leader, to : Followers] 
            \* write and order operations for ionia (from leader to followers)
           \cup [type : {"ackOrder"}, from : Followers, to : Leader]
           \cup [type : {"commit"}, from : Leader, to : Followers, val : Values]
           \cup [type : {"write"}, from : Clients, to : Nodes, val : Values]
           \cup [type: {"ackWrite"}, from : Nodes, to : Clients]
           (* leader read operations for ionia *)
           \cup [type : {"read"}, from : Clients, to : Leader]
           \cup [type : {"respRead"}, from : Leader, to : Clients, val : Values]
           (* follower read operations for ionia *)
           \cup [type : {"request"}, from : Clients, to : Nodes, val: Values] 
           \cup [type : {"metadata"}, from: Leader, to: Clients]
           \cup [type: {"respRead"}, from: Followers, to: Clients, val: Values]

(* Helper functions *)
Majority == {S \in SUBSET Nodes : Cardinality(S) > Cardinality(Nodes) \div 2}

IsLeader(n) == state[n] = "leader"

IsFollower(n) == state[n] = "follower"

GetLastLogIndex(n) == Len(log[n])

GetLastLogTerm(n) == IF log[n] = {} THEN 0 ELSE log[n][Len(log[n])].term

(* Safety properties *)
TypeInvarient == 
            /\ log \in [Nodes -> SUBSET Message]
            /\ durabilitylog \in [Nodes -> SUBSET Message]
            /\ durabilityCommitIndex \in [Nodes -> Nat]
            /\ commitIndex \in [Nodes -> Nat]
            /\ appliedIndex \in [Nodes -> Nat]
            /\ nextIndex \in [Nodes -> [Followers -> Nat]]
            /\ matchIndex \in [Nodes -> [Followers -> Nat]]
            /\ currentTerm \in [Nodes -> Nat]
            /\ state \in [Nodes -> {"leader", "follower"}]
            /\ clientRequests \in SUBSET Message
            /\ clientResponses \in SUBSET Message
            /\ msgs \subseteq Message

(* Initial state *)
Init == /\ log = [n \in Nodes |-> {}]
        /\ durabilitylog = [n \in Nodes |-> {}]
        /\ durabilityCommitIndex = [n \in Nodes |-> 0]
        /\ commitIndex = [n \in Nodes |-> 0]
        /\ appliedIndex = [n \in Nodes |-> 0]
        /\ nextIndex = [n \in Nodes |-> [f \in Followers |-> 1]]
        /\ matchIndex = [n \in Nodes |-> [f \in Followers |-> 0]]
        /\ currentTerm = [n \in Nodes |-> 0]
        /\ votedFor = [n \in Nodes |-> NULL]
        /\ state = [n \in Nodes |-> IF n = Leader THEN "leader" ELSE "follower"]
        /\ clientRequests = {}
        /\ clientResponses = {}

(* Client sends write request *)
ClientWriteRequest(c) == 
    /\ c \in Clients
    /\ \E l \in Nodes : 
        /\  l = Leader /\ l \notin Followers
        /\ Send([type: "write", from: c, to: l, val: CHOOSE v \in Values : TRUE])
        /\ UNCHANGED << log, durabilitylog, durabilityCommitIndex, commitIndex, appliedIndex, nextIndex, matchIndex, 
                            currentTerm, votedFor, state, clientResponses >>

(* Leader receives client request and proposes *)
LeaderBackgroudOrder(l, f) == 
    /\ IsLeader(l) /\ l \notin Followers
    /\ clientRequests /= {}
    /\ Send([type : {"order"}, from : l, to : f])
    /\ log' = [log EXCEPT ![l] = Append(log[l], [type : {"write"}, from : Clients, to : Nodes, val : Values])]
    /\ UNCHANGED << log, durabilitylog, durabilityCommitIndex, commitIndex, appliedIndex, nextIndex, matchIndex, 
                                currentTerm, votedFor, state, clientResponses >>

(* Leader sends proposal to followers *)
LeaderApply(l) == 
    /\ IsLeader(l) 
    /\ nextIndex[l][f] <= Len(log[l])
    /\ LET entry == log[l][nextIndex[l][f]]
           msg == [type: 3, seq: nextIndex[l][f], value: entry.value, 
                   from: entry.from, to: entry.to, term: currentTerm[l]]
            /\ nextIndex' = [nextIndex EXCEPT ![l][f] = nextIndex[l][f] + 1]
            /\ UNCHANGED << log, durabilitylog, durabilityCommitIndex, commitIndex, appliedIndex, matchIndex, 
                            currentTerm, votedFor, state, clientRequests, clientResponses >>

(* Follower receives proposal and acknowledges *)
FollowerReceiveProposal(f) == 
        /\ IsFollower(f)
        /\ state[f] = "follower"
            IN  /\ msg.type = 3
                \* Accept if log is consistent
                /\ (msg.seq = 1 \/ (msg.seq <= Len(log[f]) + 1 /\ 
                                    (msg.seq = 1 \/ log[f][msg.seq - 1].term = msg.term - 1)))
                /\ log' = [log EXCEPT ![f] = IF msg.seq <= Len(log[f]) 
                                                THEN [log[f] EXCEPT ![msg.seq] = [type: msg.type, value: msg.value, 
                                                                                    from: msg.from, to: msg.to, term: msg.term]]
                                                ELSE Append(log[f], [type: msg.type, value: msg.value, 
                                                                from: msg.from, to: msg.to, term: msg.term])]
        /\ \* Send acknowledgment
        /\ LET ackMsg == [type: 4, seq: msg.seq, value: msg.value, 
                            from: msg.from, to: msg.to, term: currentTerm[f]]
                    /\ UNCHANGED << log, durabilitylog, durabilityCommitIndex, commitIndex, appliedIndex, nextIndex, matchIndex, 
                                currentTerm, votedFor, state, clientRequests, clientResponses >>

(* Leader collects acknowledgments and commits *)
LeaderCommit(l) ==  /\ IsLeader(l) 
                    /\ state[l] = "leader"
                    /\ UNCHANGED << log, durabilitylog, durabilityCommitIndex, appliedIndex, nextIndex, currentTerm, votedFor, 
                                    state, clientRequests, clientResponses >>

(* Apply committed entries to state machine *)
ApplyCommitted(n) == 
            /\ n \in Nodes
            /\ state[n] = "leader"
            /\ appliedIndex[n] < commitIndex[n]
            /\ appliedIndex' = [appliedIndex EXCEPT ![n] = appliedIndex[n] + 1]
            \* Apply the operation to state machine (simplified)
            /\ UNCHANGED << log, durabilitylog, durabilityCommitIndex, commitIndex, nextIndex, matchIndex, currentTerm, 
                            votedFor, state, clientRequests, clientResponses, msgs>>

(* Send response to client *)
SendClientResponse(l) == 
                /\ IsLeader(l)
                /\ clientResponses /= {}
                /\ LET resp == Head(clientResponses)
                    IN  /\ clientResponses' = Tail(clientResponses)
                        /\ UNCHANGED << log, durabilitylog, durabilityCommitIndex, commitIndex, appliedIndex, nextIndex, matchIndex, 
                                    currentTerm, votedFor, state, clientRequests, clientResponses>>

(* Next state relation *)
Next ==     \/  \E c \in Clients : ClientWriteRequest(c)
            \/  \E l \in Leader : LeaderBackgroudOrder(l)
            \/  \E l \in Leader : LeaderApply(l)
            \/  \E f \in Followers : FollowerReceiveProposal(f)
            \/  \E l \in Leader : LeaderCommit(l)
            \/  \E n \in Nodes : ApplyCommitted(n)
            \/  \E l \in Leader : SendClientResponse(l)

(* all the variables grouped for the no change on Next not taking place *)
vars ==  << log, durabilitylog, durabilityCommitIndex, commitIndex, appliedIndex, nextIndex, matchIndex, 
           currentTerm, votedFor, state, clientRequests, clientResponses, msgs>>

(* Specification *)
Spec ==   Init /\ [][Next]_vars

(* Liveness properties to prove no data loss and always making progress and resilience to failures *)
EventuallyCommitted == \A n \in Nodes : <> (appliedIndex[n] = commitIndex[n])
EventuallyDurabilityCommitted == \A n \in Nodes : <> (appliedIndex[n] = durabilityCommitIndex[n])

ClientRequestEventuallyProcessed == \A c \in Clients : <> (clientRequests = {} \/ \E n \in Nodes : \E i \in 1..Len(log[n]) : log[n][i].from = c)

NoDataLoss == /\   \A n1, n2 \in Nodes:
                    \A i \in 1..Min(Len(log[n1]), Len(log[n2])) :
                        /\ commitIndex[n1] >= i
                        /\ commitIndex[n2] >= i
              /\        /\ log[n1][i] = log[n2][i]

LeaderEventuallyActive == <> (IsLeader(Leader) /\ \A f \in Followers : IsFollower(f))

SystemEventuallyResponsive == \A c \in Clients : <> (clientResponses /= {} \/ clientRequests = {})

ProgressEventuallyMade == <> (commitIndex[Leader] > 0 \/ clientRequests = {})

(* Resilience & Fault Tolerance Properties *)
MajorityConsensusEventuallyReached == \A i \in 1..MaxLogSize : <> (Cardinality({n \in Nodes : commitIndex[n] >= i}) > Cardinality(Nodes) \div 2)

SystemRecoversFromStalls == <> (msgs = [n \in Nodes |-> {}] /\\E n \in Nodes : msgs[n] /= {})

LeaderEventuallyCommits == IsLeader(Leader) => <> (commitIndex[Leader] > 0)

FollowersEventuallySync == \A f \in Followers : <> (Len(log[f]) = Len(log[Leader]) \/ \E i \in 1..Min(Len(log[f]), Len(log[Leader])) : log[f][i] = log[Leader][i])

(*Critical Invariants *)
LogConsistency == 
            /\  \A n1, n2 \in Nodes:    
                    \A i \in 1..Min(Len(log[n1]), Len(log[n2])) :
                        /\   commitIndex[n1] >= i 
                        /\   commitIndex[n2] >= i
                        /\   log[n1][i].term = log[n2][i].term
            /\  \A n1, n2 \in Nodes:    
                    \A i \in 1..Min(Len(durabilitylog[n1]), Len(durabilitylog[n2])) :
                        /\   durabilityCommitIndex[n1] >= i 
                        /\   durabilityCommitIndex[n2] >= i
                        /\   durabilitylog[n1][i].term = durabilitylog[n2][i].term

CommitIndexMonotonic == 
                /\  \A n \in Nodes : commitIndex[n] >= 0
                /\  \A n \in Nodes : durabilityCommitIndex[n] >= 0

AppliedIndexBounded == 
                /\  \A n \in Nodes : appliedIndex[n] <= commitIndex[n]
                /\  \A n \in Nodes : appliedIndex[n] <= durabilityCommitIndex[n]

LeaderUniqueness == Cardinality({n \in Nodes : IsLeader(n)}) <= 1

MessageIntegrity == \A n \in Nodes : \A i \in 1..Len(msgs[n]) : msgs[n][i].term <= currentTerm[n]

==========================

