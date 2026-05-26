---------------------------- MODULE ionia ----------------------------

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
    clientResponses,       \* Responses to send to clients
    msgs                   \* set of all messages sent

(* Process types *)
Leader == CHOOSE n \in Nodes: TRUE  \* Single leader
Followers == Nodes \ {Leader}

(* Helpful definitions *)
AllActors == Nodes \cup Clients
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a <= b THEN b ELSE a

Send(m) == msgs' = msgs \cup {m}

Message ==  [type : {"order"}] 
           \cup [type : {"ackOrder"}, from : Followers, to : Leader]
           \cup [type : {"commit"}, index : Nat]
           \cup [type : {"write"}, val : Values, term : Nat, from : Clients]
           \cup [type : {"apply"}, val : Values, term : Nat, from : Clients]
           \cup [type : {"ackWrite"}, from : Followers, match : Nat]
           \cup [type : {"read"}, from : Clients, to : Leader]
           \cup [type : {"respRead"}, from : Leader, to : Clients, val : Values]
           \cup [type : {"request"}, from : Clients, to : Nodes, val: Values] 
           \cup [type : {"metadata"}, from: Leader, to: Clients]
           \cup [type : {"respRead"}, from: Followers, to: Clients, val: Values]

Majority == {S \in SUBSET Nodes : Cardinality(S) > Cardinality(Nodes) \div 2}

IsLeader(n) == state[n] = "leader"
IsFollower(n) == state[n] = "follower"

GetLastLogIndex(n) == Len(log[n])
GetLastLogTerm(n) == IF log[n] = <<>> THEN 0 ELSE log[n][Len(log[n])].term

TypeInvarient == 
            /\ log \in [Nodes -> Seq(Message)]
            /\ durabilitylog \in [Nodes -> Seq(Message)]
            /\ durabilityCommitIndex \in [Nodes -> Nat]
            /\ commitIndex \in [Nodes -> Nat]
            /\ appliedIndex \in [Nodes -> Nat]
            /\ nextIndex \in [Nodes -> [Followers -> Nat]]
            /\ matchIndex \in [Nodes -> [Followers -> Nat]]
            /\ currentTerm \in [Nodes -> Nat]
            /\ state \in [Nodes -> {"leader", "follower"}]
            /\ clientRequests \in [Clients -> SUBSET Message]
            /\ clientResponses \in [Clients -> SUBSET Message]
            /\ msgs \subseteq Message

Init == /\ log = [n \in Nodes |-> <<>>]
        /\ durabilitylog = [n \in Nodes |-> <<>>]
        /\ durabilityCommitIndex = [n \in Nodes |-> 0]
        /\ commitIndex = [n \in Nodes |-> 0]
        /\ appliedIndex = [n \in Nodes |-> 0]
        /\ nextIndex = [n \in Nodes |-> [f \in Followers |-> 1]]
        /\ matchIndex = [n \in Nodes |-> [f \in Followers |-> 0]]
        /\ currentTerm = [n \in Nodes |-> 0]
        /\ votedFor = [n \in Nodes |-> NULL]
        /\ state = [n \in Nodes |-> IF n = Leader THEN "leader" ELSE "follower"]
        /\ clientRequests = [c \in Clients |-> {}]
        /\ clientResponses = [c \in Clients |-> {}]
        /\ msgs = {}

ClientWriteRequest(c, n) == 
    /\ IsLeader(n) \/ IsFollower(n)
    /\ clientRequests[c] = {} \* only one request at a time
    /\ clientRequests' = [clientRequests EXCEPT ![c] = {[type |-> "write", val |-> CHOOSE v \in Values : TRUE, term |-> currentTerm[n], from |-> c]}]
    /\ Send([type |-> "write", val |-> CHOOSE v \in Values : TRUE, term |-> currentTerm[n], from |-> c])
    /\ UNCHANGED << log, durabilitylog, durabilityCommitIndex, commitIndex, appliedIndex, nextIndex, matchIndex, 
                            currentTerm, votedFor, state, clientResponses >>

LeaderReceiveWrite(n) ==
        /\ IsLeader(n)
        /\ \E c \in Clients :
             /\ clientRequests[c] /= {}
             /\ Len(durabilitylog[n]) < MaxLogSize
             /\ durabilitylog' = [durabilitylog EXCEPT ![n] = Append(durabilitylog[n], [type |-> "write", val |-> CHOOSE v \in Values : TRUE, term |-> currentTerm[n], from |-> c])]
        /\ Send([type |-> "write", val |-> CHOOSE v \in Values : TRUE, term |-> currentTerm[n], from |-> CHOOSE c \in Clients : TRUE]) 
        /\ UNCHANGED << log, durabilityCommitIndex, commitIndex, appliedIndex, nextIndex, matchIndex, 
                                currentTerm, votedFor, state, clientRequests, clientResponses >>

FollowerReceiveWrite(n) == 
        /\ IsFollower(n)
        /\ \E m \in msgs :
             /\ m.type = "write"
             /\ m.term >= currentTerm[n]
             /\ Len(durabilitylog[n]) < MaxLogSize
             /\ durabilitylog' = [durabilitylog EXCEPT ![n] = Append(durabilitylog[n], m)]
             /\ Send([type |-> "ackWrite", from |-> n, match |-> Len(durabilitylog'[n])])
        /\ UNCHANGED << log, durabilityCommitIndex, commitIndex, appliedIndex, nextIndex, matchIndex, 
                                currentTerm, votedFor, state, clientRequests, clientResponses >>

LeaderReceiveAckWrite(n) ==
        /\ IsLeader(n)
        /\ \E m \in msgs :
             /\ m.type = "ackWrite"
             /\ matchIndex[n][m.from] < m.match
             /\ matchIndex' = [matchIndex EXCEPT ![n][m.from] = m.match]
        /\ UNCHANGED << log, durabilitylog, durabilityCommitIndex, commitIndex, appliedIndex, nextIndex, currentTerm, votedFor, state, clientRequests, clientResponses, msgs >>

LeaderCommit(n) ==  
    /\ IsLeader(n) 
    /\ \E N \in 1..Len(durabilitylog[n]):
        /\ N > commitIndex[n]
        /\ Cardinality({f \in Followers : matchIndex[n][f] >= N} \cup {n}) > Cardinality(Nodes) \div 2
        /\ commitIndex' = [commitIndex EXCEPT ![n] = N]
        /\ durabilityCommitIndex' = [durabilityCommitIndex EXCEPT ![n] = N]
        /\ Send([type |-> "commit", index |-> N])
    /\ UNCHANGED << log, durabilitylog, appliedIndex, nextIndex, matchIndex, currentTerm, votedFor, state, clientRequests, clientResponses >>

FollowerReceiveCommit(n) ==
    /\ IsFollower(n)
    /\ \E m \in msgs :
        /\ m.type = "commit"
        /\ m.index > commitIndex[n]
        /\ commitIndex' = [commitIndex EXCEPT ![n] = Min(m.index, Len(durabilitylog[n]))]
        /\ durabilityCommitIndex' = [durabilityCommitIndex EXCEPT ![n] = Min(m.index, Len(durabilitylog[n]))]
    /\ UNCHANGED << log, durabilitylog, appliedIndex, nextIndex, matchIndex, currentTerm, votedFor, state, clientRequests, clientResponses, msgs >>

ApplyCommitted(n) == 
    /\ commitIndex[n] > appliedIndex[n]
    /\ durabilitylog[n] /= <<>>
    /\ log' = [log EXCEPT ![n] = Append(log[n], [type |-> "apply", val |-> durabilitylog[n][appliedIndex[n] + 1].val, term |-> durabilitylog[n][appliedIndex[n] + 1].term, from |-> durabilitylog[n][appliedIndex[n] + 1].from])]
    /\ appliedIndex' = [appliedIndex EXCEPT ![n] = appliedIndex[n] + 1]
    /\ clientRequests' = [clientRequests EXCEPT ![durabilitylog[n][appliedIndex[n] + 1].from] = {}]
    /\ UNCHANGED << durabilitylog, durabilityCommitIndex, commitIndex, nextIndex, matchIndex, currentTerm, 
                    votedFor, state, clientResponses, msgs >>

Next ==    \E c \in Clients, n \in Nodes :
                \/  ClientWriteRequest(c, n)
                \/  LeaderReceiveWrite(n)
                \/  FollowerReceiveWrite(n)
                \/  LeaderReceiveAckWrite(n)
                \/  LeaderCommit(n) 
                \/  FollowerReceiveCommit(n)
                \/  ApplyCommitted(n)

vars ==  << log, durabilitylog, durabilityCommitIndex, commitIndex, appliedIndex, nextIndex, matchIndex, 
           currentTerm, votedFor, state, clientRequests, clientResponses, msgs>>

Spec ==   Init /\ [][Next]_vars /\ WF_vars(Next)

EventuallyCommitted == \A n \in Nodes : <> (appliedIndex[n] = commitIndex[n])
EventuallyDurabilityCommitted == \A n \in Nodes : <> (appliedIndex[n] = durabilityCommitIndex[n])
ClientRequestEventuallyProcessed == \A c \in Clients : <> (clientRequests[c] = {} \/ \E n \in Nodes : \E i \in 1..Len(log[n]) : log[n][i].from = c)
NoDataLoss == \A n1, n2 \in Nodes: 
                  \A i \in 1..Min(Len(log[n1]), Len(log[n2])) : 
                      (commitIndex[n1] >= i /\ commitIndex[n2] >= i) => (log[n1][i] = log[n2][i])
LeaderEventuallyActive == <> (IsLeader(Leader) /\ \A f \in Followers : IsFollower(f))
SystemEventuallyResponsive == \A c \in Clients : <> (clientResponses[c] /= {} \/ clientRequests[c] = {})
ProgressEventuallyMade == <> (commitIndex[Leader] > 0 \/ (\A c \in Clients: clientRequests[c] = {}))
MajorityConsensusEventuallyReached == \A i \in 1..MaxLogSize : <> (Cardinality({n \in Nodes : commitIndex[n] >= i}) > Cardinality(Nodes) \div 2)
SystemRecoversFromStalls == <> (msgs = {} \/ msgs /= {})
LeaderEventuallyCommits == IsLeader(Leader) => <> (commitIndex[Leader] > 0)
FollowersEventuallySync == \A f \in Followers : <> (Len(log[f]) = Len(log[Leader]) \/ \E i \in 1..Min(Len(log[f]), Len(log[Leader])) : log[f][i] = log[Leader][i])
LogConsistency == 
            /\  \A n1, n2 \in Nodes:    
                    \A i \in 1..Min(Len(log[n1]), Len(log[n2])) :
                        /\   commitIndex[n1] >= i 
                        /\   commitIndex[n2] >= i
                        =>   log[n1][i].term = log[n2][i].term
            /\  \A n1, n2 \in Nodes:    
                    \A i \in 1..Min(Len(durabilitylog[n1]), Len(durabilitylog[n2])):
                        /\   durabilityCommitIndex[n1] >= i 
                        /\   durabilityCommitIndex[n2] >= i
                        =>   durabilitylog[n1][i].term = durabilitylog[n2][i].term

CommitIndexMonotonic == 
                /\  \A n \in Nodes : commitIndex[n] >= 0
                /\  \A n \in Nodes : durabilityCommitIndex[n] >= 0

AppliedIndexBounded == 
                /\  \A n \in Nodes : appliedIndex[n] <= commitIndex[n]
                /\  \A n \in Nodes : appliedIndex[n] <= durabilityCommitIndex[n]

LeaderUniqueness == Cardinality({n \in Nodes : IsLeader(n)}) <= 1
MessageIntegrity == \A n \in Nodes : \A i \in 1..Len(log[n]) : log[n][i].term <= currentTerm[n]
========================== END OF SPECIFICATION ==========================
