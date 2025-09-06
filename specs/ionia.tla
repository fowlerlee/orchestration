---- MODULE ionia ----

(* The following is a spec to describe Inonia from the work of Xu et al. 2024 and all credit goes the authors*)
(* IonIa: High-Performance Replication for Modern Disk-based KV Stores *)

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Clients, MaxLogSize, NULL, Values

ASSUME Cardinality(Nodes) >= 3  \* Need majority for consensus
ASSUME NULL \notin Nat \* Null is not a natural number
ASSUME Values \subseteq Nat /\ Cardinality(Values) > 0  \* Finite set of possible values

(* Helpful definitions *)
AllActors == Nodes \cup Clients
(* Common module not importable - change later *)
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a <= b THEN b ELSE a

(* Message types - check if we should encode these value to 1.. N so that its easier to enumerate *)
MessageType == {"read", "write", "propose", "ack", "commit", "apply", "sync"}

(* Message structure *)
Message == [type: MessageType, 
            seq: Nat, 
            value: Values, 
            from: AllActors,
            to: AllActors,
            term: Nat]

(* Process types *)
Leader == CHOOSE n \in Nodes: TRUE  \* Single leader
Followers == Nodes \ {Leader}

(* State variables *)
VARIABLES 
    log,                   \* Replicated log: [node -> sequence of operations]
    commitIndex,           \* [node -> Nat] - highest committed index per node
    appliedIndex,          \* [node -> Nat] - highest applied index per node
    nextIndex,             \* [leader -> [follower -> Nat]] - next log entry to send
    matchIndex,            \* [leader -> [follower -> Nat]] - highest known match
    currentTerm,           \* [node -> Nat] - current term per node
    votedFor,              \* [node -> Nodes \cup {NULL}] - candidate voted for
    state,                 \* [node -> {"leader", "follower", "candidate"}]
    messages,              \* [node -> sequence of messages]
    clientRequests,        \* Pending client requests
    clientResponses        \* Responses to send to clients


(* Helper functions *)
Majority == {S \in SUBSET Nodes : Cardinality(S) > Cardinality(Nodes) \div 2}

IsLeader(n) == state[n] = "leader"

IsFollower(n) == state[n] = "follower"

GetLastLogIndex(n) == Len(log[n])

GetLastLogTerm(n) == IF log[n] = {} THEN 0 ELSE log[n][Len(log[n])].term

(* Safety properties *)
TypeInvarient == 
            /\ log \in [Nodes -> SUBSET Message]
            /\ commitIndex \in [Nodes -> Nat]
            /\ appliedIndex \in [Nodes -> Nat]
            /\ nextIndex \in [Nodes -> [Followers -> Nat]]
            /\ matchIndex \in [Nodes -> [Followers -> Nat]]
            /\ currentTerm \in [Nodes -> Nat]
            /\ state \in [Nodes -> {"leader", "follower", "candidate"}]
            /\ clientRequests \in SUBSET Message
            /\ clientResponses \in SUBSET Message
            /\ messages \in [Nodes -> SUBSET Message]

(* Initial state *)
Init == /\ log = [n \in Nodes |-> {}]
        /\ commitIndex = [n \in Nodes |-> 0]
        /\ appliedIndex = [n \in Nodes |-> 0]
        /\ nextIndex = [n \in Nodes |-> [f \in Followers |-> 1]]
        /\ matchIndex = [n \in Nodes |-> [f \in Followers |-> 0]]
        /\ currentTerm = [n \in Nodes |-> 0]
        /\ votedFor = [n \in Nodes |-> NULL]
        /\ state = [n \in Nodes |-> IF n = Leader THEN "leader" ELSE "follower"]
        /\ clientRequests = {}
        /\ clientResponses = {}
        /\ messages = [n \in Nodes |-> {}]

(* Client sends write request *)
ClientWriteRequest(c) == 
    /\ c \in Clients
    /\ \E l \in Nodes : 
        /\  l = Leader /\ l \notin Followers
    (* FIXME: this type is not enumerable by the model checker since its strings - maybe encode as 1.. N *)
        /\ LET newReq == [type: "write", value: CHOOSE v \in Values : TRUE, from: c, to: l, term: currentTerm[l]]
            IN
            /\ clientRequests' = clientRequests \cup newReq
            /\ UNCHANGED << log, commitIndex, appliedIndex, nextIndex, matchIndex, 
                            currentTerm, votedFor, state, messages, clientResponses >>

(* Leader receives client request and proposes *)
LeaderPropose(l) == 
    /\ IsLeader(l) /\ l \notin Followers
    /\ clientRequests /= {}
    /\ \E c \in Clients :
        /\ LET newEntry == [type: "write", value: CHOOSE v \in Values : TRUE, from: l, to: c, term: currentTerm[l]]
            IN  /\ log' = [log EXCEPT ![l] = (log[l] \cup newEntry)]
                /\ messages' = [messages EXCEPT ![l] = (messages[l] \cup newEntry)]
                /\ clientRequests' = clientRequests \cup newEntry
                /\ UNCHANGED << commitIndex, appliedIndex, nextIndex, matchIndex, 
                                currentTerm, votedFor, state, messages, clientResponses >>

(* Leader sends proposal to followers *)
LeaderSendProposal(l, f) == 
    /\ IsLeader(l)
    /\ f \in Followers
    /\ nextIndex[l][f] <= Len(log[l])
    /\ LET entry == log[l][nextIndex[l][f]]
           msg == [type: "propose", seq: nextIndex[l][f], value: entry.value, 
                   from: entry.from, to: entry.to, term: currentTerm[l]]
        IN  /\ messages' = [messages EXCEPT ![f] = messages[f] \cup msg]
            /\ nextIndex' = [nextIndex EXCEPT ![l][f] = nextIndex[l][f] + 1]
            /\ UNCHANGED << log, commitIndex, appliedIndex, matchIndex, 
                            currentTerm, votedFor, state, clientRequests, clientResponses >>

(* Follower receives proposal and acknowledges *)
FollowerReceiveProposal(f) == 
    /\ IsFollower(f)
    /\ messages[f] /= {}
    /\ LET msg == Head(messages[f])
        IN  /\ msg.type = "propose"
             \* Accept if log is consistent
            /\ (msg.seq = 1 \/ (msg.seq <= Len(log[f]) + 1 /\ 
                                (msg.seq = 1 \/ log[f][msg.seq - 1].term = msg.term - 1)))
            /\ log' = [log EXCEPT ![f] = IF msg.seq <= Len(log[f]) 
                                            THEN [log[f] EXCEPT ![msg.seq] = [type: msg.type, value: msg.value, 
                                                                                from: msg.from, to: msg.to, term: msg.term]]
                                            ELSE Append(log[f], [type: msg.type, value: msg.value, 
                                                            from: msg.from, to: msg.to, term: msg.term])]
       /\ messages' = [messages EXCEPT ![f] = Tail(messages[f])]
       /\ \* Send acknowledgment
       /\ LET ackMsg == [type: "ack", seq: msg.seq, value: msg.value, 
                         from: msg.from, to: msg.to, term: currentTerm[f]]
            IN  /\ messages' = [messages' EXCEPT ![Leader] = Append(messages'[Leader], ackMsg)]
                /\ UNCHANGED << commitIndex, appliedIndex, nextIndex, matchIndex, 
                            currentTerm, votedFor, state, clientRequests, clientResponses >>

(* Leader collects acknowledgments and commits *)
LeaderCommit(l) == 
    /\ IsLeader(l)
    /\ messages[l] /= <<>>
    /\ LET msg == Head(messages[l])
        IN /\ msg.type = "ack"
        /\ matchIndex' = [matchIndex EXCEPT ![l][msg.from] = msg.seq]
        /\ \* Check if majority has acknowledged
        /\ LET ackedFollowers == {f \in Followers : matchIndex'[l][f] >= msg.seq}
            IN  /\ Cardinality(ackedFollowers) + 1 >= Cardinality(Nodes) \div 2 + 1
                /\ commitIndex' = [commitIndex EXCEPT ![l] = msg.seq]
                /\ messages' = [messages EXCEPT ![l] = Tail(messages[l])]
                /\ UNCHANGED << log, appliedIndex, nextIndex, currentTerm, votedFor, 
                                state, clientRequests, clientResponses >>

(* Apply committed entries to state machine *)
ApplyCommitted(n) == 
    /\ n \in Nodes
    /\ appliedIndex[n] < commitIndex[n]
    /\ appliedIndex' = [appliedIndex EXCEPT ![n] = appliedIndex[n] + 1]
     \* Apply the operation to state machine (simplified)
    /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, currentTerm, 
                    votedFor, state, messages, clientRequests, clientResponses >>

(* Send response to client *)
SendClientResponse(l) == 
    /\ IsLeader(l)
    /\ clientResponses /= <<>>
    /\ LET resp == Head(clientResponses)
        IN  /\ clientResponses' = Tail(clientResponses)
            /\ UNCHANGED << log, commitIndex, appliedIndex, nextIndex, matchIndex, 
                        currentTerm, votedFor, state, messages, clientRequests >>

(* Next state relation *)
Next == \/ \E c \in Clients : ClientWriteRequest(c)
        \/ \E l \in Leader : LeaderPropose(l)
        \/ \E l \in Leader, f \in Followers : LeaderSendProposal(l, f)
        \/ \E f \in Followers : FollowerReceiveProposal(f)
        \/ \E l \in Leader : LeaderCommit(l)
        \/ \E n \in Nodes : ApplyCommitted(n)
        \/ \E l \in Leader : SendClientResponse(l)

(* all the variables grouped for the no change on Next not taking place *)
vars == << log, commitIndex, appliedIndex, nextIndex, matchIndex, 
           currentTerm, votedFor, state, messages, clientRequests, clientResponses >>

(* Specification *)
Spec == Init /\ [][Next]_vars

(* Liveness properties to prove no data loss and always making progress and resilience to failures *)
EventuallyCommitted == \A n \in Nodes : <> (appliedIndex[n] = commitIndex[n])

ClientRequestEventuallyProcessed == 
    \A c \in Clients : 
        <> (clientRequests = <<>> \/ \E n \in Nodes : 
                \E i \in 1..Len(log[n]) : log[n][i].from = c)

NoDataLoss == 
    \A n1, n2 \in Nodes:
        \A i \in 1..Min(Len(log[n1]), Len(log[n2])) :
            /\ commitIndex[n1] >= i
            /\ commitIndex[n2] >= i
            /\ log[n1][i] = log[n2][i]

LeaderEventuallyActive == 
    <> (IsLeader(Leader) /\ \A f \in Followers : IsFollower(f))

SystemEventuallyResponsive == 
    \A c \in Clients : 
        <> (clientResponses /= <<>> \/ clientRequests = <<>>)

ProgressEventuallyMade == 
    <> (commitIndex[Leader] > 0 \/ clientRequests = <<>>)

(* Resilience & Fault Tolerance Properties *)
MajorityConsensusEventuallyReached == 
    \A i \in 1..MaxLogSize :
        <> (Cardinality({n \in Nodes : commitIndex[n] >= i}) > Cardinality(Nodes) \div 2)

   SystemRecoversFromStalls == 
       <> (messages = [n \in Nodes |-> <<>>] \/ 
           \E n \in Nodes : messages[n] /= <<>>)

LeaderEventuallyCommits == 
    IsLeader(Leader) => <> (commitIndex[Leader] > 0)

FollowersEventuallySync == 
    \A f \in Followers :
        <> (Len(log[f]) = Len(log[Leader]) \/ 
            \E i \in 1..Min(Len(log[f]), Len(log[Leader])) : 
                log[f][i] = log[Leader][i])

(*Critical Invariants to Add*)
LogConsistency == 
    \A n1, n2 \in Nodes:    
        \A i \in 1..Min(Len(log[n1]), Len(log[n2])) :
             /\   commitIndex[n1] >= i 
             /\   commitIndex[n2] >= i
             /\   log[n1][i].term = log[n2][i].term

CommitIndexMonotonic == 
    \A n \in Nodes : commitIndex[n] >= 0

AppliedIndexBounded == 
    \A n \in Nodes : appliedIndex[n] <= commitIndex[n]

LeaderUniqueness == 
    Cardinality({n \in Nodes : IsLeader(n)}) <= 1

MessageIntegrity == 
    \A n \in Nodes : 
        \A i \in 1..Len(messages[n]) : 
            messages[n][i].term <= currentTerm[n]

====
