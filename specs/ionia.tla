---- MODULE ionia ----
EXTENDS TLC

CONSTANT Nodes, Clients

Leader == \E n \in Nodes: Leader \notin Nodes

Followers == Nodes # {Leader}

AllNodes == {Leader \union Followers \union Clients}


msg == [type: {"read", "reqs" , "meta", "order", "apply", "data", "commit", "sync"}]

(*--algorithm ionia
\* means x is the value associated with the data being persisted
\* 
variables x = 0, log = [q \in AllNodes |-> <<>>];

macro send(id, msg) begin
    queues := Append(queues[id], msg);
end macro;

macro receive(msg) begin
    await Len(queues[self] > 0);
    msg := Head(queues[self]);
    queues := Tail(queues[self]);
end macro;

process Leader \in Leader
variable leaderlog = <<>>;
begin
    GetClientRequest:
        if leaderlog /= <<>> then
            with l \in Leader do
                \* receive({"order"});
            end with;
        end if;
    ProposeToFollowers:
        skip;
    CollectAcks:
        skip;
    CommitToClients:
        skip;  
end process;

process Follower \in Followers
variable followerlog = <<>>;
begin
    GetLeaderPropose:
        skip;
    AckToLeader:
        skip;
    ApplyToStateMachine:
        skip;
    OrderLog:
        skip;
end process;

process Client \in Clients
variable clientlog = <<>>;
begin
    SendRequestToLeader:
        skip;
    WaitForReply:
        skip;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e5858edf" /\ chksum(tla) = "a60c9a41")
VARIABLES pc, x, leaderlog, followerlog, clientlog

vars == << pc, x, leaderlog, followerlog, clientlog >>

ProcSet == (Leader) \cup (Followers) \cup (Clients)

Init == (* Global variables *)
        /\ x = 0
        (* Process Leader *)
        /\ leaderlog = [self \in Leader |-> <<>>]
        (* Process Follower *)
        /\ followerlog = [self \in Followers |-> <<>>]
        (* Process Client *)
        /\ clientlog = [self \in Clients |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in Leader -> "GetClientRequest"
                                        [] self \in Followers -> "GetLeaderPropose"
                                        [] self \in Clients -> "SendRequestToLeader"]

GetClientRequest(self) == /\ pc[self] = "GetClientRequest"
                          /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "ProposeToFollowers"]
                          /\ UNCHANGED << x, leaderlog, followerlog, clientlog >>

ProposeToFollowers(self) == /\ pc[self] = "ProposeToFollowers"
                            /\ TRUE
                            /\ pc' = [pc EXCEPT ![self] = "CollectAcks"]
                            /\ UNCHANGED << x, leaderlog, followerlog, 
                                            clientlog >>

CollectAcks(self) == /\ pc[self] = "CollectAcks"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "CommitToClients"]
                     /\ UNCHANGED << x, leaderlog, followerlog, clientlog >>

CommitToClients(self) == /\ pc[self] = "CommitToClients"
                         /\ TRUE
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << x, leaderlog, followerlog, clientlog >>

Leader(self) == GetClientRequest(self) \/ ProposeToFollowers(self)
                   \/ CollectAcks(self) \/ CommitToClients(self)

GetLeaderPropose(self) == /\ pc[self] = "GetLeaderPropose"
                          /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "AckToLeader"]
                          /\ UNCHANGED << x, leaderlog, followerlog, clientlog >>

AckToLeader(self) == /\ pc[self] = "AckToLeader"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "ApplyToStateMachine"]
                     /\ UNCHANGED << x, leaderlog, followerlog, clientlog >>

ApplyToStateMachine(self) == /\ pc[self] = "ApplyToStateMachine"
                             /\ TRUE
                             /\ pc' = [pc EXCEPT ![self] = "OrderLog"]
                             /\ UNCHANGED << x, leaderlog, followerlog, 
                                             clientlog >>

OrderLog(self) == /\ pc[self] = "OrderLog"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << x, leaderlog, followerlog, clientlog >>

Follower(self) == GetLeaderPropose(self) \/ AckToLeader(self)
                     \/ ApplyToStateMachine(self) \/ OrderLog(self)

SendRequestToLeader(self) == /\ pc[self] = "SendRequestToLeader"
                             /\ TRUE
                             /\ pc' = [pc EXCEPT ![self] = "WaitForReply"]
                             /\ UNCHANGED << x, leaderlog, followerlog, 
                                             clientlog >>

WaitForReply(self) == /\ pc[self] = "WaitForReply"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << x, leaderlog, followerlog, clientlog >>

Client(self) == SendRequestToLeader(self) \/ WaitForReply(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Leader: Leader(self))
           \/ (\E self \in Followers: Follower(self))
           \/ (\E self \in Clients: Client(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


Liveness == \A self \in ProcSet: 

====
