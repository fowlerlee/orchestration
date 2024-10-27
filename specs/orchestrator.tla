---------------------------- MODULE orchestrator ----------------------------
EXTENDS TLC, Naturals, Integers, Sequences

CONSTANT Workers, Manager, Clients

Messages == [type: {"task"}, s: Manager, r: Workers] \union 
            [type: {"working", "completed", "waiting"}, s: Workers, r: Manager] \cup 
            [type: {"inprogress", "finished"}, s: Manager, r: Clients] \cup
            [type: {"doWork"}, s: Clients, r: Manager]
            

Actors == {Workers \union Manager \cup Clients}

(*--algorithm orchestrator

variables msgs = {}, wState = [w \in Workers |-> "waiting"],
            mState = [m \in Manager |-> "ready"],
            cState = [c \in Clients |-> "idle"],
            queues = [q \in Actors |-> <<>>];
            
macro send(id, msg) begin
    queues := Append(queues[id], msg);
end macro;

macro receive(msg) begin
    await Len(queues[self] > 0);
    msg := Head(queues[self]);
    queues := Tail(queues[self]);
end macro;

process worker \in Workers
variable workQueue = <<>>;
begin
    WaitForWork:
        skip;
    PerformWork:
        skip;
        
end process;

process client \in Clients
variable msg = <<>>;
begin
    SendTaskToManager:
        if msg = <<>> then
            with m \in Manager do
                send(self, [type |-> "doWork", s |-> self, r |-> m]);
            end with;
        end if;
    ReceiveTaskFinish:
        with m \in Manager do
            if 
                /\ msgs.type = "finished"
                /\ mState[m] = "done"
            then
                receive(msg);
            else 
                goto SendTaskToManager;
            end if;
        end with;
end process;

process manager \in Manager
begin
    NotifyClientOfCompleteJob:
       if msgs.type = "completed" then
            with c \in Clients do
                send(self, [type |-> "finished", s |-> self, r |-> c]);
            end with;
       end if;
    ReceiveTaskFromClient:
        skip;
    GiveTaskToWorker:
        skip;

end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "901ddb8f" /\ chksum(tla) = "580405ba")
VARIABLES msgs, wState, mState, cState, queues, pc, workQueue, msg

vars == << msgs, wState, mState, cState, queues, pc, workQueue, msg >>

ProcSet == (Workers) \cup (Clients) \cup (Manager)

Init == (* Global variables *)
        /\ msgs = {}
        /\ wState = [w \in Workers |-> "waiting"]
        /\ mState = [m \in Manager |-> "ready"]
        /\ cState = [c \in Clients |-> "idle"]
        /\ queues = [q \in Actors |-> <<>>]
        (* Process worker *)
        /\ workQueue = [self \in Workers |-> <<>>]
        (* Process client *)
        /\ msg = [self \in Clients |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in Workers -> "WaitForWork"
                                        [] self \in Clients -> "SendTaskToManager"
                                        [] self \in Manager -> "NotifyClientOfCompleteJob"]

WaitForWork(self) == /\ pc[self] = "WaitForWork"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "PerformWork"]
                     /\ UNCHANGED << msgs, wState, mState, cState, queues, 
                                     workQueue, msg >>

PerformWork(self) == /\ pc[self] = "PerformWork"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << msgs, wState, mState, cState, queues, 
                                     workQueue, msg >>

worker(self) == WaitForWork(self) \/ PerformWork(self)

SendTaskToManager(self) == /\ pc[self] = "SendTaskToManager"
                           /\ IF msg[self] = <<>>
                                 THEN /\ \E m \in Manager:
                                           queues' = Append(queues[self], ([type |-> "doWork", s |-> self, r |-> m]))
                                 ELSE /\ TRUE
                                      /\ UNCHANGED queues
                           /\ pc' = [pc EXCEPT ![self] = "ReceiveTaskFinish"]
                           /\ UNCHANGED << msgs, wState, mState, cState, 
                                           workQueue, msg >>

ReceiveTaskFinish(self) == /\ pc[self] = "ReceiveTaskFinish"
                           /\ \E m \in Manager:
                                IF /\ msgs.type = "finished"
                                   /\ mState[m] = "done"
                                   THEN /\ Len(queues[self] > 0)
                                        /\ msg' = [msg EXCEPT ![self] = Head(queues[self])]
                                        /\ queues' = Tail(queues[self])
                                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "SendTaskToManager"]
                                        /\ UNCHANGED << queues, msg >>
                           /\ UNCHANGED << msgs, wState, mState, cState, 
                                           workQueue >>

client(self) == SendTaskToManager(self) \/ ReceiveTaskFinish(self)

NotifyClientOfCompleteJob(self) == /\ pc[self] = "NotifyClientOfCompleteJob"
                                   /\ IF msgs.type = "completed"
                                         THEN /\ \E c \in Clients:
                                                   queues' = Append(queues[self], ([type |-> "finished", s |-> self, r |-> c]))
                                         ELSE /\ TRUE
                                              /\ UNCHANGED queues
                                   /\ pc' = [pc EXCEPT ![self] = "ReceiveTaskFromClient"]
                                   /\ UNCHANGED << msgs, wState, mState, 
                                                   cState, workQueue, msg >>

ReceiveTaskFromClient(self) == /\ pc[self] = "ReceiveTaskFromClient"
                               /\ TRUE
                               /\ pc' = [pc EXCEPT ![self] = "GiveTaskToWorker"]
                               /\ UNCHANGED << msgs, wState, mState, cState, 
                                               queues, workQueue, msg >>

GiveTaskToWorker(self) == /\ pc[self] = "GiveTaskToWorker"
                          /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << msgs, wState, mState, cState, queues, 
                                          workQueue, msg >>

manager(self) == NotifyClientOfCompleteJob(self)
                    \/ ReceiveTaskFromClient(self)
                    \/ GiveTaskToWorker(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Workers: worker(self))
           \/ (\E self \in Clients: client(self))
           \/ (\E self \in Manager: manager(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


TypeOK == 
        /\ wState \in [Workers -> {"waiting", "working"}]
        /\ mState \in [Manager -> {"ready", "busy", "jobComplete"}]
        /\ cState \in [Clients -> {"assignTask", "idle"}]
        /\ msgs \subseteq Messages
        


=============================================================================
\* Modification History
\* Last modified Mon Mar 11 10:40:22 CET 2024 by lee
\* Created Fri Mar 08 22:22:11 CET 2024 by lee
