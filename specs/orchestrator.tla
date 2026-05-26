---------------------------- MODULE orchestrator ----------------------------
EXTENDS TLC, Naturals, Integers, Sequences

CONSTANT Workers, Manager, Clients

Messages == [type: {"task"}, s: Manager, r: Workers, client: Clients] \union 
            [type: {"completed"}, s: Workers, r: Manager, client: Clients] \cup 
            [type: {"finished"}, s: Manager, r: Clients] \cup
            [type: {"doWork"}, s: Clients, r: Manager]
            

Actors == Workers \union Manager \union Clients

(*--algorithm orchestrator

variables wState = [w \in Workers |-> "waiting"],
            mState = [m \in Manager |-> "ready"],
            cState = [c \in Clients |-> "idle"],
            queues = [q \in Actors |-> <<>>];
            
macro send(id, msg) begin
    queues[id] := Append(queues[id], msg);
end macro;

macro receive(msg) begin
    await Len(queues[self]) > 0;
    msg := Head(queues[self]);
    queues[self] := Tail(queues[self]);
end macro;

process worker \in Workers
variable current_msg = <<>>;
begin
    WorkerLoop:
        while TRUE do
            WaitForWork:
                receive(current_msg);
            ProcessTask:
                if current_msg.type = "task" then
                    wState[self] := "working";
            PerformWork:
                    \* simulate work
                    wState[self] := "waiting";
                    with m = current_msg.s do
                        send(m, [type |-> "completed", s |-> self, r |-> m, client |-> current_msg.client]);
                    end with;
                end if;
        end while;
end process;

process client \in Clients
variable current_msg = <<>>;
begin
    SendTaskToManager:
        with m \in Manager do
            send(m, [type |-> "doWork", s |-> self, r |-> m]);
        end with;
    ReceiveTaskFinish:
        receive(current_msg);
    ProcessFinish:
        if current_msg.type = "finished" then
            cState[self] := "idle";
        else 
            goto ReceiveTaskFinish;
        end if;
end process;

process manager \in Manager
variable current_msg = <<>>;
begin
    ManagerLoop:
        while TRUE do
            ReceiveManagerTask:
                receive(current_msg);
            ProcessManagerTask:
                if current_msg.type = "doWork" then
                    with w \in Workers do
                        send(w, [type |-> "task", s |-> self, r |-> w, client |-> current_msg.s]);
                    end with;
                elsif current_msg.type = "completed" then
                    send(current_msg.client, [type |-> "finished", s |-> self, r |-> current_msg.client]);
                end if;
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
\* Process variable current_msg of process worker at line 32 col 10 changed to current_msg_
\* Process variable current_msg of process client at line 52 col 10 changed to current_msg_c
VARIABLES wState, mState, cState, queues, pc, current_msg_, current_msg_c, 
          current_msg

vars == << wState, mState, cState, queues, pc, current_msg_, current_msg_c, 
           current_msg >>

ProcSet == (Workers) \cup (Clients) \cup (Manager)

Init == (* Global variables *)
        /\ wState = [w \in Workers |-> "waiting"]
        /\ mState = [m \in Manager |-> "ready"]
        /\ cState = [c \in Clients |-> "idle"]
        /\ queues = [q \in Actors |-> <<>>]
        (* Process worker *)
        /\ current_msg_ = [self \in Workers |-> <<>>]
        (* Process client *)
        /\ current_msg_c = [self \in Clients |-> <<>>]
        (* Process manager *)
        /\ current_msg = [self \in Manager |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in Workers -> "WorkerLoop"
                                        [] self \in Clients -> "SendTaskToManager"
                                        [] self \in Manager -> "ManagerLoop"]

WorkerLoop(self) == /\ pc[self] = "WorkerLoop"
                    /\ pc' = [pc EXCEPT ![self] = "WaitForWork"]
                    /\ UNCHANGED << wState, mState, cState, queues, 
                                    current_msg_, current_msg_c, current_msg >>

WaitForWork(self) == /\ pc[self] = "WaitForWork"
                     /\ Len(queues[self]) > 0
                     /\ current_msg_' = [current_msg_ EXCEPT ![self] = Head(queues[self])]
                     /\ queues' = [queues EXCEPT ![self] = Tail(queues[self])]
                     /\ pc' = [pc EXCEPT ![self] = "ProcessTask"]
                     /\ UNCHANGED << wState, mState, cState, current_msg_c, 
                                     current_msg >>

ProcessTask(self) == /\ pc[self] = "ProcessTask"
                     /\ IF current_msg_[self].type = "task"
                           THEN /\ wState' = [wState EXCEPT ![self] = "working"]
                                /\ pc' = [pc EXCEPT ![self] = "PerformWork"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "WorkerLoop"]
                                /\ UNCHANGED wState
                     /\ UNCHANGED << mState, cState, queues, current_msg_, 
                                     current_msg_c, current_msg >>

PerformWork(self) == /\ pc[self] = "PerformWork"
                     /\ wState' = [wState EXCEPT ![self] = "waiting"]
                     /\ LET m == current_msg_[self].s IN
                          queues' = [queues EXCEPT ![m] = Append(queues[m], ([type |-> "completed", s |-> self, r |-> m, client |-> current_msg_[self].client]))]
                     /\ pc' = [pc EXCEPT ![self] = "WorkerLoop"]
                     /\ UNCHANGED << mState, cState, current_msg_, 
                                     current_msg_c, current_msg >>

worker(self) == WorkerLoop(self) \/ WaitForWork(self) \/ ProcessTask(self)
                   \/ PerformWork(self)

SendTaskToManager(self) == /\ pc[self] = "SendTaskToManager"
                           /\ \E m \in Manager:
                                queues' = [queues EXCEPT ![m] = Append(queues[m], ([type |-> "doWork", s |-> self, r |-> m]))]
                           /\ pc' = [pc EXCEPT ![self] = "ReceiveTaskFinish"]
                           /\ UNCHANGED << wState, mState, cState, 
                                           current_msg_, current_msg_c, 
                                           current_msg >>

ReceiveTaskFinish(self) == /\ pc[self] = "ReceiveTaskFinish"
                           /\ Len(queues[self]) > 0
                           /\ current_msg_c' = [current_msg_c EXCEPT ![self] = Head(queues[self])]
                           /\ queues' = [queues EXCEPT ![self] = Tail(queues[self])]
                           /\ pc' = [pc EXCEPT ![self] = "ProcessFinish"]
                           /\ UNCHANGED << wState, mState, cState, 
                                           current_msg_, current_msg >>

ProcessFinish(self) == /\ pc[self] = "ProcessFinish"
                       /\ IF current_msg_c[self].type = "finished"
                             THEN /\ cState' = [cState EXCEPT ![self] = "idle"]
                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "ReceiveTaskFinish"]
                                  /\ UNCHANGED cState
                       /\ UNCHANGED << wState, mState, queues, current_msg_, 
                                       current_msg_c, current_msg >>

client(self) == SendTaskToManager(self) \/ ReceiveTaskFinish(self)
                   \/ ProcessFinish(self)

ManagerLoop(self) == /\ pc[self] = "ManagerLoop"
                     /\ pc' = [pc EXCEPT ![self] = "ReceiveManagerTask"]
                     /\ UNCHANGED << wState, mState, cState, queues, 
                                     current_msg_, current_msg_c, current_msg >>

ReceiveManagerTask(self) == /\ pc[self] = "ReceiveManagerTask"
                            /\ Len(queues[self]) > 0
                            /\ current_msg' = [current_msg EXCEPT ![self] = Head(queues[self])]
                            /\ queues' = [queues EXCEPT ![self] = Tail(queues[self])]
                            /\ pc' = [pc EXCEPT ![self] = "ProcessManagerTask"]
                            /\ UNCHANGED << wState, mState, cState, 
                                            current_msg_, current_msg_c >>

ProcessManagerTask(self) == /\ pc[self] = "ProcessManagerTask"
                            /\ IF current_msg[self].type = "doWork"
                                  THEN /\ \E w \in Workers:
                                            queues' = [queues EXCEPT ![w] = Append(queues[w], ([type |-> "task", s |-> self, r |-> w, client |-> current_msg[self].s]))]
                                  ELSE /\ IF current_msg[self].type = "completed"
                                             THEN /\ queues' = [queues EXCEPT ![(current_msg[self].client)] = Append(queues[(current_msg[self].client)], ([type |-> "finished", s |-> self, r |-> current_msg[self].client]))]
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED queues
                            /\ pc' = [pc EXCEPT ![self] = "ManagerLoop"]
                            /\ UNCHANGED << wState, mState, cState, 
                                            current_msg_, current_msg_c, 
                                            current_msg >>

manager(self) == ManagerLoop(self) \/ ReceiveManagerTask(self)
                    \/ ProcessManagerTask(self)

Next == (\E self \in Workers: worker(self))
           \/ (\E self \in Clients: client(self))
           \/ (\E self \in Manager: manager(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


TypeOK == 
        /\ wState \in [Workers -> {"waiting", "working"}]
        /\ mState \in [Manager -> {"ready", "busy", "jobComplete"}]
        /\ cState \in [Clients -> {"assignTask", "idle"}]
        


=============================================================================
\* Modification History
\* Last modified Mon Mar 11 10:40:22 CET 2024 by lee
\* Created Fri Mar 08 22:22:11 CET 2024 by lee
