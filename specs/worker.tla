---- MODULE worker ----
EXTENDS TLC, Sequences, Naturals
CONSTANT Workers

\* |r=<<>>             |Calc    |r=<<>>    |
\* |ws=idle            |-->     |ws=    |
\* |d=<<1,2,3,4,5>>    |        |    |

VARIABLES ws \* worker state
VARIABLES d \* data state
VARIABLES r \* result state
VARIABLES kvstore \* storage for the worker

vars == << ws, r, d, kvstore >>

TypeInvarient ==
    /\ ws = [Workers -> {"working", "idle", "replicate", "writing"}] 
    /\ d \in <<1,2,3,4,5>>
    /\ r \subseteq r

Init == 
    /\ ws = [wk \in Workers |-> "idle"]
    /\ d \in 1..5
    /\ r \in 1..5
    /\ kvstore \in 1..5

Calc(w) ==
    /\ ws = "idle"
    /\ ws' = [ws EXCEPT ![w] = "working"]
    /\ IF d # <<>> THEN r = Head(d) /\ d = Tail(d)
                   ELSE FALSE
    /\ UNCHANGED kvstore

Xor(w) ==
    /\ ws = "working"
    /\ ws' = [ws EXCEPT ![w]= "replicate"]
    /\ IF r # <<>> THEN r = Tail(r)
                    ELSE FALSE
    /\ UNCHANGED <<kvstore,d>>

Write(w) == 
    /\ ws = "replicate"
    /\ ws' = [ws EXCEPT ![w] = "writing"]
    /\ IF r # <<>> THEN kvstore = Head(r)
                    ELSE FALSE
    /\ UNCHANGED <<r, d>>

Idle(w) ==
    /\ ws = "writing"
    /\ ws' = [ws EXCEPT ![w]="idle"]
    /\ UNCHANGED <<d,r,kvstore>>


Next == \E w \in Workers: 
                \/ Calc(w)
                \/ Xor(w)
                \/ Write(w) 

Spec == Init /\ [][Next]_vars


====