---- MODULE worker ----
EXTENDS TLC, Sequences, Naturals

VARIABLES ws \* worker state
VARIABLES d \* data state
VARIABLES r \* result state

TypeInvarient ==
    /\ ws \in {"working", "idle", "replicate", "writing"}
    /\ d \in 1..10
    /\ r \in 1..10

Init == 
    /\ ws = "idle"
    /\ d = {}


====