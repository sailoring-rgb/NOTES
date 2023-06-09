------------------- MODULE easy ----------------------

EXTENDS Integers

CONSTANTS N

VARIABLES r, pc

TypeOK == [] (r \in Int /\ N \in Int /\ pc \in 0..2)

Init == r = N /\ pc = 0

CondTRUE ==
    /\ pc = 0 /\ r < 0 /\ pc' = 1 /\ UNCHANGED <<r>>

CondTRUERes ==
    /\ pc = 1 /\ pc' = 2 /\ r' = -r

CondFALSE ==
    /\ pc = 0 /\ r >= 0 /\ pc' = 2 /\ UNCHANGED <<r>>

Next == CondTRUE \/ CondTRUERes \/ CondFALSE

vars == <<r,pc>>

Algorithm == Init /\ [][Next]_vars 

Termination == <>(pc = 2)

SpecFairness == WF_vars(Next)

Result == <>(r # 5)

======================================================