---------------- MODULE process ------------

EXTENDS Integers

VARIABLES sem, pc

TypeOK == [](sem \in BOOLEAN /\ pc \in [0..1 -> 0..2])

Init == sem = TRUE /\ pc = [i \in 0..1 |-> 0]

Counter0 == \E i \in 0..1 :
    pc[i] = 0
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ UNCHANGED <<sem>>
    
Counter1_TRUE == \E i \in 0..1 :
    pc[i] = 1
    /\ sem = TRUE
    /\ sem' = FALSE
    /\ pc' = [pc EXCEPT ![i] = 2]

Counter1_FALSE == \E i \in 0..1 :
    pc[i] = 1
    /\ sem = FALSE
    /\ UNCHANGED <<sem,pc>>

Counter2 == \E i \in 0..1 :
    pc[i] = 2
    /\ sem' = TRUE
    /\ UNCHANGED <<pc>>

Next == Counter0 \/ Counter1_TRUE \/ Counter1_FALSE \/ Counter2

vars == <<sem,pc>>

Algorithm == Init /\ [][Next]_vars

============================================