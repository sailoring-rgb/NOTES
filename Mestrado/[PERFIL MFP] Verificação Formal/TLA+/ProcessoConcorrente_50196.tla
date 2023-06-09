-------------- MODULE ProcessoConcorrente_50196 ----------

EXTENDS Integers, TLC

CONSTANT N

ASSUME N > 0

VARIABLES n, lock, waiting, pc

TypeOK == n \in 0..N /\ lock \in BOOLEAN /\ waiting \in [1..N -> BOOLEAN] /\ pc \in [1..N -> 0..3]

Init == n = 0 /\ lock = TRUE /\ waiting = [i \in 1..N |-> FALSE] /\ pc = [i \in 1..N |-> 0]

Counter0(i) ==
    /\ pc[i] = 0
    /\ IF lock = TRUE
       THEN lock' = FALSE
            /\ n' = n + 1
            /\ pc' = [pc EXCEPT ![i] = 1]
       ELSE pc' = [pc EXCEPT ![i] = 0]
            /\ UNCHANGED <<lock,n>>
    /\ UNCHANGED <<waiting>>

Counter1(i) ==
    /\ pc[i] = 1
    /\ IF n < N
       THEN waiting' = [waiting EXCEPT ![i] = TRUE]
            /\ lock' = TRUE
            /\ pc' = [pc EXCEPT ![i] = 2]
        ELSE waiting' = [j \in 1..N |-> FALSE]
             /\ lock' = TRUE
             /\ pc' = [pc EXCEPT ![i] = 3]
    /\ UNCHANGED <<n>>

Counter2(i) ==
    /\ pc[i] = 2
    /\ IF lock = TRUE /\ waiting[i] = FALSE
       THEN lock' = FALSE
            /\ pc' = [pc EXCEPT ![i] = 1]
        ELSE lock' = lock
            /\ pc' = [pc EXCEPT ![i] = 2]
    /\ UNCHANGED <<waiting, n>>

Next == \E i \in 1..N: Counter0(i) \/ Counter1(i) \/ Counter2(i)

vars == <<pc, lock, n, waiting>>

Algorithm == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Propriedade de Safety -- Propridade 1 *)
SharedOK == n \in 0..N /\ lock \in BOOLEAN

(* Propriedade de Safety -- Propriedade 2 *)
NotEveryoneWaiting == [] (\E i \in 1..N : ~(pc[i] = 2))

(* Propriedade de Liveness -- Propriedade 3 *)
EveryoneTerminate == WF_vars(Next) => <> (\A i \in 1..N : pc[i] = 3)

(* Propriedade de Safety -- Propriedade 4 *)
FinishAfterEveryoneStarted == [] ((\E i \in 1..N : pc[i] = 3) => (\A j \in 1..N : pc[j] > 0))

(* ???????????????? EXERCÍCIO 3 ???????????????? *)

============================================