--------------- MODULE Peterson --------------

(* var
     level : array [0..N-1] of -1..N-2 = [N of -1];
     last  : array [0..N-2] of  0..N-1;

   procedure process(i : integer);
     var l : integer = 0;
   begin
     while true do
     begin
       >>> idle // AINDA NÃO PODE ENTRAR <<<
0:     while l < N-1 do
       begin
         level[i] := l;
         last[l]  := i;
1:       repeat until (last[l] != i or ∀ k != i . level[k] < l));
         l := l+1
       end
       >>> critical // JÁ PODE ENTRAR <<<
2:     level[i] := -1;
       l := 0
     end
   end;

   process(0) || ... || process(N-1)
*)

EXTENDS Integers, TLC

CONSTANTS N

ASSUME N > 1

VARIABLES level, last, l, pc

TypeOK == [] (l \in [0..N-1 -> 0..N] /\ level \in [0..N-1 -> -1..N-2] /\ last \in [0..N-2 -> 0..N-1] /\ pc \in [0..N-1 -> 0..2])

Init == 
    /\ l = [i \in 0..N-1 |-> 0]
    /\ last = [i \in 0..N-2 |-> 0]
    /\ level = [i \in 0..N-1 |-> -1]
    /\ pc = [i \in 0..N-1 |-> 0]

whileTrue(i) ==
    /\ pc[i] = 0   
    /\ l[i] < N-1
    /\ level' = [level EXCEPT ![i] = l[i]]
    /\ last' = [last EXCEPT ![l[i]] = i]
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ UNCHANGED <<l>>

whileFalse(i) ==
    /\ pc[i] = 0
    /\ l[i] >= N-1
    /\ pc' = [pc EXCEPT ![i] = 2]
    /\ UNCHANGED <<l,level,last>>

repeatUntilTrue(i) ==
    /\ pc[i] = 1
    /\ last[l[i]] = i
    /\ \E k \in 0..N-1 : k # i /\ level[k] >= l[i]
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ UNCHANGED <<l,level,last>>

execute(i) ==
    /\ pc[i] = 1
    (* A -> B é uma função em que todos os elementos de A retornam B  *)
    /\ (last[l[i]] # i \/ \A k \in 0..N-1 : k # i => level[k] < l[i])
    /\ l' = [l EXCEPT ![i] = @ + 1]
    /\ pc' = [pc EXCEPT ![i] = 2]
    /\ UNCHANGED <<level,last>>

Counter0 == \E i \in 0..N-1 :
    (whileTrue(i) \/ whileFalse(i))
    (*/\ Print("level'", TRUE) /\ Print(level', TRUE)*)

Counter1 == \E i \in 0..N-1 :
    (repeatUntilTrue(i) \/ execute(i))
    (*/\ Print("level'", TRUE) /\ Print(level', TRUE)*)

Counter2 == \E i \in 0..N-1 : 
    pc[i] = 2
    /\ level' = [level EXCEPT ![i] = -1]
    /\ l' = [l EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = 0]
    /\ UNCHANGED <<last>>

Next == Counter0 \/ Counter1 \/ Counter2

vars == <<last,level,l,pc>>

Algorithm == Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion == [](\A i,j \in 0..N-1 : (pc[i] = 2 /\ pc[j] = 2) => (i = j))

StarvationFree == [](\A i \in 0..N-1 : (pc[i] = 2  => <>(pc[i] = 0)))

Fairness == WF_vars(Next)

===============================================