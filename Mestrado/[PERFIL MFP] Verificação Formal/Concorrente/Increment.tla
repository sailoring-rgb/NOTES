--------------- MODULE Increment --------------

(* var x : integer = 0;

   procedure increment(i : integer);
        var y : integer = 0;
   begin
0:   y := x; 
1:   x := y + 1 
2: end;

   increment(1) || ... || increment(N)
*)

EXTENDS Integers

CONSTANTS N

ASSUME N > 0

VARIABLES x, y, pc

TypeOK == [] (r \in Int /\ n \in Int /\ pc \in [0..N-1 -> 0..1])

(***  No Init, não é correto ter \A i \in 1..N : y[i] = 0  ***)
Init == x = 0 /\ y = [i \in 0..N-1 |-> 0] /\ pc = [i \in 0..N-1 |-> 0]

(***  0:  y = x  ***)
(*  Existe um processo que executará a instrução 0 e, nesse caso, no próximo estado, o y deste processo será igual a x e o program counter passa a 1 (prox instrução)  *)
(***  y EXCEPT ![i] é o mesmo que dizer o y excepto aqueles diferentes de i, ou seja, o y deste processo  ***)
Counter0 == \E i \in 0..N-1 :
    pc[i] = 0
    /\ y' = [y EXCEPT ![i] = x]
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ UNCHANGED <<x>>

(***  1:  x = y + 1  ***)
(*  Existe um processo que executará a instrução 1 e, nesse caso, no próximo estado, o x será igual ao y deste processo e o program counter passa a 2 (prox instrução)  *)
Counter1 == \E i \in 0..N-1 :
    pc[i] = 1
    /\ x' = y[i] + 1
    /\ pc' = [pc EXCEPT ![i] = 2]
    /\ UNCHANGED <<y>>

Next == Counter0 \/ Counter1

vars == <<x,y,pc>>

Algorithm == Init /\ [][Next]_vars
 
Termination == <>(\A i \in 0..N-1 : pc[i] = 2) 

===============================================