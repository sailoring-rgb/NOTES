------------------------------ MODULE Dijkstra ------------------------------

(* var state : array [0..N] of 0..K-1;

   function hasToken(i : integer) : boolean;
   begin
     hasToken := (i = 0 and state[i] = state[N]) or (i != 0 and state[i] != state[i-1])
   end;

   procedure bottom;
   begin
0:   while true do
     begin
       repeat until hasToken(0);
       state[0] := mod (state[0] + 1) K
     end
   end;

   procedure other(i : integer);
   begin
0:   while true do
     begin
       repeat until hasToken(i);
       state[i] := state[i-1]
     end
   end;

   bottom || other(1) || ... || other(N)
*)

EXTENDS Naturals

CONSTANTS N, K

ASSUME N > 0 /\ K >= N

VARIABLE state

TypeOK == [] (state \in [0..N -> 0..K-1])

hasToken(i) == (i = 0 /\ state[i] = state[N]) \/ (i # 0 /\ state[i] # state[i-1])

bottom == hasToken(0) /\ state' = [state EXCEPT ![0] = (@+1) % K]

other(i) == hasToken(i) /\ state' = [state EXCEPT ![i] = state[i-1]]
           
Next == bottom \/ \E i \in 1..N : other(i)

Init == state \in [0..N -> 0..K-1]

(* para garantir que enquanto houver pelo menos um nó que consiga progredir (enquanto houver pelo menos um nó que tenha o token),
então algum deles terá que executar *)
Spec == Init /\ [][Next]_state /\ WF_state(Next)

Valid == \E i \in 0..N : hasToken(i) /\ \A j \in 0..N : hasToken(j) => j = i
           
Closure == [] (Valid => [] Valid)

Convergence == WF_state(Next) => <> Valid

=============================================================================