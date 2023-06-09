---------------------- MODULE philosopher ----------------------

(* var
     waiter : boolean = true;
     fork   : array [0..N-1] of boolean = [N of true];
   
   function left(i : integer) : integer;
   begin
     left := i;
   end;

   function right(i : integer) : integer;
   begin
     right := mod (i-1) N;
   end;

   procedure phil(i : integer);
   begin
     while true do
     begin
0:     >>> think <<<
       repeat until waiter;
       waiter := false;
1:     repeat until fork[left(i)];
       fork[left(i)] := false;
2:     repeat until fork[right(i)];
       fork[right(i)] := false;
       waiter := true;
3:     >>> eat <<<
       fork[left(i)] := true;
       fork[right(i)] := true;       
     end
   end;

   phil(0) || ... || phil(N-1) 
*)

EXTENDS Integers

CONSTANT N
ASSUME N > 0

VARIABLES waiter, fork, pc

TypeOK == [](waiter \in BOOLEAN /\ fork \in [0..N-1 -> BOOLEAN] /\ pc \in [0..N-1 -> 0..3])

left(i) == i

right(i) == (i-1) % N 

eat(i) == fork' = [fork EXCEPT ![left(i)] = TRUE, ![right(i)] = TRUE]

counter0(i) == 
        /\ pc[i] = 0
        /\ waiter = TRUE
        /\ waiter' = FALSE
        /\ pc' = [pc EXCEPT ![i] = 1]
        /\ fork' = fork

counter1(i) == 
        /\ pc[i] = 1
        /\ fork[left(i)] = TRUE
        /\ pc' = [pc EXCEPT ![i] = 2]
        /\ fork' = [fork EXCEPT ![left(i)] = FALSE]
        /\ waiter' = waiter

counter2(i) ==
        /\ pc[i] = 2
        /\ fork[right(i)] = TRUE
        /\ pc' = [pc EXCEPT ![i] = 3]
        /\ fork' = [fork EXCEPT ![right(i)] = FALSE]
        /\ waiter' = TRUE

counter3(i) == 
        /\ pc[i] = 3
        /\ fork' = [fork EXCEPT ![right(i)] = TRUE, ![left(i)] = TRUE]
        /\ waiter' = waiter
        /\ pc' = [pc EXCEPT ![i] = 0]

phil(i) == counter0(i) \/ counter1(i) \/ counter2(i) \/ counter3(i)

Init == pc = [i \in 0..N-1 |-> 0] /\ fork = [i \in 0..N-1 |-> TRUE] /\ waiter = TRUE

Next == \E i \in 0..N-1: phil(i)

vars == <<waiter,fork,pc>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====================================================================