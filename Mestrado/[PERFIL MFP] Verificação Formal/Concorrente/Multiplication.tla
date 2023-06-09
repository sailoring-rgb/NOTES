--------------------------- MODULE Multiplication ---------------------------

EXTENDS Integers

CONSTANTS a,b

ASSUME a >= 0

VARIABLES r,n,pc

TypeOK == [] (r \in Int /\ n \in Int /\ pc \in 0..1)

Init == r = 0 /\ n = 0 /\ pc = 0

WhileT == 
    /\ pc = 0 /\ n < a 
    /\ n' = n + 1 
    /\ r' = r + b 
    /\ pc' = 0

WhileF == 
    /\ pc = 0 /\ n >= a 
    /\ pc' = 1 
    /\ UNCHANGED <<r,n>>

Next == WhileT \/ WhileF

vars == <<r,n,pc>>

Algorithm == Init /\ [][Next]_vars

PartialCorrectness == [] (pc = 1 => r = a * b)

Termination == <> (pc = 1)

=============================================================================