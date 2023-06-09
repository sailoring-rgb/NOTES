------------------------- MODULE LeaderElectionRing -------------------------

EXTENDS Naturals, TLC

CONSTANTS N, succ

Node == 1..N

(* 
    >>> se for igual a 1, então o primeiro nodo é alcançado a partir do último nodo
    (i.e., o primeiro nodo é o sucessor do último nodo).

    >>> se for diferente de 1, então existe, pelo menos, um nodo através do qual o nodo em questão pode ser alcançado
    (i.e., o nodo é o sucessor de outro nodo).

    >>> por outra palavras,todos os nodos são alcançáveis.
*)

reachable(n) ==
  LET aux[i \in Nat] == 
    IF i = 1 THEN { succ[n] }
    ELSE aux[i-1] \cup { x \in Node : \E y \in aux[i-1] : x = succ[y] }
  IN aux[N]

ASSUME 
    /\ N > 0
    /\ succ \in [Node -> Node]
    /\ \A x \in Node : Node \subseteq reachable(x)
    
VARIABLES outbox, inbox, elected

TypeOK == [] (outbox \in [Node -> SUBSET Node] /\ inbox \in [Node -> SUBSET Node] /\ elected \in [Node -> BOOLEAN])

Init ==
    /\ outbox  = [id \in Node |-> {id}]
    /\ inbox   = [id \in Node |-> {}]
    /\ elected = [id \in Node |-> FALSE]
    
transmit == \E id \in Node : \E m \in outbox[id] :
    outbox' = [outbox EXCEPT ![id] = @ \ {m}]
    /\ inbox'  = [inbox  EXCEPT ![succ[id]] = @ \cup {m}] (* cup significa união *)
    /\ UNCHANGED elected

(* verificar que o anel está ordenado decrescentemente (primeiro exercício) *)
(* isto quer dizer que o sucessor de 5 é 4, o sucessor de 4 é 3, por aí em diante *)
sorted == 1 :> 5 @@ 5 :> 4 @@ 4 :> 3 @@ 3 :> 2 @@ 2 :> 1
    
node(id) == \E m \in inbox[id] :
    /\ inbox'   = [inbox EXCEPT ![id] = @ \ {m}]
    /\ outbox'  = IF m >= id 
                  THEN [outbox EXCEPT ![id] = @ \cup {m}]
                  ELSE outbox
    /\ elected' = IF m = id
                  THEN [elected EXCEPT ![id] = TRUE]
                  ELSE elected

Next == transmit \/ \E id \in Node : node(id)

vars == <<outbox, inbox, elected>>

Spec == Init /\ [][Next]_vars

AtMostOneLeader == [] (\A x,y \in Node : elected[x] /\ elected[y] => x = y)

LeaderStaysLeader == [](\A x \in Node : elected[x] => [] (elected[x]))

AtLeastOneLeader == WF_vars(Next) => <> (\E x \in Node : elected[x]) 

NoLeader == \A x \in Node : [] (~elected[x])

=============================================================================