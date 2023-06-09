---------------- MODULE ProcessoDistribuido_50196 --------------

EXTENDS Integers, TLC, Sequences

VARIABLE inbox, pc, result, try

TypeOK ==
    /\ inbox \in [0..1 -> Seq(1..2)]
    /\ pc \in [0..1 -> 0]
    /\ result \in [0..1 -> 0..2]
    /\ try \in [0..1 -> 1..2]

random(x) == (3-x)

Init ==
    /\ try = [id \in 0..1 |-> 1]
    /\ inbox = [id \in 0..1 |-> <<1>>]
    /\ pc = [id \in 0..1 |-> 0]
    /\ result = [id \in 0..1 |-> 0]

InternalCond(i) == IF try[i] = inbox[i][Len(inbox[i])]
                   THEN try' = [try EXCEPT ![i] = random(@)]
                    /\ inbox' = [inbox EXCEPT ![1-i] = Append(inbox[1-i],random(try[i]))]
                    /\ UNCHANGED <<result>>
                    ELSE result' = [result EXCEPT ![i] = try[i]]
                    /\ UNCHANGED <<try, inbox>>

Start(i) ==
    /\ pc[i] = 0
    /\ IF result[i] = 0 /\ Len(inbox[i]) # 0
       THEN InternalCond(i)
       ELSE UNCHANGED <<inbox,result,try>>
    /\ pc' = [pc EXCEPT ![i] = 0]

Next == \E i \in 0..1 : Start(i)

vars == <<result, pc, inbox, try>>

Algorithm == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Sempre que um dos processos tiver um result diferente de 0 o outro processo terá necessariamente um valor diferente. *)
Propriedade1 == [] (result[0] # 0 => result[1] # result[0])

(* Os canais de comunicação nunca têm mais do que 2 mensagens. *)
Propriedade2 == [] (\A id \in 0..1 : Len(inbox[id]) <= 2)

(* Mal um processo tenha um result diferente de 0 o outro irá inevitavelmente ter um valor de result diferente de 0. *)
Propriedade3 == WF_vars(Next) => [](result[0] # 0 => <> (result[1] # 0))

==========================================================