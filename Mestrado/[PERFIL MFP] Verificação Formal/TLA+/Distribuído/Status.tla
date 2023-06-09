------------------------- MODULE Status -------------------------

(* type status = (Working,Prepared,Aborted,Committed);

   type message = record
     from: 0..N;
     type: status;
   end;

   var inbox : array [0..N] of channel;

   procedure worker(id : integer);
     var state : status = Working;
         msg : message; 
   begin
0:   while true do
     begin
       >>> Finish task <<<
       if state = Working then
       begin 
         state := Prepared; 
         msg.from = id;
         msg.type = Prepared;
         send(msg,inbox[0])
       end
       or else
       >>> Abort task <<<
       if state = Working then 
       begin
         state := Aborted
       end
       or else
       >>> Receive message <<<
       if not empty(inbox[id]) then
       begin
         msg := receive(inbox[id]); 
         if msg.type = Aborted or msg.type = Committed then state := msg.type;
       end
     end
   end;

   procedure broadcast(msg : message);
     var id : integer = 1;
   begin
     while id <= N do
     begin
       send(msg,inbox[id]);
       id := id + 1
     end
   end;

   procedure master;
     var state : status = Working;
         prepared : array 1..N of boolean = [N of false];
         msg : message;
     procedure 
   begin
0:   while true do
     begin
       >>> Abort transaction <<<
       if state = Working then
       begin 
         state := Aborted; 
         msg.from = 0;
         msg.type = Aborted;
         broadcast(msg)
       end
       or else
       >>> Receive message <<<
       if not empty(inbox[0]) then
       begin
         msg := receive(inbox[0]);
         prepared[msg.from] := true; 
         if state = Working and prepared = [N of true] then 
         begin 
           msg.from = 0;
           msg.type = Committed;
           state := Committed; 
           broadcast(msg) 
         end
       end
     end
   end;

   master || worker(1) || ... || worker(N)
*)
EXTENDS Naturals, TLC, Sequences

CONSTANTS N

VARIABLES inbox, worker_status, master_status, prepared

Status == {"Working","Prepared","Aborted","Committed"}

TypeOK == [] (inbox \in [0..N -> Seq([from : 0..N,type : Status ])]
            /\ worker_status \in [1..N -> Status]
            /\ master_status \in Status
            /\ prepared \in [1..N -> BOOLEAN])

Init == /\ inbox = [id \in 0..N |-> <<>>]
        /\ worker_status = [id \in 1..N |-> "Working"]
        /\ master_status = "Working"
        /\ prepared = [id \in 1..N |-> FALSE]

Worker_Finish(id) ==
    /\ worker_status[id] = "Working"
    /\ worker_status' = [worker_status EXCEPT ![id] = "Prepared"]
    /\ inbox' = [inbox EXCEPT ![0] = Append(@,[from |-> id, type |-> "Prepared"])]
    /\ prepared' = prepared
    /\ master_status' = master_status

Worker_Abort(id) == 
    /\ worker_status[id] = "Working"
    /\ worker_status' = [worker_status EXCEPT ![id] = "Aborted"]
    /\ inbox' = inbox
    /\ prepared' = prepared
    /\ master_status' = master_status

Worker_Recieve(id) ==
    /\ Len(inbox[id]) # 0
    /\ (Head(inbox[id]).type = "Aborted" \/ Head(inbox[id]).type = "Prepared")
    /\ worker_status' = [worker_status EXCEPT ![id] = Head(inbox[id]).type]
    /\ inbox' = [inbox EXCEPT ![id] = Tail(inbox[id])]
    /\ prepared' = prepared
    /\ master_status' = master_status

Broadcast(m) == inbox' = [id \in 0..N |-> IF id = 0 THEN inbox[0] ELSE Append(inbox[id],m)]
    
Master_Abort_Transction == 
    /\ master_status = "Working"
    /\ master_status' = "Aborted"
    /\ Broadcast([from |-> 0, type |-> "Aborted"])
    /\ prepared' = prepared
    /\ worker_status' = worker_status

Master_Recieve_Message ==
    /\ Len(inbox[0]) # 0
    /\ prepared' = [prepared EXCEPT ![Head(inbox[0]).from] = TRUE]
    /\ (IF /\ prepared' = [id \in 1..N |-> TRUE]
          /\ master_status = "Working"
          THEN master_status' = "Committed"
            /\ Broadcast([from |-> 0, type |-> "Committed"])
          ELSE master_status' = master_status)
    /\ inbox' = [inbox EXCEPT ![0] = Tail(inbox[0])]
    /\ worker_status' = worker_status


Next ==(\E id \in 1..N : Worker_Recieve(id) \/ Worker_Finish(id) \/ Worker_Abort(id)) \/
        Master_Abort_Transction \/ Master_Recieve_Message

vars == <<inbox, worker_status, master_status, prepared>>

Spec == Init /\ [][Next]_vars

=============================================================================