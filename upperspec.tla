----------------------------- MODULE upperspec -----------------------------
EXTENDS Naturals
CONSTANTS MaxObj
VARIABLES State, Pending, Output

ObjIDs == {0..MaxObj}
Values == {0, 1, 2}

PendingInit == Pending = {}
StateInit == State = [x \in ObjIDs |-> 0]
OutputInit == Output = 0

PendingInv == Pending \subseteq ([type : {"query"}, objid : ObjIDs] \cup [type : {"update"}, objid : ObjIDs, newval : Values])
StateInv == State \in [ObjIDs -> Values]
OutputInv == Output \in Values

Query(id) == /\ id \in ObjIDs  
             /\ Pending' = Pending \cup {[type |-> "query", objid |-> id]}
             /\ State' = State
             /\ Output' = Output
             
Update(id, newVal) == /\ id \in ObjIDs
                      /\ newVal \in Values
                      /\ Pending' = Pending \cup {[type |-> "update", objid |-> id, newval |-> newVal]}
                      /\ State' = State
                      /\ Output' = Output
                      
Ignore == /\ IF \E y \in Pending : TRUE 
             THEN Pending' = Pending \ {CHOOSE x \in Pending : TRUE}
             ELSE Pending' = Pending
          /\ State' = State
          /\ Output' = Output

Process == IF \E y \in Pending : TRUE 
           THEN LET r == CHOOSE x \in Pending : TRUE IN
             /\ Pending' = Pending \ {r}
             /\ CASE r["type"] = "query" -> 
                  /\ Output' = State[r["objid"]]
                  /\ State' = State
                [] r["type"] = "update" ->
                  /\ Output' = 0
                  /\ State' = [State EXCEPT ![r["objid"]] = r["newval"]]
                [] OTHER ->
                  /\ Output' = Output
                  /\ State' = State
           ELSE /\ Pending' = Pending
                /\ Output' = Output
                /\ State' = State
                 
TypeInv == PendingInv /\ StateInv /\ OutputInv
Init == PendingInit /\ StateInit /\ OutputInit
Next == (\E id \in ObjIDs : Query(id)) \/ (\E id \in ObjIDs, val \in Values : Update(id, val)) \/ Ignore \/ Process
Spec == Init /\ [][Next]_<<State, Pending, Output>>

THEOREM TypeInvHolds == Spec => []TypeInv
=============================================================================
