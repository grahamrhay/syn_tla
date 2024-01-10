---- MODULE syn ----
EXTENDS FiniteSets, Integers, Sequences

CONSTANTS Nodes, MaxValues

VARIABLES inbox, registered, locally_registered, next_val

vars == <<inbox, registered, locally_registered, next_val>>

Init ==
    /\ inbox = [n \in Nodes |-> <<>>]
    /\ registered = {}
    /\ locally_registered = [n \in Nodes |-> {}]
    /\ next_val = 0

Register(n) ==
    /\ next_val < MaxValues
    /\ registered' = registered \union {next_val}
    /\ locally_registered' = [locally_registered EXCEPT![n] = locally_registered[n] \union {next_val}]
    /\ next_val' = next_val + 1
    /\ inbox' = [o \in Nodes |-> IF o = n THEN inbox[o] ELSE Append(inbox[o], [action |-> "sync_register", name |-> next_val])]

SyncRegister(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "sync_register"
    /\ locally_registered' = [locally_registered EXCEPT![n] = locally_registered[n] \union {Head(inbox[n]).name}]
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ UNCHANGED <<registered, next_val>>

ItemToRemove(n) ==
    CHOOSE r \in locally_registered[n]: TRUE

Unregister(n) ==
    /\ Cardinality(locally_registered[n]) > 0
    /\ LET item_to_remove == ItemToRemove(n)
        IN registered' = registered \ {item_to_remove}
        /\ locally_registered' = [locally_registered EXCEPT![n] = locally_registered[n] \ {item_to_remove}]
        /\ inbox' = [o \in Nodes |-> IF o = n THEN inbox[o] ELSE Append(inbox[o], [action |-> "sync_unregister", name |-> item_to_remove])]
    /\ UNCHANGED <<next_val>>

SyncUnregister(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "sync_unregister"
    /\ locally_registered' = [locally_registered EXCEPT![n] = locally_registered[n] \ {Head(inbox[n]).name}]
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ UNCHANGED <<registered, next_val>>

Complete ==
    /\ next_val = MaxValues
    /\ UNCHANGED <<inbox, registered, next_val, locally_registered>>

Next ==
    /\ \E n \in Nodes:
        \/ Register(n)
        \/ SyncRegister(n)
        \/ Unregister(n)
        \/ SyncUnregister(n)
        \/ Complete

Spec == Init /\ [][Next]_vars

AllRegistered ==
    \A n \in Nodes:
        Len(inbox[n]) = 0 => locally_registered[n] = registered

AllMessagesProcessed ==
    \A n \in Nodes:
        <>(Len(inbox[n]) = 0)
====
