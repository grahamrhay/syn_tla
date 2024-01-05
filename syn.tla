---- MODULE syn ----
EXTENDS FiniteSets, Integers, Sequences

CONSTANTS Nodes, MaxValues

VARIABLES inbox, registered, next_val, added, removed

vars == <<inbox, registered, next_val, added, removed>>

Init ==
    /\ inbox = [n \in Nodes |-> <<>>]
    /\ registered = [n \in Nodes |-> {}]
    /\ next_val = 0
    /\ added = 0
    /\ removed = 0

Register(n) ==
    /\ \A o \in Nodes: Len(inbox[o]) = 0
    /\ next_val < MaxValues
    /\ registered' = [registered EXCEPT![n] = registered[n] \union {next_val}]
    /\ next_val' = next_val + 1
    /\ added' = added + 1
    /\ inbox' = [o \in Nodes |-> IF o = n THEN inbox[o] ELSE Append(inbox[o], [action |-> "sync_register", name |-> next_val])]
    /\ UNCHANGED <<removed>>

SyncRegister(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "sync_register"
    /\ registered' = [registered EXCEPT![n] = registered[n] \union {Head(inbox[n]).name}]
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ UNCHANGED <<removed, added, next_val>>

ItemToRemove(n) ==
    CHOOSE r \in registered[n]: TRUE

Unregister(n) ==
    /\ \A o \in Nodes: Len(inbox[o]) = 0
    /\ Cardinality(registered[n]) > 0
    /\ LET item_to_remove == ItemToRemove(n)
        IN registered' = [registered EXCEPT![n] = registered[n] \ {item_to_remove}]
        /\ inbox' = [o \in Nodes |-> IF o = n THEN inbox[o] ELSE Append(inbox[o], [action |-> "sync_unregister", name |-> item_to_remove])]
    /\ removed' = removed + 1
    /\ UNCHANGED <<added, next_val>>

SyncUnregister(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "sync_unregister"
    /\ registered' = [registered EXCEPT![n] = registered[n] \ {Head(inbox[n]).name}]
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ UNCHANGED <<removed, added, next_val>>

Complete ==
    /\ next_val = MaxValues
    /\ UNCHANGED <<inbox, added, next_val, registered, removed>>

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
        Len(inbox[n]) = 0 => Cardinality(registered[n]) = (added - removed)

AllMessagesProcessed ==
    \A n \in Nodes:
        <>(Len(inbox[n]) = 0)
====
