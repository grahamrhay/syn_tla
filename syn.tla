---- MODULE syn ----
EXTENDS FiniteSets, Integers

VARIABLES registered, next_val, added, removed

vars == <<registered, next_val, added, removed>>

Init ==
    /\ registered = {}
    /\ next_val = 0
    /\ added = 0
    /\ removed = 0

Register ==
    /\ next_val < 5
    /\ registered' = registered \union {next_val}
    /\ next_val' = next_val + 1
    /\ added' = added + 1
    /\ UNCHANGED <<removed>>

ItemToRemove ==
    CHOOSE r \in registered: TRUE

Unregister ==
    /\ Cardinality(registered) > 0
    /\ registered' = registered \ {ItemToRemove}
    /\ removed' = removed + 1
    /\ UNCHANGED <<added, next_val>>

Complete ==
    /\ next_val = 5
    /\ UNCHANGED <<added, next_val, registered, removed>>

Next ==
    \/ Register
    \/ Unregister
    \/ Complete

Spec == Init /\ [][Next]_vars

AllRegistered == Cardinality(registered) = (added - removed)
====
