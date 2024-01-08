---- MODULE syn ----
EXTENDS FiniteSets, Integers, Sequences

CONSTANTS Nodes, MaxValues

VARIABLES inbox, registered, locally_registered, next_val, visible_nodes, states

vars == <<inbox, registered, locally_registered, next_val, visible_nodes, states>>

AllOtherNodes(n) ==
    Nodes \ {n}

Init ==
    /\ inbox = [n \in Nodes |-> <<>>]
    /\ registered = {}
    /\ locally_registered = [n \in Nodes |-> {}]
    /\ next_val = 0
    /\ visible_nodes = [n \in Nodes |-> AllOtherNodes(n)]
    /\ states = <<>>

Register(n) ==
    /\ next_val < MaxValues
    /\ registered' = registered \union {next_val}
    /\ locally_registered' = [locally_registered EXCEPT![n] = locally_registered[n] \union {next_val}]
    /\ next_val' = next_val + 1
    /\ inbox' = [o \in Nodes |-> IF o \in visible_nodes[n] THEN Append(inbox[o], [action |-> "sync_register", name |-> next_val]) ELSE inbox[o]]
    /\ states' = Append(states, "Register")
    /\ UNCHANGED <<visible_nodes>>

SyncRegister(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "sync_register"
    /\ locally_registered' = [locally_registered EXCEPT![n] = locally_registered[n] \union {Head(inbox[n]).name}]
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ states' = Append(states, "SyncRegister")
    /\ UNCHANGED <<registered, next_val, visible_nodes>>

ItemToRemove(n) ==
    CHOOSE r \in locally_registered[n]: TRUE

Unregister(n) ==
    /\ Cardinality(locally_registered[n]) > 0
    /\ LET item_to_remove == ItemToRemove(n)
        IN registered' = registered \ {item_to_remove}
        /\ locally_registered' = [locally_registered EXCEPT![n] = locally_registered[n] \ {item_to_remove}]
        /\ inbox' = [o \in Nodes |-> IF o \in visible_nodes[n] THEN Append(inbox[o], [action |-> "sync_unregister", name |-> item_to_remove]) ELSE inbox[o]]
    /\ states' = Append(states, "Unregister")
    /\ UNCHANGED <<next_val, visible_nodes>>

SyncUnregister(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "sync_unregister"
    /\ locally_registered' = [locally_registered EXCEPT![n] = locally_registered[n] \ {Head(inbox[n]).name}]
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ states' = Append(states, "SyncUnregister")
    /\ UNCHANGED <<registered, next_val, visible_nodes>>

Disconnect(n) ==
    /\ Cardinality(visible_nodes[n]) > 0
    /\ LET other_node == CHOOSE o \in visible_nodes[n]: TRUE
        IN visible_nodes' = [o \in Nodes |-> CASE
            (o = other_node) -> visible_nodes[o] \ {n}
            [] (o = n) -> visible_nodes[o] \ {other_node}
            [] OTHER -> visible_nodes[o]
        ]
    /\ states' = Append(states, "Disconnect")
    /\ UNCHANGED <<registered, locally_registered, inbox, next_val>>

Reconnect(n) ==
    /\ Cardinality(AllOtherNodes(n) \ visible_nodes[n]) > 0
    /\ LET other_node == CHOOSE o \in (AllOtherNodes(n) \ visible_nodes[n]): TRUE
        IN visible_nodes' = [o \in Nodes |-> CASE
            (o = other_node) -> visible_nodes[o] \union {n}
            [] (o = n) -> visible_nodes[o] \union {other_node}
            [] OTHER -> visible_nodes[o]
        ]
        /\ inbox' = [o \in Nodes |-> CASE
            (o = n) -> Append(inbox[o], [action |-> "discover", from |-> other_node])
            [] (o = other_node) -> Append(inbox[o], [action |-> "discover", from |-> n])
            [] OTHER -> inbox[o]
        ]
    /\ states' = Append(states, "Reconnect")
    /\ UNCHANGED <<registered, locally_registered, next_val>>

Discover(n) ==
    /\ Len(inbox[n]) > 0
    /\ LET message == Head(inbox[n])
        IN message.action = "discover"
        /\ inbox' = [o \in Nodes |-> CASE
            (o = n) -> Tail(inbox[o])
            [] (o = message.from) -> Append(inbox[o], [action |-> "ack_sync", local_data |-> locally_registered[n]])
            [] OTHER -> inbox[o]
        ]
    /\ states' = Append(states, "Discover")
    /\ UNCHANGED <<registered, next_val, visible_nodes, locally_registered>>

AckSync(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "ack_sync"
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ LET message == Head(inbox[n])
        IN locally_registered' = [locally_registered EXCEPT![n] = locally_registered[n] \union message.local_data]
    /\ states' = Append(states, "AckSync")
    /\ UNCHANGED <<registered, next_val, visible_nodes>>

Complete ==
    /\ next_val = MaxValues
    /\ UNCHANGED <<inbox, registered, next_val, locally_registered, visible_nodes, states>>

Next ==
    /\ \E n \in Nodes:
        \/ Register(n)
        \/ SyncRegister(n)
        \/ Unregister(n)
        \/ SyncUnregister(n)
        \/ Disconnect(n)
        \/ Reconnect(n)
        \/ Discover(n)
        \/ AckSync(n)
        \/ Complete

Spec == Init /\ [][Next]_vars

AllRegistered ==
    \A n \in Nodes:
        (\A o \in Nodes: Len(inbox[o]) = 0) /\ visible_nodes[n] = AllOtherNodes(n) => locally_registered[n] = registered

AllMessagesProcessed ==
    \A n \in Nodes:
        <>(Len(inbox[n]) = 0)
====
