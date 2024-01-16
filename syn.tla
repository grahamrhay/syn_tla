---- MODULE syn ----
EXTENDS FiniteSets, Integers, Sequences, TLC

CONSTANTS Nodes, MaxDisconnections

Symmetry == Permutations(Nodes)

VARIABLES inbox, registered, locally_registered, names, visible_nodes, states, disconnections, time

vars == <<inbox, registered, locally_registered, names, visible_nodes, states, disconnections, time>>

AllOtherNodes(n) ==
    Nodes \ {n}

Init ==
    /\ inbox = [n \in Nodes |-> <<>>]
    /\ registered = {}
    /\ locally_registered = [n1 \in Nodes |-> [n2 \in Nodes |-> <<>>]]
    /\ names = {"a"}
    /\ disconnections = 0
    /\ visible_nodes = [n \in Nodes |-> AllOtherNodes(n)]
    /\ time = 0
    /\ states = <<>>

Register(n) ==
    /\ names # {}
    /\ LET next_val == CHOOSE o \in names: TRUE
        l == [locally_registered[n] EXCEPT![n] = locally_registered[n][n] @@ [r \in {next_val} |-> time]]
        IN registered' = registered \union {next_val}
        /\ locally_registered' = [locally_registered EXCEPT![n] = l]
        /\ names' = names \ {next_val}
        /\ inbox' = [o \in Nodes |-> IF o \in visible_nodes[n] THEN Append(inbox[o], [action |-> "sync_register", name |-> next_val, from |-> n, time |-> time]) ELSE inbox[o]]
        /\ states' = Append(states, <<"Register", n, next_val>>)
    /\ time' = time + 1
    /\ UNCHANGED <<visible_nodes, disconnections>>

SyncRegister(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "sync_register"
    /\ LET message == Head(inbox[n])
        l == [locally_registered[n] EXCEPT![message.from] = locally_registered[n][message.from] @@ [r \in {message.name} |-> message.time]]
        IN locally_registered' = [locally_registered EXCEPT![n] = l]
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ time' = time + 1
    /\ states' = Append(states, <<"SyncRegister", n, Head(inbox[n]).name>>)
    /\ UNCHANGED <<registered, names, visible_nodes, disconnections>>

ItemToRemove(n) ==
    CHOOSE r \in DOMAIN locally_registered[n][n]: TRUE

Unregister(n) ==
    /\ Cardinality(DOMAIN locally_registered[n][n]) > 0
    /\ LET item_to_remove == ItemToRemove(n)
        l == [r \in (DOMAIN locally_registered[n][n] \ {item_to_remove}) |-> locally_registered[n][n][r]]
        IN registered' = registered \ {item_to_remove}
        /\ locally_registered' = [locally_registered EXCEPT![n] = ([locally_registered[n] EXCEPT![n] = l])]
        /\ inbox' = [o \in Nodes |-> IF o \in visible_nodes[n] THEN Append(inbox[o], [action |-> "sync_unregister", name |-> item_to_remove, from |-> n]) ELSE inbox[o]]
        /\ states' = Append(states, <<"Unregister", n, item_to_remove>>)
    /\ time' = time + 1
    /\ UNCHANGED <<names, visible_nodes, disconnections>>

SyncUnregister(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "sync_unregister"
    /\ LET message == Head(inbox[n])
        l == [r \in (DOMAIN locally_registered[n][message.from] \ {message.name}) |-> locally_registered[n][message.from][r]]
        IN locally_registered' = [locally_registered EXCEPT![n] = [locally_registered[n] EXCEPT![message.from] = l]]
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ time' = time + 1
    /\ states' = Append(states, <<"SyncUnregister", n, Head(inbox[n]).name>>)
    /\ UNCHANGED <<registered, names, visible_nodes, disconnections>>

Disconnect(n) ==
    /\ disconnections < MaxDisconnections
    /\ Cardinality(visible_nodes[n]) > 0
    /\ LET other_node == CHOOSE o \in visible_nodes[n]: TRUE
        IN visible_nodes' = [o \in Nodes |-> CASE
            (o = other_node) -> visible_nodes[o] \ {n}
            [] (o = n) -> visible_nodes[o] \ {other_node}
            [] OTHER -> visible_nodes[o]
        ]
        /\ inbox' = [o \in Nodes |-> CASE
            (o = n) -> Append(inbox[o], [action |-> "DOWN", from |-> other_node])
            [] (o = other_node) -> Append(inbox[o], [action |-> "DOWN", from |-> n])
            [] OTHER -> inbox[o]
        ]
        /\ states' = Append(states, <<"Disconnect", n, other_node>>)
    /\ disconnections' = disconnections + 1
    /\ time' = time + 1
    /\ UNCHANGED <<registered, locally_registered, names>>

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
        /\ states' = Append(states, <<"Reconnect", n, other_node>>)
    /\ time' = time + 1
    /\ UNCHANGED <<registered, locally_registered, names, disconnections>>

Discover(n) ==
    /\ Len(inbox[n]) > 0
    /\ LET message == Head(inbox[n])
        IN message.action = "discover"
        /\ inbox' = [o \in Nodes |-> CASE
            (o = n) -> Tail(inbox[o])
            [] (o = message.from) -> Append(inbox[o], [action |-> "ack_sync", local_data |-> locally_registered[n][n], from |-> n])
            [] OTHER -> inbox[o]
        ]
        /\ states' = Append(states, <<"Discover", n, message.from>>)
    /\ time' = time + 1
    /\ UNCHANGED <<registered, names, visible_nodes, locally_registered, disconnections>>

AckSync(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "ack_sync"
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ LET message == Head(inbox[n])
        l == [locally_registered[n] EXCEPT![message.from] = message.local_data]
        IN locally_registered' = [locally_registered EXCEPT![n] = l]
        /\ states' = Append(states, <<"AckSync", n, message.from>>)
    /\ time' = time + 1
    /\ UNCHANGED <<registered, names, visible_nodes, disconnections>>

Down(n) ==
    /\ Len(inbox[n]) > 0
    /\ Head(inbox[n]).action = "DOWN"
    /\ inbox' = [inbox EXCEPT![n] = Tail(inbox[n])]
    /\ LET message == Head(inbox[n])
        l == [locally_registered[n] EXCEPT![message.from] = <<>>]
        IN locally_registered' = [locally_registered EXCEPT![n] = l]
        /\ states' = Append(states, <<"Down", n, message.from>>)
    /\ time' = time + 1
    /\ UNCHANGED <<registered, names, visible_nodes, disconnections>>

Complete ==
    /\ names = {}
    /\ UNCHANGED <<inbox, registered, names, locally_registered, visible_nodes, disconnections, time, states>>

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
        \/ Down(n)
        \/ Complete

Spec == Init /\ [][Next]_vars

RECURSIVE ReduceStruct(_, _, _)

ReduceStruct(keys, struct, acc) ==
    IF keys = {} THEN acc
    ELSE
        LET k == CHOOSE k \in keys: TRUE
        IN ReduceStruct(keys \ {k}, struct, acc \union DOMAIN struct[k])

AllRegisteredForNode(locals) ==
    ReduceStruct(DOMAIN locals, locals, {})

AllRegistered ==
    \A n \in Nodes:
        (\A o \in Nodes: Len(inbox[o]) = 0) /\ visible_nodes[n] = AllOtherNodes(n) => AllRegisteredForNode(locally_registered[n]) = registered

AllMessagesProcessed ==
    \A n \in Nodes:
        <>(Len(inbox[n]) = 0)
====
