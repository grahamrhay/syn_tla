---- MODULE syn_tests ----
EXTENDS syn

VARIABLE x

I == FALSE /\ x = 0
N == FALSE /\ x' = x

\* AllRegisteredForNode

ASSUME LET l == ("n1" :> <<>> @@ "n2" :> [a |-> 0, b |-> 2] @@ "n3" :> [c |-> 1])
       res == AllRegisteredForNode(l)
       IN res = {"a", "b", "c"}

\* Duplicates

ASSUME LET l == ("n1" :> <<>> @@ "n2" :> [a |-> 0] @@ "n3" :> [a |-> 1])
       res == Duplicates(DOMAIN l, l, {})
       IN res = {"a"}
====
