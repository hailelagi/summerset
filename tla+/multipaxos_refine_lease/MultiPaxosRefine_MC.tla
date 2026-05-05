---- MODULE MultiPaxosRefine_MC ----
EXTENDS MultiPaxosRefine

\* INSTANCE the `_MC` definitions of the two underlying modules so we can
\* reuse the invariants they already defined.
LPMC == INSTANCE LeaseProtocol_MC
MPMC == INSTANCE MultiPaxos_MC

(****************************)
(* TLC config-related defs. *)
(****************************)
ConditionalPerm(set) == IF Cardinality(set) > 1
                          THEN Permutations(set)
                          ELSE {}

SymmetricPerms ==      ConditionalPerm(Replicas)
                  \cup ConditionalPerm(Writes)
                  \cup ConditionalPerm(Reads)

ConstMaxBallot == 2

ConstTGuard == 1

ConstTLease == 1

ConstMaxTime == 3

----------

(*************************)
(* Type check invariant. *)
(*************************)
FullTypeOK == /\ \A m \in msgs: m \in MP!Messages
              /\ \A lm \in leaseMsgs: lm \in LP!LeaseMsgs
              /\ \A g \in grants: g \in MP!LeaseGrants
              /\ \A r \in Replicas: node[r] \in MP!NodeStates
              /\ \A r \in Replicas: leaseState[r] \in LP!LeaseStates
              /\ \A r \in Replicas: time[r] \in LP!Times
              /\ Len(pending) =< MP!NumCommands
              /\ Cardinality(MP!Range(pending)) = Len(pending)
              /\ \A c \in MP!Range(pending): c \in MP!Commands
              /\ Len(observed) =< 2 * MP!NumCommands
              /\ Cardinality(MP!Range(observed)) = Len(observed)
              /\ Cardinality(MP!reqsMade) >= Cardinality(MP!acksRecv)
              /\ \A e \in MP!Range(observed): e \in MP!ClientEvents
              /\ \A r \in Replicas: crashed[r] \in BOOLEAN

THEOREM Spec => []FullTypeOK

----------

(*******************************************)
(* Plain-name re-definition of properties. *)
(*******************************************)
LeaseExpirationSafety == LPMC!LeaseExpirationSafety

AtMostOneGrantPerNode == MPMC!AtMostOneGrantPerNode
AtMostOneStableLeader == MPMC!AtMostOneStableLeader

\* the refinement: every behavior of this composed spec is, when viewed through
\* `grants = LP!ActiveGrants` lens, a legal behavior of the higher MultiPaxos spec
RefinesMultiPaxos == MP!AbstractSpec

----------

(************************)
(* Refinement theorem.  *)
(************************)
GrantsEqualsActive == grants = LP!ActiveGrants

THEOREM Spec => /\ MP!AbstractSpec
                /\ []GrantsEqualsActive

====
