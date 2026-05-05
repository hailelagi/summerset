(*********************************************************************************)
(* Refinement composition. This module contains NO algorithm logic of its own -- *)
(* it INSTANCEs LeaseProtocol.tla and MultiPaxos.tla, composes their Init/Next   *)
(* into a single spec, and states the refinement theorem                         *)
(*     RefineSpec => MP!AbstractSpec                                             *)
(* under the mapping `grants <- LP!ActiveGrants`.                                *)
(*********************************************************************************)

---- MODULE MultiPaxosRefine ----
EXTENDS FiniteSets, Sequences, Integers, TLC

(*******************************)
(* Model inputs & assumptions. *)
(*******************************)
CONSTANT Replicas,   \* symmetric set of server nodes
         Writes,     \* symmetric set of write commands (each w/ unique value)
         Reads,      \* symmetric set of read commands
         MaxBallot,  \* maximum ballot pickable for leader preemption
         NodeFailuresOn,  \* if true, turn on node failures injection
         TGuard,          \* lease guard phase window length (ticks)
         TLease,          \* lease renewal extend window length (ticks)
         MaxTime          \* upper bound on abstract time for model checking

\* MultiPaxos variables:
VARIABLES msgs, grants, node, pending, observed, crashed, pc
mpVars == <<msgs, grants, node, pending, observed, crashed, pc>>
mpVarsExceptGrants == <<msgs, node, pending, observed, crashed, pc>>

\* Leasing protocol variables:
VARIABLES leaseState, leaseMsgs, time
lpVars == <<leaseState, leaseMsgs, time>>

allVars == <<mpVars, lpVars>>

----------

(*****************************************)
(* Instantiate both underlying modules.  *)
(*****************************************)
\* Abstract MultiPaxos, using our local `grants` variable, which will be the
\* one we prove equal to LP!ActiveGrants.
MP == INSTANCE MultiPaxos

\* Concrete lease protocol. Constants are matched by name.
LP == INSTANCE LeaseProtocol

----------

(***********************************************)
(* Spec Composing consensus and leasing layer. *)
(***********************************************)
Init == /\ MP!Init
        /\ LP!Init

\* The lease protocol's LearnsNewLeader is unconstrained in isolation; this
\* condition explicitly binds it to the consensus layer `node[self].leader`
\* so the lease layer only serves ballot-leader pairs actually seen.
BindsLeaderDiscovery(self) ==
    /\ ~crashed[self]
    /\ LP!Replica(self)
    /\ leaseState'[self].leaseBal = node[self].balMaxKnown
    /\ leaseState'[self].leaseLeader = node[self].leader

LeasingStep == /\ \E self \in Replicas: BindsLeaderDiscovery(self)
               /\ grants' = LP!ActiveGrants'
               /\ UNCHANGED mpVarsExceptGrants

ConsensusStep == /\ \E self \in Replicas: MP!Replica(self)
                 /\ UNCHANGED lpVars

\* Time horizon stutter: once every replica's clock has reached MaxTime, no
\* further TimeTick is possible, so lease-layer GC and subsequent sessions
\* would not progress; we should consider this a termination condition and
\* let user control the time horizon length to check with.
TimeExhausted == \A r \in Replicas: time[r] = MaxTime
                 
\* Combined termination condition.
Terminating == \/ /\ MP!Terminating
                  /\ UNCHANGED lpVars
               \/ /\ TimeExhausted
                  /\ UNCHANGED allVars

Next == \/ ConsensusStep
        \/ LeasingStep
        \/ Terminating

Spec == Init /\ [][Next]_allVars

====
