------------------------------- MODULE TPaxos -------------------------------
EXTENDS Integers, FiniteSets

Max(m, n) == IF m > n THEN m ELSE n
Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])
-----------------------------------------------------------------------------
CONSTANTS Participant,  \* the set of participants
          Value         \* the set of possible input values for Participant to propose

None == CHOOSE b: b \notin Value

Quorum == {Q \in SUBSET Participant: Cardinality(Q)*2 > Cardinality(Participant)}

ASSUME QuorumAssumption == /\ \A Q \in Quorum: Q \subseteq Participant
                           /\ \A Q1, Q2 \in Quorum: Q1 \cap Q2 # {}

Ballot == Nat
=============================================================================
\* Modification History
\* Last modified Sat Mar 06 22:07:02 CST 2021 by Dell
\* Created Sat Mar 06 18:00:00 CST 2021 by Dell
