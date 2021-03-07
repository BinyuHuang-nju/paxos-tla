------------------------------- MODULE TPaxos -------------------------------
\* Copied from my junior.
\* (https://github.com/Starydark/PaxosStore-tla/blob/master/specification/TPaxos.tla)

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

MaxBallot == Cardinality(Ballot) - 1

PIndex == CHOOSE f \in [Participant -> 1 .. Cardinality(Participant)]: Injective(f)
Bals(p) == {b \in Ballot: b % Cardinality(Participant) = PIndex[p] - 1} \* allocate ballots for each p \in Participant
-----------------------------------------------------------------------------
State == [maxBal: Ballot \union {-1}, maxVBal: Ballot \union {-1}, maxVVal: Value \union {None}]

InitState == [maxBal |-> -1,maxVBal |-> -1,maxVVal |-> None]
(*
For simplicity, in this specification, we choose to send the complete state
of a participant each time. When receiving such a message, the participant 
processes only the "partial" state it needs.
*)
Message == [from:Participant, to: SUBSET Participant, state:[Participant -> State]]
-----------------------------------------------------------------------------
VARIABLES state, \* state[p][q]: the state of q \in Participant from the view of p \in Participant
          msgs   \* the set of messages that have been sent

vars == <<state,msgs>>

TypeOK == /\ state \in [Participant -> [Participant -> State]]
          /\ msgs \subseteq Message

Send(m) == msgs' = msgs \union {m}
-----------------------------------------------------------------------------
Init == /\ state = [p \in Participant |->[q \in Participant |-> InitState]]
        /\ msgs = {}

(*
p \in Participant starts the prepare phase by issuing a ballot b \in Ballot.
*)
Prepare(p, b) == /\ b \in Bals(p)
                 /\ state[p][p].maxBal < b
                 /\ state' = [state EXCEPT ![p][p].maxBal = b]
                 /\ Send([from |-> p, to |-> Participant \ {p}, state |-> state'[p]])

(*
q \in Participant updates its own state state[q] according to the actual state
pp of p \in Participant extracted from a message m \in Message it receives. 
This is called by OnMessage(q).
Note: pp is m.state[p]; it may not be equal to state[p][p] at the time 
UpdateState is called.
*)
UpdateState(q, p, pp) == LET maxB == Max(state[q][q].maxBal, pp.maxBal)
                         IN state' = [state EXCEPT ![q][p].maxBal = Max(@, pp.maxBal),
                                                   ![q][p].maxVBal = Max(@, pp.maxBal),
                                                   ![q][p].maxVVal = IF state[q][p].maxVBal < pp.maxVBal
                                                                     THEN pp.maxVVal ELSE @,
                                                   ![q][q].maxBal = maxB,                    \* make promise first and then accept
                                                   ![q][q].maxVBal = IF maxB <= pp.maxVBal   \* accept
                                                                     THEN pp.maxVBal ELSE @,
                                                   ![q][q].maxVVal = IF maxB <= pp.maxVBal   \* accept
                                                                     THEN pp.maxVVal ELSE @]
=============================================================================
\* Modification History
\* Last modified Sun Mar 07 21:49:23 CST 2021 by Dell
\* Created Sat Mar 06 18:00:00 CST 2021 by Dell
