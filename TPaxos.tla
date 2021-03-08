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
                                                   ![q][p].maxVBal = Max(@, pp.maxVBal),
                                                   ![q][p].maxVVal = IF state[q][p].maxVBal < pp.maxVBal
                                                                     THEN pp.maxVVal ELSE @,
                                                   ![q][q].maxBal = maxB,                    \* make promise first and then accept
                                                   ![q][q].maxVBal = IF maxB <= pp.maxVBal   \* accept
                                                                     THEN pp.maxVBal ELSE @,
                                                   ![q][q].maxVVal = IF maxB <= pp.maxVBal   \* accept
                                                                     THEN pp.maxVVal ELSE @]
(*
q \in Participant receives and processes a message in Message.
*)               
OnMessage(q) == \E m \in msgs:
                    /\ q \in m.to
                    /\ LET p == m.from
                       IN UpdateState(q, p, m.state[p])
                    /\ LET qm == [from |-> m.from, to |-> m.to \ {q}, state |-> m.state] \* remove q from to
                           nm == [from |-> q, to |-> {m.from}, state |-> state'[q]]      \* new message to reply
                       IN IF \/ m.state[q].maxBal < state'[q][q].maxBal
                             \/ m.state[q].maxVBal < state'[q][q].maxVBal
                          THEN msgs' = (msgs \ {m}) \union {qm, nm}
                          ELSE msgs' = (msgs \ {m}) \union {qm}

Accept(p, b, v) == /\ b \in Bals(p)
                   /\ state[p][p].maxBal <= b \* corresponding the first conjunction in Voting
                   /\ state[p][p].maxVBal # b \* cooresponding the first conjunction in Voting
                   /\ \E Q \in Quorum:
                        /\ \A q \in Q: state[p][q].maxBal = b
                   /\ \/ \A q \in Participant: state[p][q].maxVBal = -1
                      \/ \E q \in Participant:
                            /\ state[p][q].maxVVal = v
                            /\ \A r \in Participant: state[p][q].maxVBal >= state[p][r].maxVBal
                   /\ state' = [state EXCEPT ![p][p].maxVBal = b,
                                             ![p][p].maxVVal = v]
                   /\ Send([from |-> p, to |-> Participant \ {p}, state |-> state'[p]]) 
-----------------------------------------------------------------------------   
Next == \E p \in Participant: \/ OnMessage(p)
                              \/ \E b \in Ballot: \/ Prepare(p, b)
                                                  \/ \E v \in Value: Accept(p,b,v)

Spec == Init /\ [][Next]_vars              
-----------------------------------------------------------------------------
ChosenP(p) == {v \in Value: \E b \in Ballot: 
                                \E Q \in Quorum: \A q\in Q: /\ state[p][q].maxVBal = b
                                                            /\ state[p][q].maxVVal = v}
chosen == UNION {ChosenP(p): p \in Participant}

Consistency == Cardinality(chosen) <= 1

THEOREM Spec => []Consistency
-----------------------------------------------------------------------------
(*
For checking Liveness
WF(A): if A ever becomes enabled, then an A step will eventually occur-even 
if A remains enabled for only a fraction of a nanosecond and is never again
enabled. 
Liveness in TPaxos: like paxos, there should be a single-leader to prapre
and accept.
*)

LConstrain == /\ \E p \in Participant:
                /\ MaxBallot \in Bals(p)
                /\ WF_vars(Prepare(p, MaxBallot))
                /\ \A v \in Value: WF_vars(Accept(p, MaxBallot, v))
                /\ \E Q \in Quorum:
                    /\ p \in Q
                    /\ \A q \in Q: WF_vars(OnMessage(q))

LSpec == Spec /\ LConstrain

Liveness == <>(chosen # {})
=============================================================================
\* Modification History
\* Last modified Mon Mar 08 14:38:59 CST 2021 by Dell
\* Created Sat Mar 06 18:00:00 CST 2021 by Dell
