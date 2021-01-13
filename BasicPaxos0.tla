---------------------------- MODULE BasicPaxos0 ----------------------------
EXTENDS Integers, FiniteSets


Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n >= m

CONSTANTS Acceptors, Ballot, Value

NoneValue == CHOOSE v : v \notin Value

Messages == [type:{"prepare"}, bal: Ballot]
                \union
            [type:{"promise"}, bal: Ballot, maxVBal: Ballot \union {-1},maxVVal: Value \union {NoneValue},acc: Acceptors]
                \union
            [type:{"accept"},  bal: Ballot, val: Value]
                \union
            [type:{"accepted"},maxVBal: Ballot, maxVVal: Value, acc: Acceptors]
            
Quorums == {Q \in SUBSET Acceptors: Cardinality(Q)*2>Cardinality(Acceptors)}

ASSUME /\ Ballot \subseteq Nat
       /\ 0 \in Ballot
       /\ \A Q1,Q2 \in Quorums: Q1 \intersect Q2 /= {}

-----------------------------------------------------------------------------
VARIABLES state, msgs

vars == <<state, msgs>>

TypeOK == /\ state \in [Acceptors -> [maxBal: Ballot \union {-1},
                                      maxVBal: Ballot \union {-1},
                                      maxVVal: Value \union {NoneValue}]]
          /\ msgs \subseteq Messages

Send(m) == msgs' = msgs \union {m}

-----------------------------------------------------------------------------
Init == /\ state = [a \in Acceptors |->[maxBal|->-1,maxVBal|->-1,maxVVal|->NoneValue]]
        /\ msgs = {}

Prepare(b) == /\ ~\E m \in msgs: m.type = "prepare" /\ m.bal = b
              /\ Send([type|->"prepare",bal|->b])
              /\ UNCHANGED state

Promise(acc) == \E msg \in msgs: /\ msg.type = "prepare"
                                 /\ state[acc].maxBal < msg.bal
                                 /\ state' = [state EXCEPT ![acc].maxBal = msg.bal]
                                 /\ Send([type   |->"promise",
                                          bal    |->msg.bal,
                                          maxVBal|->state[acc].maxVBal,
                                          maxVVal|->state[acc].maxVVal,
                                          acc    |->acc])

Accept(b) == /\ ~\E m \in msgs: m.type = "accept" /\ m.bal = b
             /\ \E Q \in Quorums:
                LET mset == {m \in msgs: /\ m.type = "promise"
                                         /\ m.bal = b
                                         /\ m.acc \in Q}
                    mu == Maximum({m.maxVBal: m \in mset})
                    v == IF mu = -1 THEN CHOOSE val \in Value: TRUE
                                    ELSE (CHOOSE m \in mset: m.maxVBal = mu).maxVVal
                IN /\ \A ac \in Q: \E m \in mset: m.acc = ac
                   /\ Send([type|->"accept",bal|->b,val|->v])
             /\ UNCHANGED state

Accepted(acc) == \E msg \in msgs:  /\ msg.type = "accept"
                                   /\ state[acc].maxBal <= msg.bal
                                   /\ state[acc].maxVBal < msg.bal
                                   /\ state' = [state EXCEPT ![acc].maxBal = msg.bal,
                                                             ![acc].maxVBal = msg.bal,
                                                             ![acc].maxVVal = msg.val]
                                   /\ Send([type|->"accepted",maxVBal|->msg.bal,maxVVal|->msg.val,acc|->acc])

Next == \/ \E b \in Ballot: Prepare(b) \/ Accept(b)
        \/ \E a \in Acceptors: Promise(a) \/ Accepted(a)
        
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
VoteForIn(a,v,b) == \E m \in msgs: /\ m.type = "accepted"
                                   /\ m.maxVVal = v
                                   /\ m.maxVBal = b
                                   /\ m.acc = a
                                   
\* There exists a quorum accepting the proposal(b,v)
ChosenIn(v,b) == \E Q \in Quorums: 
                    \A a\in Q: VoteForIn(a,v,b)

Chosen(v) == \E b \in Ballot: ChosenIn(v,b)

\* Only a value is chosen in a ballot
Consistency == \A v1,v2 \in Value: Chosen(v1) /\ Chosen(v2) => (v1 = v2)

ChosenSet == {v \in Value: \E b \in Ballot:
                               \E Q \in Quorums: \A a \in Q: /\ state[a].maxVBal = b
                                                             /\ state[a].maxVVal = v}
\* There exists some value being chosen eventually
\* And it should be false, because Paxos does not satisfy liveness
Liveness == <>(ChosenSet /= {})

=============================================================================
\* Create on 1/11/2021


=============================================================================
\* Modification History
\* Last modified Wed Jan 13 17:00:17 CST 2021 by Dell
\* Created Tue Jan 12 17:39:42 CST 2021 by Dell
