----------------------------- MODULE MultiPaxos -----------------------------
\* Heavily inspired by (https://github.com/nano-o/MultiPaxos/blob/master/MultiPaxos.tla)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Acceptors, Values, Ballots

-------------------------------------------------------------------------------
Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n >= m

Max(S, LessEq(_,_)) == IF S = {} THEN -1
                                 ELSE CHOOSE n \in S: \A m \in S: LessEq(m,n)
-------------------------------------------------------------------------------
Instances == {1,2,3}

Quorums == {Q \in SUBSET Acceptors: Cardinality(Q)*2 > Cardinality(Acceptors)}

None == CHOOSE v: v \notin Values

Messages == [type:{"prepare"}, bal: Ballots]
                \union
            [type:{"promise"}, bal: Ballots, maxVBal: Ballots \union {-1},maxVVal: Values \union {None},acc: Acceptors]
                \union
            [type:{"accept"},  bal: Ballots, val: Values]
                \union
            [type:{"accepted"},maxVBal: Ballots, maxVVal: Values, acc: Acceptors]

-------------------------------------------------------------------------------
VARIABLES ballot, 1amsgs, 1bmsgs, 2amsgs, vote, leaderVote

TypeOK == /\ ballot \in [Acceptors -> Ballots \union {-1}]
          /\ 1amsgs \subseteq {<<b>>: b \in Ballots}
          /\ vote \in [Acceptors -> [Instances -> [Ballots -> Values \union {None}]]]


allEntries == {<< i, <<b,v>> >>: i \in Instances, b \in Ballots \union {-1}, v \in Values \union {None}}

-------------------------------------------------------------------------------
MaxVotedBallot(i, a, max) == Max({b \in Ballots: b <= max /\ vote[a][i][b] # None} \union {-1}, <=)

MaxVotedBallots(i, Q, max) == {MaxVotedBallot(i,a,max): a \in Q}

HighestVote(i, max, Q) == IF \E a \in Q: MaxVotedBallot(i,a,max) # -1
                          THEN LET MaxVoter == CHOOSE a \in Q: MaxVotedBallot(i,a,max) = Max(MaxVotedBallots(i,Q,max),<=)
                               IN vote[MaxVoter][i][MaxVotedBallot(i,MaxVoter,max)]
                          ELSE None
                          
-------------------------------------------------------------------------------
Init == /\ ballot = [a \in Acceptors |-> 0]
        /\ 1amsgs = {}
        /\ 1bmsgs = {}
        /\ 2amsgs = {}
        /\ vote = [a \in Acceptors |-> [i \in Instances |-> [b \in Ballots |->None]]]
        /\ leaderVote = [b \in Ballots |-> [i \in Instances |-> <<-1, None>>]]

Phase1a(b) == /\ ~\E msg \in 1amsgs: msg[1] = b
              /\ 1amsgs' = 1amsgs \union {<<b>>}
              /\ UNCHANGED <<ballot, 1bmsgs, 2amsgs, vote, leaderVote>>

MaxBallotAndVote(a, i, max) == LET maxBallot == Max({b \in Ballots: b <= max /\ vote[a][i][b] # None} \union {-1}, <=)
                                   v == IF maxBallot = -1 THEN None
                                                           ELSE vote[a][i][maxBallot]
                               IN <<maxBallot,v>>

Phase1b(a, b) == /\ ballot[a] < b
                 /\ <<b>> \in 1amsgs
                 /\ ballot' = [ballot EXCEPT ![a] = b]
                 /\ 1bmsgs' = 1bmsgs \union {<<a,b,{<<i,MaxBallotAndVote(a,i,b-1)>>: i \in Instances}>>}
                 /\ UNCHANGED <<1amsgs,2amsgs,vote,leaderVote>> 

1bMsgs(b, Q) == {m \in 1bmsgs: m[1] \in Q /\ m[2] = b}

MaxVote(i, b, Q) == LET entries == UNION{m[3]: m \in 1bMsgs(b,Q)}
                        ientries == {e \in entries: e[1] = i}
                        maxVBal == Max({e[2][1]: e \in ientries},<=)
                    IN CHOOSE v \in Values \union {None}: \E e \in ientries: /\ e[2][1] = maxVBal
                                                                             /\ e[2][2] = v

LastInstance(b, Q) == LET entries == UNION{m[3]: m \in 1bMsgs(b,Q)}
                          valid == {e \in entries: e[2][1] # -1}
                      IN IF valid = {} THEN -1
                                       ELSE Max({e[1]: e \in valid}, <=)

Merge(b) == /\ \E Q \in Quorums:
                /\ \A a \in Q: \E m \in 1bMsgs(b,Q): m[1] = a
                /\ \E v \in Values: leaderVote' = [leaderVote EXCEPT ![b] = [i \in Instances |->
                                                        IF (i \in 0..LastInstance(b,Q) /\ leaderVote[b][i][1] = -1)
                                                            THEN IF MaxVote(i,b,Q) = None THEN <<b,v>>
                                                                                          ELSE <<b,MaxVote(b,i,Q)>>
                                                            ELSE leaderVote[b][i] ]]
            /\ UNCHANGED <<vote,ballot,1amsgs,1bmsgs,2amsgs>>
        
-------------------------------------------------------------------------------
Conservative(i,b) == \A a1,a2 \in Acceptors: LET v1 == vote[a1][i][b]
                                                 v2 == vote[a2][i][b]
                                             IN (v1 # None /\ v2 # None) => v1 = v2

ConservativeVoteArray == \A i \in Instances: \A b \in Ballots: Conservative(i,b)

=============================================================================
\* Modification History
\* Last modified Fri Jan 15 15:37:35 CST 2021 by Dell
\* Created Wed Jan 13 20:45:35 CST 2021 by Dell
