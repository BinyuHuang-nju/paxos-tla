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

vars == <<leaderVote, ballot, vote, 1amsgs, 1bmsgs, 2amsgs>>

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

IncreaseBallot(a,b) == /\ ballot[a] < b
                       /\ ballot' = [ballot EXCEPT ![a] = b]
                       /\ UNCHANGED << vote, leaderVote, 1amsgs, 1bmsgs, 2amsgs>>

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

MaxVote(b, i, Q) == LET entries == UNION{m[3]: m \in 1bMsgs(b,Q)}
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
                                                        IF (i \in 1..LastInstance(b,Q) /\ leaderVote[b][i][1] = -1)
                                                            THEN IF MaxVote(i,b,Q) = None THEN <<b,v>>
                                                                                          ELSE <<b,MaxVote(b,i,Q)>>
                                                            ELSE leaderVote[b][i] ]]
            /\ UNCHANGED <<vote,ballot,1amsgs,1bmsgs,2amsgs>>

Propose(b,i) == /\ leaderVote[b][i][1] = -1
                /\ \E Q \in Quorums:
                    /\ \A a \in Q: \E m \in 1bMsgs(b,Q): m[1] = a
                    /\ \E v \in Values: leaderVote' = [leaderVote EXCEPT ![b][i] = IF MaxVote(b,i,Q) = None THEN <<b,v>>
                                                                                                            ELSE <<b,MaxVote(b,i,Q)>>]
                /\ UNCHANGED <<vote, ballot, 1amsgs, 1bmsgs, 2amsgs>>

Phase2a(b,i) == /\ leaderVote[b][i][1] = b
                /\ 2amsgs' = 2amsgs \union {<<b,i,leaderVote[b][i]>>}
                /\ UNCHANGED << ballot, vote, leaderVote, 1amsgs, 1bmsgs>>

Phase2b(a,b,i) == /\ ballot[a] <= b
                  /\ ballot' = [ballot EXCEPT ![a] = b]
                  /\ \E m \in 2amsgs: /\ m[2] = i
                                      /\ m[1] = b
                                      /\ vote' = [vote EXCEPT ![a][i][b] = m[3][2]]
                  /\ UNCHANGED << leaderVote, 1amsgs, 1bmsgs, 2amsgs>>

Next == 
    \/  \E a \in Acceptors, b \in Ballots : IncreaseBallot(a,b)
    \/  \E b \in Ballots : Phase1a(b)
    \/  \E a \in Acceptors, b \in Ballots : Phase1b(a,b)
    \/  \E b \in Ballots : Merge(b)
    \/  \E b \in Ballots, i \in Instances : Propose(b,i)
    \/  \E b \in Ballots, i \in Instances : Phase2a(b,i)
    \/  \E a \in Acceptors, b \in Ballots, i \in Instances : Phase2b(a, b, i)
    
Spec == Init /\ [][Next]_vars
-------------------------------------------------------------------------------
Conservative(i,b) == \A a1,a2 \in Acceptors: LET v1 == vote[a1][i][b]
                                                 v2 == vote[a2][i][b]
                                             IN (v1 # None /\ v2 # None) => v1 = v2

ConservativeVoteArray == \A i \in Instances: \A b \in Ballots: Conservative(i,b)

WellFormed == \A a \in Acceptors : \A i \in Instances : \A b \in Ballots :
    b > ballot[a] => vote[a][i][b] = None
       
VotedFor(a,i,b,v) == vote[a][i][b] = v

ChosenAt(i,b,v) ==
    \E Q \in Quorums : \A a \in Q : VotedFor(a,i,b,v)

Chosen(i,v) ==
    \E b \in Ballots : ChosenAt(i,b,v)

Choosable(v, i, b) ==
    \E Q \in Quorums : \A a \in Q : ballot[a] > b => vote[a][i][b] = v
    
SafeAt(v, i, b) ==
    \A b2 \in Ballots : \A v2 \in Values : 
        (b2 < b /\ Choosable(v2, i, b2))
        => v = v2
        
SafeInstanceVoteArray(i) == \A b \in Ballots : \A a \in Acceptors :
    LET v == vote[a][i][b]
    IN  v # None => SafeAt(v, i, b)

SafeVoteArray == \A i \in Instances : SafeInstanceVoteArray(i)

Inv == TypeOK /\ WellFormed /\ SafeVoteArray /\ ConservativeVoteArray

Correctness ==  
    \A i \in Instances : \A v1,v2 \in Values :
        Chosen(i, v1) /\ Chosen(i, v2) => v1 = v2 

=============================================================================
\* Modification History
\* Last modified Fri Jan 15 16:29:36 CST 2021 by Dell
\* Created Wed Jan 13 20:45:35 CST 2021 by Dell
