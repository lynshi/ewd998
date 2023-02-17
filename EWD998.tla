0) Sending a message by node  i  increments a counter at  i  , the receipt of a
   message decrements i's counter
3) Receiving a *message* (not token) blackens the (receiver) node
2) An active node j -owning the token- keeps the token.  When j becomes inactive,
   it passes the token to its neighbor with  q = q + counter[j] 
4) A black node taints the token
7) Passing the token whitens the sender node
1) The initiator sends the token with a counter  q  initialized to  0  and color
   white
5) The initiator starts a new round iff the current round is inconclusive
6) The initiator whitens itself and the token when initiating a new round

---------------------- MODULE EWD998 ---------------------
EXTENDS Naturals, Integers

CONSTANT N, MAX_PENDING_MESSAGES

ASSUME NIsPosNat == N \in Nat \ {0}
ASSUME MaxMsgsIsPosNat == MAX_PENDING_MESSAGES \in Nat \ {0}

Node == 0 .. N-1

White == "White"
Black == "Black"
Color == { White, Black }

VARIABLES active, network, counter, color, token
vars == <<active, network, counter, color, token >>

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> Nat ]
    /\ counter \in [ Node -> Int ]
    /\ color \in [ Node -> Color ]
    /\ token \in [ t: Node, color: Color, q: Int ]

terminationDetected ==
    /\ token["t"] = 0
    /\ active[0] = FALSE
    /\ counter[0] + token["q"] = 0
    /\ color[0] = White
    /\ token["color"] = White

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network = [ m \in Node |-> 0 ]
    /\ counter = [ m \in Node |-> 0 ]
    /\ color = [ m \in Node |-> White ]
    /\ token = [ t |-> 0, color |-> Black, q |-> 0 ]

StartProbe ==
    /\ ~terminationDetected
    /\ token["t"] = 0
    /\ token' = [ t |-> N - 1, color |-> White, q |-> 0 ]
    /\ color' = [ color EXCEPT ![0] = White ]
    /\ UNCHANGED << active, network, counter >>

\* EndProbe ==
\*     /\ token["t"] = 0
\*     /\ terminationDetected
\*     /\ UNCHANGED << active, network, counter, color, token >>

PassToken(n) ==
    /\ active[n] = FALSE
    /\ token["t"] = n
    /\ token["t"] # 0
    /\
        \/
            /\ color[n] = Black
            /\ token' = [ t |-> n - 1, color |-> Black, q |-> token["q"] + counter[n] ]
        \/
            /\ color[n] = White
            /\ token' = [ t |-> n - 1, color |-> token["color"], q |-> token["q"] + counter[n] ]
    /\ color' = [ color EXCEPT ![n] = White ]
    /\ UNCHANGED << active, network, counter >>

SendMsg(snd, rcv) ==
    /\ snd # rcv
    /\ active[snd]
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ counter' = [ counter EXCEPT ![snd] = @ + 1 ]
    /\ UNCHANGED << active, color, token >>

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ active' = [ active EXCEPT ![rcv] = TRUE]
    /\ network' = [ network EXCEPT ![rcv] = @ - 1 ]
    /\ counter' = [ counter EXCEPT ![rcv] = @ - 1 ]
    /\ color' = [ color EXCEPT ![rcv] = Black ]
    /\ UNCHANGED << token >>

Deactivate(n) ==
    /\ active[n] = TRUE
    /\ active' = [ active EXCEPT ![n] = FALSE]
    /\ UNCHANGED << network, counter, color, token >>

Next ==
    \/ StartProbe
    \* \/ EndProbe
    \/ \E n, m \in Node:
        \/ PassToken(n)
        \/ SendMsg(n, m)
        \/ Deactivate(n)
        \/ RecvMsg(m)

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety ==
\*     [](terminationDetected => []terminated)

\* Liveness ==
\*     /\ terminated ~> terminationDetected
    

ATD == INSTANCE AsyncTerminationDetection
    WITH pending <- network

ATDSpec == ATD!Spec


Sum(f, from, to) ==
    LET sum[ n \in from..to ] ==
        IF n = from THEN f[from]
        ELSE f[n] + sum[n - 1]
    IN sum[to]
    

IInv == 
    /\ Sum(network, 0, N - 1) = Sum(counter, 0, N - 1)
    /\
        \/
            /\ ~\E i \in Node: token.t < i /\ active[i] = TRUE
            /\ IF token.t # N - 1 THEN Sum(counter, token.t + 1, N - 1) = token.q ELSE token.q = 0
        \/ Sum(counter, 0, token.t) + token.q > 0
        \/ \E i \in Node: 0 \leq i /\ i \leq token.t /\ color[i] = Black
        \/ token.color = Black

\* IInvSpec ==
\*     IInv /\ [][Next]_vars => IInv'

---------------------------------------------------------------------------

\* Below this line this is just TLC related.

MaxPendingMessages ==
    /\ \A n \in Node : network[n] < MAX_PENDING_MESSAGES
    /\ \A n \in Node : counter[n] < MAX_PENDING_MESSAGES
=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl