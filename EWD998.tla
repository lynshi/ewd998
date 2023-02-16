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

VARIABLES active, network, counter, color, token, terminationDetected
vars == <<active, network, counter, color, token, terminationDetected>>

terminated ==
    /\ token["t"] = 0
    /\ active[0] = FALSE
    /\ counter[0] + token["q"] = 0
    /\ color[0] = White
    /\ token["color"] = White

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> Nat ]
    /\ counter \in [ Node -> Int ]
    /\ color \in [ Node -> Color ]
    /\ token \in [ t: Node, color: Color, q: Int ]
    /\ terminationDetected \in BOOLEAN 

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network = [ m \in Node |-> 0 ]
    /\ counter = [ m \in Node |-> 0 ]
    /\ color = [ m \in Node |-> White ]
    /\ token = [ t |-> 0, color |-> White, q |-> 0 ]
    /\ terminationDetected \in { FALSE, terminated }

StartProbe ==
    /\ ~terminationDetected
    /\ ~terminated
    /\ token["t"] = 0
    /\ token' = [ t |-> N - 1, color |-> White, q |-> 0 ]
    /\ color' = [ color EXCEPT ![0] = White ]
    /\ UNCHANGED << active, network, counter, terminationDetected >>

EndProbe ==
    /\ token["t"] = 0
    /\ terminated
    /\ terminationDetected' = terminated
    /\ UNCHANGED << active, network, counter, color, token >>

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
    /\ UNCHANGED << active, network, counter, terminationDetected >>

SendMsg(snd, rcv) ==
    /\ snd # rcv
    /\ active[snd]
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ counter' = [ counter EXCEPT ![snd] = @ + 1 ]
    /\ UNCHANGED << active, color, token, terminationDetected >>

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ active' = [ active EXCEPT ![rcv] = TRUE]
    /\ network' = [ network EXCEPT ![rcv] = @ - 1 ]
    /\ counter' = [ counter EXCEPT ![rcv] = @ - 1 ]
    /\ color' = [ color EXCEPT ![rcv] = Black ]
    /\ UNCHANGED << token, terminationDetected >>

Deactivate(n) ==
    /\ active[n] = TRUE
    /\ active' = [ active EXCEPT ![n] = FALSE]
    /\ UNCHANGED << network, counter, color, token, terminationDetected >>

Next ==
    \/ StartProbe
    \/ EndProbe
    \/ \E n, m \in Node:
        \/ PassToken(n)
        \/ SendMsg(n, m)
        \/ Deactivate(n)
        \/ RecvMsg(m)

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

Safety ==
    [](terminationDetected => []terminated)

Liveness ==
    terminated ~> terminationDetected
    

---------------------------------------------------------------------------

\* Below this line this is just TLC related.

MaxPendingMessages ==
    \A n \in Node : network[n] < MAX_PENDING_MESSAGES
=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl