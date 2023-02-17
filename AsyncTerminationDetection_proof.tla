---------------------- MODULE AsyncTerminationDetection_proof ---------------------
EXTENDS AsyncTerminationDetection, TLAPS

(* Do not whitelist all the known facts/assumptions and definitions to speedup provers *)
\*USE NIsPosNat DEF vars, terminated, Node,
\*                  Init, Next, Spec,
\*                  DetectTermination, Terminate,
\*                  Wakeup, SendMsg,
\*                  TypeOK, Stable

\* * An invariant I is inductive, iff Init => I and I /\ [Next]_vars => I. Note
\* * though, that TypeOK itself won't imply  Stable  though!  TypeOK alone
\* * does not help us prove Stable.

LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK BY NIsPosNat DEF Init, TypeOK, Node, terminated
<1>2. TypeOK /\ [Next]_vars => TypeOK'
 <2> SUFFICES ASSUME TypeOK,
                     [Next]_vars
              PROVE  TypeOK'
   OBVIOUS
 <2>1. CASE DetectTermination
   BY <2>1 DEF TypeOK, Next, vars, DetectTermination
 <2>2. ASSUME NEW i \in Node,
              NEW j \in Node,
              Terminate(i)
       PROVE  TypeOK'
   BY <2>2 DEF TypeOK, Next, vars, Terminate, terminated
 <2>3. ASSUME NEW i \in Node,
              NEW j \in Node,
              Wakeup(i)
       PROVE  TypeOK'
   BY <2>3 DEF TypeOK, Next, vars, Wakeup
 <2>4. ASSUME NEW i \in Node,
              NEW j \in Node,
              SendMsg(i, j)
       PROVE  TypeOK'
   BY <2>4 DEF TypeOK, Next, vars, SendMsg
 <2>5. CASE UNCHANGED vars
   BY <2>5 DEF TypeOK, Next, vars
 <2>6. QED
   BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Proofs of safety and stability.                                         *)
(***************************************************************************)
Safe == terminationDetected => terminated

THEOREM Safety == Spec => []Safe
<1>. USE DEF terminated, TypeOK, Safe
<1>1. Init => Safe
  BY Zenon DEF Init
<1>2. TypeOK /\ Safe /\ [Next]_vars => Safe'
  <2> SUFFICES ASSUME TypeOK, Safe, [Next]_vars
               PROVE  Safe'
    OBVIOUS
  <2>1. CASE DetectTermination
    BY <2>1 DEF DetectTermination
  <2>2. ASSUME NEW i \in Node, Terminate(i)
        PROVE  Safe'
    BY <2>2, Zenon DEF Terminate
  <2>3. ASSUME NEW i \in Node, Wakeup(i)
        PROVE  Safe'
    BY <2>3 DEF Wakeup
  <2>4. ASSUME NEW i \in Node, NEW j \in Node, SendMsg(i, j)
        PROVE  Safe'
    BY <2>4 DEF SendMsg
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED
  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM Stability == Spec => Stable
\* We show that terminationDetected is never reset to FALSE
<1>1. TypeOK /\ Safe /\ terminationDetected /\ [Next]_vars => terminationDetected'
    BY Zenon
       DEF TypeOK, Safe, terminated, Next, DetectTermination, Terminate, Wakeup, SendMsg, vars
<1>. QED  BY <1>1, TypeCorrect, Safety, PTL DEF Spec, Stable, Safe

-----------------------------------------------------------------------------

\* syncActive == [n \in Node |-> active[n] \/ pending[n] # 0]

\* STD == INSTANCE SyncTerminationDetection WITH active <- syncActive

\* (***************************************************************************)
\* (* We prove (the safety part of) refinement.                               *)
\* (***************************************************************************)

\* THEOREM Refinement == Spec => STD!Spec
\* <1>. USE DEF Node, STD!Node, syncActive, terminated, STD!terminated
\* <1>1. Init => STD!Init
\*   BY NIsPosNat, Zenon DEF Init, STD!Init
\* <1>2. TypeOK /\ Safe /\ [Next]_vars => [STD!Next]_(STD!vars)
\*   <2> SUFFICES ASSUME TypeOK, Safe, [Next]_vars
\*                PROVE  [STD!Next]_(STD!vars)
\*     OBVIOUS
\*   <2>. USE NIsPosNat DEF TypeOK, STD!Next, STD!vars
\*   <2>1. CASE DetectTermination
\*     BY <2>1, Zenon DEF DetectTermination, STD!DetectTermination
\*   <2>2. ASSUME NEW i \in Node, Terminate(i)
\*         PROVE  [STD!Next]_(STD!vars)
\*     BY <2>2, Zenon DEF Terminate, STD!Terminate, Safe
\*   <2>3. ASSUME NEW i \in Node, Wakeup(i)
\*         PROVE  [STD!Next]_(STD!vars)
\*     BY <2>3 DEF Wakeup
\*   <2>4. ASSUME NEW i \in Node, NEW j \in Node, SendMsg(i, j)
\*         PROVE  [STD!Next]_(STD!vars)
\*     <3>1. syncActive[i] /\ UNCHANGED terminationDetected
\*       BY <2>4 DEF SendMsg
\*     <3>2. syncActive' = [syncActive EXCEPT ![j] = TRUE]
\*       BY <2>4, Isa DEF SendMsg
\*     <3>. QED  BY <3>1, <3>2, Zenon DEF STD!Wakeup
\*   <2>5. CASE UNCHANGED vars
\*     BY <2>5 DEF vars
\*   <2>6. QED
\*     BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
\* <1>3. Spec => WF_(STD!vars)(STD!DetectTermination)
\*   OMITTED
\* <1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, Safety, PTL DEF Spec, STD!Spec

=============================================================================
