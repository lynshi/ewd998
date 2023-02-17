------------------------------- MODULE SmokeEWD998 -------------------------------
EXTENDS MCEWD998, TLC, Randomization

k ==
    10

\* SmokeInit is configured to re-define the initial predicate. We use  SmokeInit
\* to randomly select a subset of the defined initial states in cases when the
\* set of all initial states is too expensive to generate during smoke testing.
SmokeInit ==
    /\ pending \in RandomSubset(k, [Node -> 0..(N-1)])
    /\ counter \in RandomSubset(k, [Node -> -(N-1)..(N-1)])
    /\ active \in RandomSubset(k, [Node -> BOOLEAN])
    /\ color \in RandomSubset(k, [Node -> Color])
    /\ token \in RandomSubset(k, [pos: Node, q: Node, color: Color])
    /\ Inv \* Reject states with invalid ratio between counter, pending, ...

\* StopAfter  has to be configured as a state constraint. It stops TLC after ~1
\* second or after generating 100 traces, whatever comes first, unless TLC
\* encountered an error.  In this case,  StopAfter  has no relevance.
StopAfter ==
    TLCGet("config").mode = "simulate" =>
    (* The smoke test has a time budget of 1 second. *)
    \/ TLCSet("exit", TLCGet("duration") > 1)
    (* Generating 100 traces should provide reasonable coverage. *)
    \/ TLCSet("exit", TLCGet("diameter") > 100)

===============================================================================