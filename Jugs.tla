---------------------- MODULE Jugs ---------------------

EXTENDS Naturals

CONSTANT SMALL_MAX
CONSTANT BIG_MAX
CONSTANT DESIRED

ASSUME SmallMaxIsNat == SMALL_MAX \in Nat \ {0}
ASSUME BigMaxIsNat == BIG_MAX \in Nat \ {0}
ASSUME SmallIsSmaller == SMALL_MAX <= BIG_MAX

ASSUME DesiredMaxIsNat == DESIRED \in Nat \ {0}
ASSUME DesiredMaxIsAchievable == DESIRED <= BIG_MAX

VARIABLE big, small

TypeOf ==
    /\ big \in 0..BIG_MAX
    /\ small \in 0..SMALL_MAX

gotDesired == 
    \/ small = DESIRED
    \/ big = DESIRED

Init ==
    /\ big = 0
    /\ small = 0

Min(a, b) == IF a < b THEN a ELSE b

BigToSmall ==
    /\ big > 0
    /\ big' = big - Min(SMALL_MAX - small, big)
    /\ small' = small + (big - big')

SmallToBig ==
    /\ small > 0
    /\ small' = small - Min(BIG_MAX - big, small)
    /\ big' = big + (small - small')

EmptySmall ==
    /\ small' = 0
    /\ UNCHANGED big

EmptyBig ==
    /\ big' = 0
    /\ UNCHANGED small

FillBig ==
    /\ big = 0
    /\ big' = BIG_MAX
    /\ UNCHANGED small

FillSmall ==
    /\ small = 0
    /\ small' = SMALL_MAX
    /\ UNCHANGED big

Next ==
    \/ BigToSmall
    \/ SmallToBig
    \/ EmptySmall
    \/ EmptyBig
    \/ FillBig
    \/ FillSmall

Inv ==
    /\ big # DESIRED
    /\ small # DESIRED

=============================================================================