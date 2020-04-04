---------------------------- MODULE DieHard ----------------------------
EXTENDS TLC, Integers

Min(m, n) == IF m < n THEN m ELSE n

NONDET == "nondet"
FILL_BIG == "fill big"
EMPTY_BIG == "empty big"
FILL_SMALL == "fill small"
EMPTY_SMALL == "empty small"
BIG_TO_SMALL == "pour big to small"
SMALL_TO_BIG == "pour small to big"

(***************************************************************************
--algorithm DieHardDemo {
    variables bigBucket = 0, smallBucket = 0, action = NONDET;
      
    process (FixWater = 1)
      variables water_to_pour = 0;
      {
        LB1: while (TRUE) 
          {
            either { action := FILL_BIG; bigBucket := 5; }
                or { action := EMPTY_BIG; bigBucket := 0; }
                or { action := FILL_SMALL; smallBucket := 3; } 
                or { action := EMPTY_SMALL; smallBucket := 0; } 
                or { 
                     action := BIG_TO_SMALL; 
                     water_to_pour := Min(3 - smallBucket, bigBucket); 
                     smallBucket := smallBucket + water_to_pour;
                     bigBucket := bigBucket - water_to_pour;
                   }
                or { 
                     action := SMALL_TO_BIG; 
                     water_to_pour := Min(5 - bigBucket, smallBucket); 
                     smallBucket := smallBucket - water_to_pour;
                     bigBucket := bigBucket + water_to_pour;
                   }
          }
      }
}

***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES bigBucket, smallBucket, action, water_to_pour

vars == << bigBucket, smallBucket, action, water_to_pour >>

ProcSet == {1}

Init == (* Global variables *)
        /\ bigBucket = 0
        /\ smallBucket = 0
        /\ action = NONDET
        (* Process FixWater *)
        /\ water_to_pour = 0

FixWater == \/ /\ action' = FILL_BIG
               /\ bigBucket' = 5
               /\ UNCHANGED <<smallBucket, water_to_pour>>
            \/ /\ action' = EMPTY_BIG
               /\ bigBucket' = 0
               /\ UNCHANGED <<smallBucket, water_to_pour>>
            \/ /\ action' = FILL_SMALL
               /\ smallBucket' = 3
               /\ UNCHANGED <<bigBucket, water_to_pour>>
            \/ /\ action' = EMPTY_SMALL
               /\ smallBucket' = 0
               /\ UNCHANGED <<bigBucket, water_to_pour>>
            \/ /\ action' = BIG_TO_SMALL
               /\ water_to_pour' = Min(3 - smallBucket, bigBucket)
               /\ smallBucket' = smallBucket + water_to_pour'
               /\ bigBucket' = bigBucket - water_to_pour'
            \/ /\ action' = SMALL_TO_BIG
               /\ water_to_pour' = Min(5 - bigBucket, smallBucket)
               /\ smallBucket' = smallBucket - water_to_pour'
               /\ bigBucket' = bigBucket + water_to_pour'

Next == FixWater

Spec == Init /\ [][Next]_vars

Inv == bigBucket # 4

\* END TRANSLATION

=============================================================================
