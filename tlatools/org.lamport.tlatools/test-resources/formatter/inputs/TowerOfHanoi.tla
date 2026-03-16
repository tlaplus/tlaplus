------------------------------- MODULE TowerOfHanoi -------------------------------
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two                                            *)
(***************************************************************************)
PowerOfTwo(i) == i & (i-1) = 0

(***************************************************************************)
(* A set of all powers of two up to n                                      *)
(***************************************************************************)
SetOfPowerOfTwo(n) == {x \in 1..(2^n-1): PowerOfTwo(x)}

(***************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in  *)
(* DOMAIN f.                                                               *)
(***************************************************************************)
Sum(f) == LET DSum[S \in SUBSET DOMAIN f] ==
               LET elt == CHOOSE e \in S : TRUE
               IN  IF S = {} THEN 0
                             ELSE f[elt] + DSum[S \ {elt}]
          IN  DSum[DOMAIN f]

(***************************************************************************)
(* D is number of disks and N number of towers                             *)
(***************************************************************************)
CONSTANT D, N

(***************************************************************************)
(* Towers of Hanoi with N towers                                           *)
(***************************************************************************)
VARIABLES towers
vars == <<towers>>

(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system      *)
(***************************************************************************)
Inv == Sum(towers) = 2^D - 1

(* Towers are naturals in the interval (0, 2^D] *)
TypeOK == /\ \A i \in DOMAIN towers : /\ towers[i] \in Nat \* Towers are represented by natural numbers
                                      /\ towers[i] < 2^D

(***************************************************************************)
(* Now we define of the initial predicate, that specifies the initial      *)
(* values of the variables.                                                *)
(***************************************************************************)
Init == /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0] \* all towers are empty except all disks are on the first Tower

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff the disk is located on the given tower                         *)
(***************************************************************************)
IsOnTower(tower, disk) == /\ tower & disk = disk

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower                             *)
(***************************************************************************)
IsSmallestDisk(tower, disk) == /\ IsOnTower(tower, disk)
                               /\ tower & (disk - 1) = 0 \* All less significant bits are 0

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                 *)
(***************************************************************************)
CanMoveOff(tower, disk) == /\ IsOnTower(tower, disk)
                           /\ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                 *)
(***************************************************************************)
CanMoveTo(tower, disk) == \/ tower & (disk - 1) = 0
                          \/ IsEmptyTower(tower)

(***************************************************************************)
(*                                                                         *)
(***************************************************************************)
Move(from, to, disk) == /\ CanMoveOff(towers[from], disk)
                        /\ CanMoveTo(towers[to], disk)
                        /\ towers' = [towers EXCEPT ![from] = towers[from] - disk,  \* Remaining tower does not change
                                                    ![to] = towers[to] + disk]

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
Next == \E d \in SetOfPowerOfTwo(D): \E idx1, idx2 \in DOMAIN towers:
            /\ idx1 # idx2 \* No need to try to move onto the same tower (Move(...) prevents it too)
            /\ Move(idx1, idx2, d)

=============================================================================
\* Modification History
\* Last modified Tue May 17 14:55:33 CEST 2016 by markus
\* Created Sun Jul 17 10:20:57 CEST 2011 by markus