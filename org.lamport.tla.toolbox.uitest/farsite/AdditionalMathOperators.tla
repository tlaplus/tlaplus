---- MODULE AdditionalMathOperators ----
(*`^\addcontentsline{toc}{section}{AdditionalMathOperators}^'*)

EXTENDS Naturals,Sequences,TLC
(*Defn*)NatSeq==ArbSeq(Nat)

(*Defn*)PosInt==Nat \ {0}

(*Defn*)PosIntSeq==ArbSeq(PosInt)

CONSTANT Nil

(*Defn*)NilSet=={Nil}

(*Defn*)NilOr(set)=={Nil}\union set

(*Defn*)SetHasMinElement(set,min)==
  /\ min \in set
  /\ (\A el \in set:min \leq el)

(*Defn*)SetHasMaxElement(set,max)==
  /\ max \in set
  /\ (\A el \in set:max \geq el)

(*Defn*)MinElement(set)==CHOOSE min \in set:(\A el \in set:min \leq el)

(*Defn*)MaxElement(set)==CHOOSE max \in set:(\A el \in set:max \geq el)
====
