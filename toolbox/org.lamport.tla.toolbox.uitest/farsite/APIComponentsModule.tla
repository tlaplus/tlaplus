---- MODULE APIComponentsModule ----
(*`^\addcontentsline{toc}{section}{APIComponentsModule}^'*)

EXTENDS
  Stubs,Naturals,Sequences,AdditionalSequenceOperators,AdditionalMathOperators
CONSTANT Content

CONSTANT Label

CONSTANT Handle

CONSTANT Thread

(*Defn*)ThreadSet==SUBSET Thread

(*Defn*)HandleSet==SUBSET Handle

(*Defn*)LabelSet==SUBSET Label

(*Defn*)LabelOrNil==NilOr(Label)

ASSUME Nil \notin Content

ASSUME Nil \notin Label

ASSUME Nil \notin Handle

ASSUME Nil \notin Thread

CONSTANT ContentNull

CONSTANT RootHandle

ASSUME ContentNull \in Content

(*Defn*)LabelSeq==ArbSeq(Label)

CONSTANT LoadValue
====
