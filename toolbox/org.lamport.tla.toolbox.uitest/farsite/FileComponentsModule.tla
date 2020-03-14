---- MODULE FileComponentsModule ----
(*`^\addcontentsline{toc}{section}{FileComponentsModule}^'*)

EXTENDS Stubs,Sequences,AdditionalMathOperators
(*Defn*)FileIDComponent==PosInt

(*  As types go, "Nat" doesn't give us much of a hint for the implementation.  *)

CONSTANT FileID

(*Defn*)FileSet==SUBSET FileID

(*Defn*)FileSeq==ArbSeq(FileID)

(*Defn*)FileOrNil==NilOr(FileID)

ASSUME Nil \notin FileID

CONSTANT FilesystemRoot

ASSUME FilesystemRoot \in FileID
====
