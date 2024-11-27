--------------------------- MODULE ViewMap ---------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC, TLCExt

CONSTANT P, \* Set of Producers
         C, \* Set of Consumers
         K  \* Capacity of buffer/queue 

RemoveLast(seq) == [ i \in 1..(Len(seq) - 1) |-> seq[i] ]

(*
--algorithm JBuffer01Pcal {
   variables buffer = <<>>, waitset = {};

   process (p \in P) {
      lbp: while (Len(buffer) >= K) {
               (* wait *)
               waitset := waitset \cup {self};
          };
          buffer := Append(buffer, "d");
          (* notify *)
          if (waitset # {}) {
            with (x \in waitset) {
              waitset := waitset \ {x};
            }
          };
          goto lbp;
   }

   process (c \in C) {
      lbc:  while (Len(buffer) = 0) {
               (* wait *)
               waitset := waitset \cup {self};
          };
          buffer := RemoveLast(buffer);
          (* notify *)
          if (waitset # {}) {
            with (x \in waitset) {
              waitset := waitset \ {x};
            }
          };
          goto lbc;
   }
}
*)
\* BEGIN TRANSLATION
VARIABLES buffer, waitset, pc

vars == << buffer, waitset, pc >>

ProcSet == (P) \cup (C)

Init == (* Global variables *)
        /\ buffer = <<>>
        /\ waitset = {}
        /\ pc = [self \in ProcSet |-> CASE self \in P -> "lbp"
                                        [] self \in C -> "lbc"]

lbp(self) == /\ pc[self] = "lbp"
             /\ IF Len(buffer) >= K
                   THEN /\ waitset' = (waitset \cup {self})
                        /\ pc' = [pc EXCEPT ![self] = "lbp"]
                        /\ UNCHANGED buffer
                   ELSE /\ buffer' = Append(buffer, "d")
                        /\ IF waitset # {}
                              THEN /\ \E x \in waitset:
                                        waitset' = waitset \ {x}
                              ELSE /\ TRUE
                                   /\ UNCHANGED waitset
                        /\ pc' = [pc EXCEPT ![self] = "lbp"]

p(self) == lbp(self)

lbc(self) == /\ pc[self] = "lbc"
             /\ IF Len(buffer) = 0
                   THEN /\ waitset' = (waitset \cup {self})
                        /\ pc' = [pc EXCEPT ![self] = "lbc"]
                        /\ UNCHANGED buffer
                   ELSE /\ buffer' = RemoveLast(buffer)
                        /\ IF waitset # {}
                              THEN /\ \E x \in waitset:
                                        waitset' = waitset \ {x}
                              ELSE /\ TRUE
                                   /\ UNCHANGED waitset
                        /\ pc' = [pc EXCEPT ![self] = "lbc"]

c(self) == lbc(self)

Next == (\E self \in P: p(self))
           \/ (\E self \in C: c(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Inv == waitset # ProcSet

view == <<buffer, waitset>>

CONSTANTS c1, c2, p1

PostCondition ==
	/\ TLCSet(42, TLCGet("generated"))
	/\ CounterExample =
		[ state |->
		      { << 1,
		           [ buffer |-> <<>>,
		             waitset |-> {},
		             pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
		        << 2,
		           [ buffer |-> <<>>,
		             waitset |-> {c1},
		             pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
		        << 3,
		           [ buffer |-> <<>>,
		             waitset |-> {c1, c2},
		             pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
		        << 4,
		           [ buffer |-> <<"d">>,
		             waitset |-> {c2},
		             pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
		        << 5,
		           [ buffer |-> <<"d">>,
		             waitset |-> {c2, p1},
		             pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
		        << 6,
		           [ buffer |-> << >>,
		             waitset |-> {p1},
		             pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
		        << 7,
		           [ buffer |-> << >>,
		             waitset |-> {c1, p1},
		             pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
		        << 8,
		           [ buffer |-> << >>,
		             waitset |-> {c1, c2, p1},
		             pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >> },
		  action |->
				{ << << 1,
				        [ buffer |-> <<>>,
				          waitset |-> {},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
				     [ name |-> "lbc",
				       context |-> [self |-> c1],
				       location |->
				           [ beginLine |-> 73,
				             beginColumn |-> 14,
				             endLine |-> 84,
				             endColumn |-> 60,
				             module |-> "ViewMap" ],
				       parameters |-> <<"self">> ],
				     << 2,
				        [ buffer |-> <<>>,
				          waitset |-> {c1},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >> >>,
				  << << 2,
				        [ buffer |-> <<>>,
				          waitset |-> {c1},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
				     [ name |-> "lbc",
				       context |-> [self |-> c2],
				       location |->
				           [ beginLine |-> 73,
				             beginColumn |-> 14,
				             endLine |-> 84,
				             endColumn |-> 60,
				             module |-> "ViewMap" ],
				       parameters |-> <<"self">> ],
				     << 3,
				        [ buffer |-> <<>>,
				          waitset |-> {c1, c2},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >> >>,
				  << << 3,
				        [ buffer |-> <<>>,
				          waitset |-> {c1, c2},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
				     [ name |-> "lbp",
				       context |-> [self |-> p1],
				       location |->
				           [ beginLine |-> 58,
				             beginColumn |-> 14,
				             endLine |-> 69,
				             endColumn |-> 60,
				             module |-> "ViewMap" ],
				       parameters |-> <<"self">> ],
				     << 4,
				        [ buffer |-> <<"d">>,
				          waitset |-> {c2},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >> >>,
				  << << 4,
				        [ buffer |-> <<"d">>,
				          waitset |-> {c2},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
				     [ name |-> "lbp",
				       context |-> [self |-> p1],
				       location |->
				           [ beginLine |-> 58,
				             beginColumn |-> 14,
				             endLine |-> 69,
				             endColumn |-> 60,
				             module |-> "ViewMap" ],
				       parameters |-> <<"self">> ],
				     << 5,
				        [ buffer |-> <<"d">>,
				          waitset |-> {c2, p1},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >> >>,
				  << << 5,
				        [ buffer |-> <<"d">>,
				          waitset |-> {c2, p1},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
				     [ name |-> "lbc",
				       context |-> [self |-> c1],
				       location |->
				           [ beginLine |-> 73,
				             beginColumn |-> 14,
				             endLine |-> 84,
				             endColumn |-> 60,
				             module |-> "ViewMap" ],
				       parameters |-> <<"self">> ],
				     << 6,
				        [ buffer |-> <<>>,
				          waitset |-> {p1},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >> >>,
				  << << 6,
				        [ buffer |-> <<>>,
				          waitset |-> {p1},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
				     [ name |-> "lbc",
				       context |-> [self |-> c1],
				       location |->
				           [ beginLine |-> 73,
				             beginColumn |-> 14,
				             endLine |-> 84,
				             endColumn |-> 60,
				             module |-> "ViewMap" ],
				       parameters |-> <<"self">> ],
				     << 7,
				        [ buffer |-> <<>>,
				          waitset |-> {c1, p1},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >> >>,
				  << << 7,
				        [ buffer |-> <<>>,
				          waitset |-> {c1, p1},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >>,
				     [ name |-> "lbc",
				       context |-> [self |-> c2],
				       location |->
				           [ beginLine |-> 73,
				             beginColumn |-> 14,
				             endLine |-> 84,
				             endColumn |-> 60,
				             module |-> "ViewMap" ],
				       parameters |-> <<"self">> ],
				     << 8,
				        [ buffer |-> <<>>,
				          waitset |-> {c1, c2, p1},
				          pc |-> (c1 :> "lbc" @@ c2 :> "lbc" @@ p1 :> "lbp") ] >> >> } ]
	
=============================================================================
