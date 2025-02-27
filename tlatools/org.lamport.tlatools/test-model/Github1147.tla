---- MODULE Github1147 ----
EXTENDS FiniteSets, Naturals, TLC, TLCExt

Data == {"d1", "d2"}

VARIABLES state

Init == state = {}

Act(e,f,g) ==
	state' = state \union {<<e, f, g>>}

Next == 
	\E e \in Data: 
		\E f \in {1,2,3}:
			\E g \in [{0,1,2} -> {"a","b"}]: 
				Act(e,f,g)

Inv == Cardinality(state) < 2

Post ==
	CounterExample =
		[ state |->
		      { <<1, [state |-> {}]>>,
		        <<2, [state |-> {<<"d1", 1, (0 :> "a" @@ 1 :> "a" @@ 2 :> "a")>>}]>>,
		        << 3,
		           [ state |->
		                 { <<"d1", 1, (0 :> "a" @@ 1 :> "a" @@ 2 :> "a")>>,
		                   <<"d1", 1, (0 :> "a" @@ 1 :> "a" @@ 2 :> "b")>> } ] >> },
		  action |->
		      { << <<1, [state |-> {}]>>,
		           [ name |-> "Act",
		             location |->
		                 [ beginLine |-> 11,
		                   beginColumn |-> 9,
		                   endLine |-> 11,
		                   endColumn |-> 43,
		                   module |-> "Github1147" ],
		             context |->
		                 [ e |-> "d1",
		                   f |-> 1,
		                   g |-> (0 :> "a" @@ 1 :> "a" @@ 2 :> "a") ],
		             parameters |-> <<"e", "f", "g">> ],
		           << 2,
		              [ state |->
		                    {<<"d1", 1, (0 :> "a" @@ 1 :> "a" @@ 2 :> "a")>>} ] >> >>,
		        << <<2, [state |-> {<<"d1", 1, (0 :> "a" @@ 1 :> "a" @@ 2 :> "a")>>}]>>,
		           [ name |-> "Act",
		             location |->
		                 [ beginLine |-> 11,
		                   beginColumn |-> 9,
		                   endLine |-> 11,
		                   endColumn |-> 43,
		                   module |-> "Github1147" ],
		             context |->
		                 [ e |-> "d1",
		                   f |-> 1,
		                   g |-> (0 :> "a" @@ 1 :> "a" @@ 2 :> "b") ],
		             parameters |-> <<"e", "f", "g">> ],
		           << 3,
		              [ state |->
		                    { <<"d1", 1, (0 :> "a" @@ 1 :> "a" @@ 2 :> "a")>>,
		                      << "d1",
		                         1,
		                         (0 :> "a" @@ 1 :> "a" @@ 2 :> "b") >> } ] >> >> } ]
	
=============================================================================
