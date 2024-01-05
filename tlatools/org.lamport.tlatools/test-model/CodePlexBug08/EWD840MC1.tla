---- MODULE EWD840MC1 ----
EXTENDS EWD840, TLC, TLCExt

const_123 == 4

PostCondition ==
	/\ TLCSet(42, TLCGet("generated"))
	/\ \/ CounterExample = [ action |-> {} , state |-> {} ]
	   \/ /\ ToTrace(CounterExample) = 
				<< [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white"),
				     tpos |-> 0,
				     tcolor |-> "black" ],
				   [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "white" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
				     tpos |-> 3,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
				     tpos |-> 2,
				     tcolor |-> "white" ],
				   [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "white" @@ 3 :> "white"),
				     tpos |-> 1,
				     tcolor |-> "black" ],
				   [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "white" @@ 3 :> "white"),
				     tpos |-> 1,
				     tcolor |-> "black" ],
				   [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
				     color |-> (0 :> "white" @@ 1 :> "black" @@ 2 :> "white" @@ 3 :> "white"),
				     tpos |-> 1,
				     tcolor |-> "black" ] >>
	      /\ CounterExample =
			[ action |->
		      { << << 1,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "white" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 0,
		                tcolor |-> "black" ] >>,
		           [ name |-> "InitiateProbe",
		             location |->
		                 [ beginLine |-> 30,
		                   beginColumn |-> 3,
		                   endLine |-> 35,
		                   endColumn |-> 43,
		                   module |-> "EWD840" ] ],
		           << 2,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "white" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 2,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "white" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "SendMsg",
		             location |->
		                 [ beginLine |-> 61,
		                   beginColumn |-> 3,
		                   endLine |-> 65,
		                   endColumn |-> 31,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 3] ],
		           << 3,
		              [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "white" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 3,
		              [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "white" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "SendMsg",
		             location |->
		                 [ beginLine |-> 61,
		                   beginColumn |-> 3,
		                   endLine |-> 65,
		                   endColumn |-> 31,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 2] ],
		           << 4,
		              [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "white" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 4,
		              [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "white" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "SendMsg",
		             location |->
		                 [ beginLine |-> 61,
		                   beginColumn |-> 3,
		                   endLine |-> 65,
		                   endColumn |-> 31,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 1] ],
		           << 5,
		              [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "white" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 5,
		              [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "white" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "SendMsg",
		             location |->
		                 [ beginLine |-> 61,
		                   beginColumn |-> 3,
		                   endLine |-> 65,
		                   endColumn |-> 31,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 1] ],
		           << 6,
		              [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 6,
		              [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "SendMsg",
		             location |->
		                 [ beginLine |-> 61,
		                   beginColumn |-> 3,
		                   endLine |-> 65,
		                   endColumn |-> 31,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 2] ],
		           << 7,
		              [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 7,
		              [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "Deactivate",
		             location |->
		                 [ beginLine |-> 69,
		                   beginColumn |-> 3,
		                   endLine |-> 71,
		                   endColumn |-> 38,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 0] ],
		           << 8,
		              [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 8,
		              [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "Deactivate",
		             location |->
		                 [ beginLine |-> 69,
		                   beginColumn |-> 3,
		                   endLine |-> 71,
		                   endColumn |-> 38,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 1] ],
		           << 9,
		              [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 9,
		              [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "SendMsg",
		             location |->
		                 [ beginLine |-> 61,
		                   beginColumn |-> 3,
		                   endLine |-> 65,
		                   endColumn |-> 31,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 2] ],
		           << 10,
		              [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 10,
		              [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "Deactivate",
		             location |->
		                 [ beginLine |-> 69,
		                   beginColumn |-> 3,
		                   endLine |-> 71,
		                   endColumn |-> 38,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 2] ],
		           << 11,
		              [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 11,
		              [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "Deactivate",
		             location |->
		                 [ beginLine |-> 69,
		                   beginColumn |-> 3,
		                   endLine |-> 71,
		                   endColumn |-> 38,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 3] ],
		           << 12,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >> >>,
		        << << 12,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 3,
		                tcolor |-> "white" ] >>,
		           [ name |-> "PassToken",
		             location |->
		                 [ beginLine |-> 47,
		                   beginColumn |-> 3,
		                   endLine |-> 52,
		                   endColumn |-> 43,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 3] ],
		           << 13,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 2,
		                tcolor |-> "white" ] >> >>,
		        << << 13,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "black" @@
		                      3 :> "white" ),
		                tpos |-> 2,
		                tcolor |-> "white" ] >>,
		           [ name |-> "PassToken",
		             location |->
		                 [ beginLine |-> 47,
		                   beginColumn |-> 3,
		                   endLine |-> 52,
		                   endColumn |-> 43,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 2] ],
		           << 14,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 1,
		                tcolor |-> "black" ] >> >>,
		        << << 14,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 1,
		                tcolor |-> "black" ] >>,
		           [ name |-> "SendMsg",
		             location |->
		                 [ beginLine |-> 61,
		                   beginColumn |-> 3,
		                   endLine |-> 65,
		                   endColumn |-> 31,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 1] ],
		           << 15,
		              [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 1,
		                tcolor |-> "black" ] >> >>,
		        << << 15,
		              [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 1,
		                tcolor |-> "black" ] >>,
		           [ name |-> "Deactivate",
		             location |->
		                 [ beginLine |-> 69,
		                   beginColumn |-> 3,
		                   endLine |-> 71,
		                   endColumn |-> 38,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 1] ],
		           << 16,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 1,
		                tcolor |-> "black" ] >> >>,
		        << << 16,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "black" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 1,
		                tcolor |-> "black" ] >>,
		           [ name |-> "PassToken",
		             location |->
		                 [ beginLine |-> 47,
		                   beginColumn |-> 3,
		                   endLine |-> 52,
		                   endColumn |-> 43,
		                   module |-> "EWD840" ],
		             context |-> [i |-> 1] ],
		           << 1,
		              [ active |->
		                    (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
		                color |->
		                    ( 0 :> "white" @@
		                      1 :> "white" @@
		                      2 :> "white" @@
		                      3 :> "white" ),
		                tpos |-> 0,
		                tcolor |-> "black" ] >> >> },
			  state |->
			      { << 1,
			           [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white"),
			             tpos |-> 0,
			             tcolor |-> "black" ] >>,
			        << 2,
			           [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 3,
			           [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 4,
			           [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 5,
			           [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 6,
			           [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "white" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 7,
			           [ active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 8,
			           [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 9,
			           [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 10,
			           [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 11,
			           [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 12,
			           [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
			             tpos |-> 3,
			             tcolor |-> "white" ] >>,
			        << 13,
			           [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "black" @@ 3 :> "white"),
			             tpos |-> 2,
			             tcolor |-> "white" ] >>,
			        << 14,
			           [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "white" @@ 3 :> "white"),
			             tpos |-> 1,
			             tcolor |-> "black" ] >>,
			        << 15,
			           [ active |-> (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "white" @@ 3 :> "white"),
			             tpos |-> 1,
			             tcolor |-> "black" ] >>,
			        << 16,
			           [ active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE),
			             color |->
			                 (0 :> "white" @@ 1 :> "black" @@ 2 :> "white" @@ 3 :> "white"),
			             tpos |-> 1,
			             tcolor |-> "black" ] >> } ]
			
===================