------------------------------ MODULE ACP_NB_TLC -------------------------------

\* ACP_SB, TLC ready

EXTENDS ACP_NB, TLC, TLCExt

Perms == Permutations(participants) \* to benefit from symmetries

--------------------------------------------------------------------------------

\* AC4 rewritten in a way that is better handled by TLC

AC4_alt == [][ /\ (\A i \in participants : participant[i].decision = commit 
                                => (participant'[i].decision = commit))
               /\ (\A j \in participants : participant[j].decision = abort  
                                => (participant'[j].decision = abort))]_<<participant>>

AllMustCommit == \A p \in participants : <>(participant[p].decision = commit)

CONSTANTS p0, p1

PostCondition ==
   CounterExample = 
    [ action |->
      { << << 1,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> waiting @@ p1 :> waiting),
                      alive |-> TRUE,
                      faulty |-> FALSE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> FALSE @@ p1 :> FALSE) ] ] >>,
           [ name |-> "request",
             location |->
                 [ beginLine |-> 100,
                   beginColumn |-> 15,
                   endLine |-> 105,
                   endColumn |-> 41,
                   module |-> "ACP_SB" ],
             context |-> [i |-> p0],
             parameters |-> <<"i">> ],
           << 2,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> waiting @@ p1 :> waiting),
                      alive |-> TRUE,
                      faulty |-> FALSE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> FALSE) ] ] >> >>,
        << << 2,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> waiting @@ p1 :> waiting),
                      alive |-> TRUE,
                      faulty |-> FALSE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> FALSE) ] ] >>,
           [ name |-> "sendVote",
             location |->
                 [ beginLine |-> 211,
                   beginColumn |-> 16,
                   endLine |-> 216,
                   endColumn |-> 42,
                   module |-> "ACP_SB" ],
             context |-> [i |-> p0],
             parameters |-> <<"i">> ],
           << 3,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> waiting @@ p1 :> waiting),
                      alive |-> TRUE,
                      faulty |-> FALSE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> FALSE) ] ] >> >>,
        << << 3,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> waiting @@ p1 :> waiting),
                      alive |-> TRUE,
                      faulty |-> FALSE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> FALSE) ] ] >>,
           [ name |-> "request",
             location |->
                 [ beginLine |-> 100,
                   beginColumn |-> 15,
                   endLine |-> 105,
                   endColumn |-> 41,
                   module |-> "ACP_SB" ],
             context |-> [i |-> p1],
             parameters |-> <<"i">> ],
           << 4,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> waiting @@ p1 :> waiting),
                      alive |-> TRUE,
                      faulty |-> FALSE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >> >>,
        << << 4,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> waiting @@ p1 :> waiting),
                      alive |-> TRUE,
                      faulty |-> FALSE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >>,
           [ name |-> "getVote",
             location |->
                 [ beginLine |-> 118,
                   beginColumn |-> 15,
                   endLine |-> 126,
                   endColumn |-> 41,
                   module |-> "ACP_SB" ],
             context |-> [i |-> p0],
             parameters |-> <<"i">> ],
           << 5,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> yes @@ p1 :> waiting),
                      alive |-> TRUE,
                      faulty |-> FALSE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >> >>,
        << << 5,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> yes @@ p1 :> waiting),
                      alive |-> TRUE,
                      faulty |-> FALSE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >>,
           [ name |-> "coordDie",
             location |->
                 [ beginLine |-> 196,
                   beginColumn |-> 13,
                   endLine |-> 198,
                   endColumn |-> 39,
                   module |-> "ACP_SB" ] ],
           << 6,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> yes @@ p1 :> waiting),
                      alive |-> FALSE,
                      faulty |-> TRUE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >> >>,
        << << 6,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> yes @@ p1 :> waiting),
                      alive |-> FALSE,
                      faulty |-> TRUE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >>,
           [ name |-> "parDie",
             location |->
                 [ beginLine |-> 280,
                   beginColumn |-> 14,
                   endLine |-> 284,
                   endColumn |-> 40,
                   module |-> "ACP_SB" ],
             context |-> [i |-> p0],
             parameters |-> <<"i">> ],
           << 7,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> FALSE,
                            faulty |-> TRUE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> yes @@ p1 :> waiting),
                      alive |-> FALSE,
                      faulty |-> TRUE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >> >>,
        << << 7,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> FALSE,
                            faulty |-> TRUE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> TRUE,
                            faulty |-> FALSE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> yes @@ p1 :> waiting),
                      alive |-> FALSE,
                      faulty |-> TRUE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >>,
           [ name |-> "parDie",
             location |->
                 [ beginLine |-> 280,
                   beginColumn |-> 14,
                   endLine |-> 284,
                   endColumn |-> 40,
                   module |-> "ACP_SB" ],
             context |-> [i |-> p1],
             parameters |-> <<"i">> ],
           << 8,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> FALSE,
                            faulty |-> TRUE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> FALSE,
                            faulty |-> TRUE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> yes @@ p1 :> waiting),
                      alive |-> FALSE,
                      faulty |-> TRUE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >> >>,
        << << 8,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> FALSE,
                            faulty |-> TRUE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> FALSE,
                            faulty |-> TRUE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> yes @@ p1 :> waiting),
                      alive |-> FALSE,
                      faulty |-> TRUE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >>,
           [ name |-> "parDie",
             location |->
                 [ beginLine |-> 280,
                   beginColumn |-> 14,
                   endLine |-> 284,
                   endColumn |-> 40,
                   module |-> "ACP_SB" ],
             context |-> [i |-> p1],
             parameters |-> <<"i">> ],
           << 8,
              [ participant |->
                    ( p0 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> FALSE,
                            faulty |-> TRUE,
                            voteSent |-> TRUE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                      p1 :>
                          [ decision |-> undecided,
                            vote |-> yes,
                            alive |-> FALSE,
                            faulty |-> TRUE,
                            voteSent |-> FALSE,
                            forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
                coordinator |->
                    [ decision |-> undecided,
                      vote |-> (p0 :> yes @@ p1 :> waiting),
                      alive |-> FALSE,
                      faulty |-> TRUE,
                      broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                      request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >> >> },
  state |->
      { << 1,
           [ participant |->
                 ( p0 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> FALSE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                   p1 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> FALSE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
             coordinator |->
                 [ decision |-> undecided,
                   vote |-> (p0 :> waiting @@ p1 :> waiting),
                   alive |-> TRUE,
                   faulty |-> FALSE,
                   broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                   request |-> (p0 :> FALSE @@ p1 :> FALSE) ] ] >>,
        << 2,
           [ participant |->
                 ( p0 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> FALSE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                   p1 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> FALSE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
             coordinator |->
                 [ decision |-> undecided,
                   vote |-> (p0 :> waiting @@ p1 :> waiting),
                   alive |-> TRUE,
                   faulty |-> FALSE,
                   broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                   request |-> (p0 :> TRUE @@ p1 :> FALSE) ] ] >>,
        << 3,
           [ participant |->
                 ( p0 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> TRUE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                   p1 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> FALSE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
             coordinator |->
                 [ decision |-> undecided,
                   vote |-> (p0 :> waiting @@ p1 :> waiting),
                   alive |-> TRUE,
                   faulty |-> FALSE,
                   broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                   request |-> (p0 :> TRUE @@ p1 :> FALSE) ] ] >>,
        << 4,
           [ participant |->
                 ( p0 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> TRUE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                   p1 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> FALSE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
             coordinator |->
                 [ decision |-> undecided,
                   vote |-> (p0 :> waiting @@ p1 :> waiting),
                   alive |-> TRUE,
                   faulty |-> FALSE,
                   broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                   request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >>,
        << 5,
           [ participant |->
                 ( p0 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> TRUE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                   p1 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> FALSE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
             coordinator |->
                 [ decision |-> undecided,
                   vote |-> (p0 :> yes @@ p1 :> waiting),
                   alive |-> TRUE,
                   faulty |-> FALSE,
                   broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                   request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >>,
        << 6,
           [ participant |->
                 ( p0 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> TRUE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                   p1 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> FALSE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
             coordinator |->
                 [ decision |-> undecided,
                   vote |-> (p0 :> yes @@ p1 :> waiting),
                   alive |-> FALSE,
                   faulty |-> TRUE,
                   broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                   request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >>,
        << 7,
           [ participant |->
                 ( p0 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> FALSE,
                         faulty |-> TRUE,
                         voteSent |-> TRUE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                   p1 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> TRUE,
                         faulty |-> FALSE,
                         voteSent |-> FALSE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
             coordinator |->
                 [ decision |-> undecided,
                   vote |-> (p0 :> yes @@ p1 :> waiting),
                   alive |-> FALSE,
                   faulty |-> TRUE,
                   broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                   request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >>,
        << 8,
           [ participant |->
                 ( p0 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> FALSE,
                         faulty |-> TRUE,
                         voteSent |-> TRUE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] @@
                   p1 :>
                       [ decision |-> undecided,
                         vote |-> yes,
                         alive |-> FALSE,
                         faulty |-> TRUE,
                         voteSent |-> FALSE,
                         forward |-> (p0 :> notsent @@ p1 :> notsent) ] ),
             coordinator |->
                 [ decision |-> undecided,
                   vote |-> (p0 :> yes @@ p1 :> waiting),
                   alive |-> FALSE,
                   faulty |-> TRUE,
                   broadcast |-> (p0 :> notsent @@ p1 :> notsent),
                   request |-> (p0 :> TRUE @@ p1 :> TRUE) ] ] >> } ]

================================================================================
