---------------------------- MODULE BNFGrammars -----------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
-----------------------------------------------------------------------------
OneOf(s) == {<<s[i]>> : i \in DOMAIN s}
tok(s) == {<<s>>}
Tok(S) == {<<s>> : s \in S}
-----------------------------------------------------------------------------
Nil == {<< >>}
  
L & M   == {s \o t : s \in L, t \in M}
  
L | M   == L \cup M

L^+ == 
  LET LL[n \in Nat] == IF n = 0 THEN L 
                                ELSE LL[n-1] | (LL[n-1] & L)

  IN  UNION {LL[n] : n \in Nat}
  
L^* == Nil | L^+ 
-----------------------------------------------------------------------------
L ::= M == L = M

Grammar == [STRING -> SUBSET Seq(STRING)]

LeastGrammar(P(_)) ==
  CHOOSE G \in Grammar : /\ P(G) 
                         /\ \A H \in Grammar :
                              P(H) => \A s \in STRING : G[s] \subseteq H[s]
=============================================================================