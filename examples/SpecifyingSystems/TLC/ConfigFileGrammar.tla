------------------------- MODULE ConfigFileGrammar --------------------------
EXTENDS BNFGrammars
-----------------------------------------------------------------------------
Letter == OneOf("abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ")
Num    == OneOf("0123456789")
LetterOrNum == Letter \cup Num
AnyChar     == LetterOrNum \cup OneOf("~!@#\\$%^&*-+=|(){}[],:;`'<>.?/")
SingularKW  == {"SPECIFICATION", "INIT", "NEXT", "VIEW", "SYMMETRY"}
PluralKW == 
  {"CONSTRAINT", "CONSTRAINTS", "ACTION-CONSTRAINT", "ACTION-CONSTRAINTS", 
   "INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES"}
Keyword  == SingularKW \cup PluralKW \cup {"CONSTANT", "CONSTANTS"}
AnyIdent == LetterOrNum^* & Letter & LetterOrNum^*
Ident    == AnyIdent \ Keyword
-----------------------------------------------------------------------------
ConfigGrammar ==
  LET P(G) ==
        /\ G.File ::= G.Statement^+
        /\ G.Statement ::=   Tok(SingularKW) & Tok(Ident)
                           | Tok(PluralKW) & Tok(Ident)^*
                           |   Tok({"CONSTANT", "CONSTANTS"}) 
                             & (G.Replacement | G.Assignment)^*
        /\ G.Replacement ::= Tok(Ident) & tok("<-") & Tok(AnyIdent)
        /\ G.Assignment  ::= Tok(Ident) & tok("=") & G.IdentValue
        /\ G.IdentValue  ::=   
              Tok(AnyIdent) | G.Number | G.String
            |    tok("{") 
              &  (Nil | G.IdentValue & (tok(",") & G.IdentValue)^*)
              &  tok("}")
        /\ G.Number ::= (Nil | tok("-")) & Tok(Num^+)
        /\ G.String ::= tok("\"") & Tok(AnyChar^*) & tok("\"") 
   IN  LeastGrammar(P)
=============================================================================
