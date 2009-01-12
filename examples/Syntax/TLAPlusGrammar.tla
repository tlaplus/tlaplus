--------------------------- MODULE TLAPlusGrammar --------------------------- 
EXTENDS Naturals, Sequences, BNFGrammars

CommaList(L) == L & (tok(",") &  L)^*
AtLeast4(s) == Tok({s \o s \o s} & {s}^+)

ReservedWord == 
  { "ASSUME",       "ELSE",      "LOCAL",      "UNION",     
   "ASSUMPTION",    "ENABLED",   "MODULE",     "VARIABLE",   
   "AXIOM",         "EXCEPT",    "OTHER",      "VARIABLES",  
   "CASE",          "EXTENDS",   "SF_",        "WF_",      
   "CHOOSE",        "IF",        "SUBSET",     "WITH", 
   "CONSTANT",      "IN",        "THEN",               
   "CONSTANTS" ,    "INSTANCE",  "THEOREM",       
   "DOMAIN",        "LET",       "UNCHANGED"   }

Letter == OneOf("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")
Numeral   == OneOf("0123456789") 
NameChar  == Letter \cup Numeral \cup {"_"}  

Name == Tok((NameChar^* & Letter & NameChar^*)  
                   \ ({"WF_","SF_"} & NameChar^+))


Identifier == Name \ Tok(ReservedWord)

IdentifierOrTuple  ==   
   Identifier | tok("<<") & CommaList(Identifier) & tok(">>")

NumberLexeme == 
         Numeral^+ 
      |  (Numeral^* & {"."} & Numeral^+) 
      |  {"\\b", "\\B"} & OneOf("01")^+ 
      |  {"\\o", "\\O"} & OneOf("01234567")^+ 
      |  {"\\h", "\\H"} & OneOf("0123456789abcdefABCDEF")^+ 

Number == Tok(NumberLexeme)

String == Tok({"\""} & STRING & {"\""})

PrefixOp  ==  Tok({ "-", "~", "\\lnot", "\\neg", "[]", "<>", "DOMAIN",  
                    "ENABLED", "SUBSET", "UNCHANGED", "UNION"})

InfixOp   ==
  Tok({  "!!",  "#",    "##",   "$",    "$$",   "%",    "%%",  
         "&",   "&&",   "(+)",  "(-)",  "(.)",  "(/)",  "(\\X)",  
         "*",   "**",   "+",    "++",   "-",    "-+->", "--",  
         "-|",  "..",   "...",  "/",    "//",   "/=",   "/\\",  
         "::=", ":=",   ":>",   "<",    "<:",   "<=>",  "=",  
         "=<",  "=>",   "=|",   ">",    ">=",   "?",    "??", 
         "@@",  "\\",    "\\/", "^",    "^^",   "|",    "|-",  
         "|=",  "||",   "~>",   ".",
         "\\approx",  "\\geq",       "\\oslash",     "\\sqsupseteq",
         "\\asymp",   "\\gg",        "\\otimes",     "\\star",     
         "\\bigcirc", "\\in",        "\\prec",       "\\subset",   
         "\\bullet",  "\\intersect", "\\preceq",     "\\subseteq", 
         "\\cap",     "\\land",      "\\propto",     "\\succ",     
         "\\cdot",    "\\leq",       "\\sim",        "\\succeq",   
         "\\circ",    "\\ll",        "\\simeq",      "\\supset",   
         "\\cong",    "\\lor",       "\\sqcap",      "\\supseteq", 
         "\\cup",     "\\o",         "\\sqcup",      "\\union",    
         "\\div",     "\\odot",      "\\sqsubset",   "\\uplus",    
         "\\doteq",   "\\ominus",    "\\sqsubseteq", "\\wr",      
         "\\equiv",   "\\oplus",     "\\sqsupset"                  })

PostfixOp ==  Tok({ "^+", "^*", "^#", "'" })

TLAPlusGrammar ==
 LET P(G) ==
   /\ G.Module ::=   AtLeast4("-") & tok("MODULE") & Name & AtLeast4("-")
                   & (Nil | (tok("EXTENDS") & CommaList(Name)))
                   & (G.Unit)^* 
                   & AtLeast4("=") 

   /\ G.Unit ::=   G.VariableDeclaration 
                 | G.ConstantDeclaration 
                 | (Nil | tok("LOCAL")) & G.OperatorDefinition 
                 | (Nil | tok("LOCAL")) & G.FunctionDefinition 
                 | (Nil | tok("LOCAL")) & G.Instance           
                 | (Nil | tok("LOCAL")) & G.ModuleDefinition  
                 | G.Assumption 
                 | G.Theorem 
                 | G.Module  
                 | AtLeast4("-") 

   /\ G.VariableDeclaration ::=  
          Tok({"VARIABLE", "VARIABLES"}) & CommaList(Identifier)

   /\ G.ConstantDeclaration ::=   
           Tok({"CONSTANT", "CONSTANTS"}) & CommaList(G.OpDecl)

   /\ G.OpDecl ::=    Identifier 
                    | Identifier & tok("(") & CommaList(tok("_")) & tok(")")
                    | PrefixOp & tok("_")
                    | tok("_") & InfixOp & tok("_")
                    | tok("_") & PostfixOp  

   /\  G.OperatorDefinition ::=  (  G.NonFixLHS 
                                  | PrefixOp & Identifier 
                                  | Identifier & InfixOp & Identifier 
                                  | Identifier & PostfixOp )
                                & tok("==") 
                                & G.Expression  

   /\ G.NonFixLHS ::=   
             Identifier 
          &  (  Nil 
              | tok("(") & CommaList(Identifier | G.OpDecl) & tok(")")) 

   /\ G.FunctionDefinition ::=   
          Identifier  
        & tok("[") & CommaList(G.QuantifierBound) & tok("]") 
        & tok("==") 
        & G.Expression  

   /\ G.QuantifierBound ::=   (IdentifierOrTuple | CommaList(Identifier))  
                            & tok("\\in") 
                            & G.Expression 

   /\ G.Instance ::=   tok("INSTANCE") 
                     & Name 
                     & (Nil | tok("WITH") & CommaList(G.Substitution))  

   /\ G.Substitution ::=   (Identifier | PrefixOp | InfixOp | PostfixOp) 
                         & tok("<-") 
                         & G.Argument  

   /\ G.Argument ::=   G.Expression  
                     | G.GeneralPrefixOp 
                     | G.GeneralInfixOp  
                     | G.GeneralPostfixOp  

   /\ G.InstancePrefix ::=  
        (    Identifier 
          &  (   Nil 
               | tok("(") & CommaList(G.Expression) & tok(")") )
          &  tok("!")  )^*  

   /\ G.GeneralIdentifier ::= G.InstancePrefix & Identifier 
   /\ G.GeneralPrefixOp   ::= G.InstancePrefix & PrefixOp 
   /\ G.GeneralInfixOp    ::= G.InstancePrefix & InfixOp
   /\ G.GeneralPostfixOp  ::= G.InstancePrefix & PostfixOp  

   /\ G.ModuleDefinition ::=   G.NonFixLHS & tok("==") & G.Instance  

   /\ G.Assumption ::=  
          Tok({"ASSUME", "ASSUMPTION", "AXIOM"}) & G.Expression  

   /\ G.Theorem ::= tok("THEOREM") & G.Expression  

   /\ G.Expression  ::= 
            G.GeneralIdentifier 

         |  G.GeneralIdentifier & tok("(") 
              & CommaList(G.Argument) &  tok(")") 

         |  G.GeneralPrefixOp & G.Expression 

         |  G.Expression & G.GeneralInfixOp & G.Expression 

         |  G.Expression & G.GeneralPostfixOp

         |  tok("(") & G.Expression & tok(")") 

         |  Tok({"\\A", "\\E"}) & CommaList(G.QuantifierBound) 
                & tok(":") & G.Expression 

         |  Tok({"\\A", "\\E", "\\AA", "\\EE"}) &  CommaList(Identifier) 
                & tok(":") & G.Expression 

        |     tok("CHOOSE") 
           &  IdentifierOrTuple 
           &  (Nil | tok("\\in") & G.Expression) 
           &  tok(":") 
           &  G.Expression 

        | tok("{") & (Nil | CommaList(G.Expression)) & tok("}") 

        |     tok("{") 
           &  IdentifierOrTuple & tok("\\in") & G.Expression 
           &  tok(":") 
           &  G.Expression 
           &  tok("}") 

        |     tok("{") 
           &  G.Expression  
           &  tok(":")  
           &  CommaList(G.QuantifierBound) 
           &  tok("}") 

        |  G.Expression & tok("[") & CommaList(G.Expression) & tok("]")

        |     tok("[") 
           &  CommaList(G.QuantifierBound)
           &  tok("|->")  
           &  G.Expression 
           &  tok("]") 

       |  tok("[") & G.Expression & tok("->") & G.Expression & tok("]") 

       |  tok("[") & CommaList(Name & tok("|->") & G.Expression) 
               & tok("]") 

       | tok("[") & CommaList(Name & tok(":") & G.Expression)  
              & tok("]") 

       |      tok("[") 
           &  G.Expression 
           &  tok("EXCEPT") 
           &  CommaList(  tok("!")
                        & (  tok(".") & Name 
                           | tok("[") & CommaList(G.Expression) & tok("]"))^+ 
                        & tok("=") & G.Expression ) 
           &  tok("]") 

      |  tok("<<") & CommaList(G.Expression) & tok(">>") 

      |  G.Expression & (Tok({"\\X", "\\times"}) & G.Expression)^+ 

      |  tok("[") & G.Expression & tok("]_") & G.Expression 

      |  tok("<<") & G.Expression & tok(">>_") & G.Expression 

      |  Tok({"WF_", "SF_"}) & G.Expression  
             & tok("(") & G.Expression & tok(")") 

      |  tok("IF") & G.Expression & tok("THEN")  
              & G.Expression & tok("ELSE") & G.Expression 

      |  tok("CASE") 
         &  ( LET CaseArm == 
                     G.Expression & tok("->") & G.Expression
              IN  CaseArm & (tok("[]") & CaseArm)^* )
         &  (    Nil 
              |  (tok("[]") & tok("OTHER") & tok("->") & G.Expression)) 

     |        tok("LET") 
           &  (    G.OperatorDefinition 
                |  G.FunctionDefinition 
                |  G.ModuleDefinition)^+ 
           &  tok("IN") 
           &  G.Expression

     |  (tok("/\\") & G.Expression)^+ 

     |  (tok("\\/") & G.Expression)^+ 

     |  Number 

     |  String 

     |  tok("@")

IN LeastGrammar(P)
=============================================================================