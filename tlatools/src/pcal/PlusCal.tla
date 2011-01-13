last modified on Wed 22 Aug 2007 at 16:24:25 PST by lamport
 
------------------------------- MODULE PlusCal ------------------------------
(***************************************************************************)
(* Compiling a +cal algorithm to a TLA+ specification is performed in      *)
(* three steps:                                                            *)
(*                                                                         *)
(*   Parsing     : Mapping the algorithm text to an AST (Abstract          *)
(*                 Syntax Tree).                                           *)
(*                                                                         *)
(*   Renaming    : Renaming algorithm identifiers to avoid clashes in      *)
(*                 the TLA+ specification.  Those identifiers may          *)
(*                 include local variable names and labels.                *)
(*                                                                         *)
(*   Translation : Mapping the AST to a TLA+ specification.                *)
(*                                                                         *)
(* This module specifies the translation step.  It extends module AST,     *)
(* which is assumed to define two values:                                  *)
(*                                                                         *)
(*   ast      : The algorithm's AST.                                       *)
(*   fairness : A specification of the algorithm's fairness condition,     *)
(*              which is one of the following                              *)
(*                                                                         *)
(*                ""       - No fainess condition.                         *)
(*                "wf"     - Weak fairness of all process actions.         *)
(*                "wfNext" - Weak fairness of entire next-state action.    *)
(*                "sf"     - Strong fairness of all process actions.       *)
(*                                                                         *)
(*                                                                         *)
(* The specification contains three main parts: a specification of the     *)
(* AST, a specification of "label correctness", and a specification of the *)
(* translation.  These sections contain the following definitions, where   *)
(* an error value is one that equals Assert(FALSE, ...)  and whose         *)
(* evaluation produces an error message.                                   *)
(*                                                                         *)
(*   IsAlgorithm : Equals TRUE if ast is a legal AST, FALSE otherwise.     *)
(*                 (However, evaluating it may produce a TLC error if      *)
(*                 ast is not a legal AST.)                                *)
(*                                                                         *)
(*   CheckLabels : Equals TRUE if there are no duplicate labels in the     *)
(*                 same context and every goto statement specifies         *)
(*                 a label that is legal in the statement's context.       *)
(*                 Otherwise, it equals an error value.                    *)
(*                                                                         *)
(*   Translation : Equals either a sequence of strings that represents     *)
(*                 the TLA+ specification obtained from the algorithm,     *)
(*                 or equals an error value if an error in the             *)
(*                 algorithm is detected.                                  *)
(*                                                                         *)
(* Specifying an AST is straightforward, so Part I of the specification is *)
(* of no intrinsic interest.  However, since the translation works on the  *)
(* AST, understanding the translation requires understanding the AST. So,  *)
(* the AST must be specified precisely.  Label checking is rather trivial  *)
(* and Part II has little redeeming social value.  Readers should feel     *)
(* free to skip it.  Part III, the specification of the actual             *)
(* translation, is the interesting part of the specification.              *)
(*                                                                         *)
(* One important aspect of the translation that is not specified here is   *)
(* the formatting of expressions and of the specification.  Neither the    *)
(* AST representation of an expression nor the translation contain any     *)
(* formatting information.  Hence, an algorithm with expressions           *)
(* containing bulleted conjunction/disjunction lists may not be            *)
(* translated correctly, and the translation does not specify how the      *)
(* TLA+ specification is to be formatted.                                  *)
(*                                                                         *)
(* Other than the limitations mentioned above, this module should be a     *)
(* correct specification of the version of +cal at the time of the         *)
(* last-modification date at the beginning of the file.                    *)
(***************************************************************************)

(***************************************************************************)
(*                      RECURSIVE OPERATOR DEFINITIONS                     *)
(*                                                                         *)
(* Georges Gonthier and I have figured out how to assign a reasonable      *)
(* meaning to recursively defined operators, and they may be permitted in  *)
(* a future version of TLA+.  An operator is recursively defined iff it is *)
(* used earlier in the module than its definition.  To prevent accidental  *)
(* recursion, the first use of a recursively defined operator Foo will     *)
(* have to be preceded by a statement such as                              *)
(*                                                                         *)
(*    RECURSIVE Foo(_, _)                                                  *)
(*                                                                         *)
(* In this specification, such recursive specifications are simulated      *)
(* as follows.  The RECURSIVE statement is replaced with                   *)
(*                                                                         *)
(*   (*RECURSIVE*) CONSTANT Foo(_, _)                                      *)
(*                                                                         *)
(* The definition of Foo is modified to be a definition of XFoo (but all   *)
(* occurrences of Foo, including in the definition of XFoo, are left       *)
(* unchanged).  When the specification is executed by TLC, the             *)
(* substitution                                                            *)
(*                                                                         *)
(*   Foo <- XFoo                                                           *)
(*                                                                         *)
(* is placed in a CONSTANT statement in the configuration file.  This      *)
(* will cause TLC to act exactly as it would if Foo had been defined       *)
(* recursively.  (The only problem with this method of simulating          *)
(* recursion is that it doesn't work for recursive definitions within a    *)
(* LET expression.)                                                        *)
(***************************************************************************)

EXTENDS Naturals, Sequences, TLC, AST

-----------------------------------------------------------------------------
(***************************************************************************)
(*                 PART I: THE DEFINITION OF IsAlgorithm                   *)
(*                                                                         *)
(* We describe the AST in terms of a BNF grammar for +cal.  This grammar   *)
(* describes the labeling rules as well as the simple syntax, so it is     *)
(* more complicated than the one in the +cal manual.  However, it is       *)
(* simpler because the parsing phase is assumed to perform macro           *)
(* substitution and to represent an `if' with `elsif' clauses as nested    *)
(* if-then-else statements.                                                *)
(*                                                                         *)
(* The AST is a tree in which each non-leaf node is either a record.       *)
(* Each field of that record is either a child node, a sequence of         *)
(* children nodes, or a value associated with the node.  If a              *)
(* non-terminal in the BNF grammar represents a record node of the AST,    *)
(* we indicate the fields of that record in that non-terminal's            *)
(* production.  For example, the production                                *)
(*                                                                         *)
(*    <VarDecl>  ::= <Name>.var  [= | \in].eqOrIn  <Expr>.val              *)
(*                                                                         *)
(* indicates that a <VarDecl> node is a record r where r.var is a <Name>   *)
(* node, r.val is an <Expr> node, and r.eqOrIn is a value indicating if    *)
(* the statement has an "=" or "\in" token.                                *)
(*                                                                         *)
(* THE BNF GRAMMAR                                                         *)
(* ---------------                                                         *)
(* High-Level Constructs and VariableDeclarations                          *)
(* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^                          *)
(* <Algorithm> ::== <UniprocessAlgorithm> | <MultiprocessAlgorithm>        *)
(*                                                                         *)
(* <UniprocessAlgorithm> ::= --algorithm  <Name>.name                      *)
(*                              variable[s]  <VarDecls>*.decls             *)
(*                              [define <Expr> end define]^0,1.defs        *)
(*                              <Procedure>*.prcds                         *)
(*                              begin  <LabeledStmt>*.body                 *)
(*                              end algorithm                              *)
(*                                                                         *)
(* <MultiprocessAlgorithm> ::= --algorithm <Name>.name                     *)
(*                               <VarDecls>*                               *)
(*                               [define <Expr> end define]^0,1.defs       *)
(*                               <Procedure>*.prcds                        *)
(*                               <Process>*.procs                          *)
(*                                                                         *)
(* <Procedure> ::= procedure  <Name>.name                                  *)
(*                   ( [<PVarDecl> [, <PVarDecl>]*]^0,1.params )           *)
(*                   variable[s]  <PVarDecl>*.decls                        *)
(*                   begin <LabeledStmt>*.body                             *)
(*                   end procedure                                         *)
(*                                                                         *)
(* <Process> ::= process  <Name>.name  [= | \in].eqOrIn  <Expr>.id         *)
(*                 variable[s]  <PVarDecl>*.decls                          *)
(*                   begin <LabeledStmt>*.body                             *)
(*                   end procedure                                         *)
(*                                                                         *)
(* <VarDecl>  ::= <Name>.var  [= | \in].eqOrIn  <Expr>.val                 *)
(*                                                                         *)
(* <PVarDecl> ::= <Name>.var  =.eqOrIn  <Expr>.val                         *)
(*    For convenience, we define a <PVarDecl> node to be a restricted      *)
(*    class of <VarDecl> node.                                             *)
(*                                                                         *)
(* Statements                                                              *)
(* ^^^^^^^^^^                                                              *)
(* In explaining the grammar, we consider three classes of statements:     *)
(*                                                                         *)
(*  - A label statement that may be labeled or contain a label             *)
(*    somewhere inside it.                                                 *)
(*                                                                         *)
(*  - A final statement that contains no label but may contain a           *)
(*    <Goto>, <Call>, or <Return> within it.                               *)
(*                                                                         *)
(*  - A simple statement that contains no label, <Goto>, <Call>, or        *)
(*    <Return>.                                                            *)
(*                                                                         *)
(* We use the naming convention for non-terminals that <LabelX>, <FinalX>, *)
(* and <SimpleX> is a statement of type X of the indicated class.          *)
(*                                                                         *)
(* Label Statement                                                         *)
(* ^^^^^^^^^^^^^^^                                                         *)
(* <LabeledStmt> ::= <Label>.label :                                       *)
(*                      [<NonWhileBody> | <While> <NonWhileBody>].stmts ;  *)
(*                                                                         *)
(* <While>  ::= while  <Expr>.test  do                                     *)
(*                 <NonWhileBody>.unlabDo  <LabeledStmt>*.labDo            *)
(*              end while ;                                                *)
(*                                                                         *)
(* <NonWhileBody> ::= <SimpleStmtSeqFinalStmt01> |                         *)
(*                      [<SimpleStmtSeq> [<LabelIf> | <LabelEither>]]      *)
(*                                                                         *)
(* <LabelIf> ::= if <Expr>                                                 *)
(*                 then <NonWhileBody>.unlabThen  <LabeledStmt>*.labThen   *)
(*                 else <NonWhileBody>.unlabElse  <LabeledStmt>*.labElse   *)
(*               end if ;                                                  *)
(*                                                                         *)
(* <LabelEither> ::= either                                                *)
(*                     [<EitherClause> [or <EitherClause>]^+].clauses      *)
(*                   end either ;                                          *)
(*                                                                         *)
(* <EitherClause> ::= <NonWhileBody>.unlabOr  <LabeledStmt>*.labOr         *)
(*                                                                         *)
(*                                                                         *)
(* Final Statements                                                        *)
(* ^^^^^^^^^^^^^^^^                                                        *)
(* <SimpleStmtSeqFinalStmt01> ::= <SimpleStmtSeq> <FinalStmt>^0,1          *)
(*                                                                         *)
(* <FinalStmt>   ::= <FinalIf> | <FinalWith> | <CallOrReturn> | <Goto>     *)
(*                                                                         *)
(* <FinalIf>     ::= if <Expr>.test  then <SimpleStmtSeqFinalStmt01>.then  *)
(*                                   else <SimpleStmtSeqFinalStmt01>.else  *)
(*                   end if ;                                              *)
(*                                                                         *)
(* <FinalEither> ::= either [<SimpleStmtSeqFinalStmt01>                    *)
(*                              [or <SimpleStmtSeqFinalStmt01>]+ ].ors     *)
(*                   end either ;                                          *)
(*                                                                         *)
(* <FinalWith>   ::= with  <Name>.var  [= | \in].eqOrIn  <Expr>.exp        *)
(*                     do  <SimpleStmtSeqFinalStmt01>.do                   *)
(*                   end with ;                                            *)
(*                                                                         *)
(* Simple Statements                                                       *)
(* ^^^^^^^^^^^^^^^^^                                                       *)
(* <SimpleStmtSeq> ::= <SimpleStmt>*                                       *)
(*                                                                         *)
(* <SimpleStmt>    ::= <When> | <Print> | <Assert> | <Skip> | <Assign> |   *)
(*                     <SimpleWith> | <SimpleIf> | <SimpleEither>          *)
(*                                                                         *)
(* <SimpleWith>    ::= with  <Name>.var  [= | \in].eqOrIn   <Expr>.exp     *)
(*                       do  <SimpleStmtSeq>.do                            *)
(*                     end with ;                                          *)
(*                                                                         *)
(* <SimpleIf>      ::= if  <Expr>.test  then  <SimpleStmtSeq>.then         *)
(*                                      else  <SimpleStmtSeq>              *)
(*                     end if;                                             *)
(*                                                                         *)
(* <SimpleEither>  ::= either <SimpleStmtSeq> [or <SimpleStmtSeq>]^+       *)
(*                     end either ;                                        *)
(*                                                                         *)
(* <Assign>       ::= [ <SingleAssign> [ || <SingleAssign>]^* ].ass ;      *)
(*                                                                         *)
(* <SingleAssign> ::= <Name>.lhs.var  <Expr>.lhs.sub  :=  <Expr>.rhs       *)
(*    NOTE: <Expr>.lhs.sub is the "subscript"--for example, the            *)
(*          ".foo[3]" in "x.foo[3] := exp".                                *)
(*                                                                         *)
(* <CallOrReturn> ::= <Call> | <Return> | <CallReturn>                     *)
(*                                                                         *)
(* <Call>         ::= call <Name>.to ( [<Expr> [, <Expr>]^*]^0,1.args ) ;  *)
(*                                                                         *)
(* <Return>       ::= return ;                                             *)
(*    NOTE: <Return>.from is the name of the procedure containing          *)
(*          the statement.                                                 *)
(*                                                                         *)
(* <CallReturn>   ::= <Call> ; <Return>                                    *)
(*    NOTE: Has the fields of both the <Call> and the <Return>.  It        *)
(*          is made a separate node type for convenience of the            *)
(*          translation.                                                   *)
(*                                                                         *)
(* <Goto>   ::= goto <Label>.to ;                                          *)
(* <When>   ::= when <Expr>.exp  ;                                         *)
(* <Print>  ::= print <Expr>.exp ;                                         *)
(* <Assert> ::= assert <Expr>.exp ;                                        *)
(* <Skip>   ::= skip ;                                                     *)
(*                                                                         *)
(* Terminals                                                               *)
(* ^^^^^^^^^                                                               *)
(* <Expr>  : A sequence of strings that usually represents a TLA+          *)
(*           expression, but is also used to represent the contents of     *)
(*           a `define' section.                                           *)
(*                                                                         *)
(*           In the representation of a TLA+ expression by a sequence      *)
(*           of strings, each token is represented by a single string,     *)
(*           except that a quoted token is bracketed by the strings        *)
(*           "\"" (a string containing a single quote character), so       *)
(*           the string "foo bar" is represented by the sequence of        *)
(*           three strings "\"", "foo bar", "\"".                          *)
(*                                                                         *)
(* <Name>  : A TLA+ identifier that is not a TLA+ or +cal reserved word.   *)
(*                                                                         *)
(* <Label> : A <Name> that is not "Done" or "Error".                       *)
(*                                                                         *)
(* THE TLA+ SPECIFICATION OF THE AST                                       *)
(* ---------------------------------                                       *)
(* For every terminal or nonterminal <Foo> of the BNF, we define an        *)
(* operator IsFoo(x) that is true iff x is a <Foo> node.  To minimize the  *)
(* number of recursive definitions needed, we define these operators in an *)
(* approximately bottom-up order, rather than in the top-down order of the *)
(* BNF grammar.                                                            *)
(*                                                                         *)
(* We begin by defining some operators that will be used in defining the   *)
(* Is...  operators.                                                       *)
(***************************************************************************)
IsRecord(r, D) == DOMAIN r = D 
  (*************************************************************************)
  (* If D is a set of strings, then this is true iff r is a record whose   *)
  (* set of fields equals D.                                               *)
  (*************************************************************************)

IsSeq(IsX(_), seq) ==
  (*************************************************************************)
  (* True iff seq is a sequence and IsX(seq[i]) is true for all i in       *)
  (* DOMAIN seq.                                                           *)
  (*************************************************************************)
  /\ DOMAIN seq = 1..Len(seq)
  /\ \A i \in 1..Len(seq) : IsX(seq[i])

Front(seq) == [i \in 1..(Len(seq)-1) |-> seq[i]]
Last(seq)  == seq[Len(seq)]
  (*************************************************************************)
  (* Front(<<s1, s2, s3>>) = <<s1, s2>>                                    *)
  (* Last(<<s1, s2, s3>>)  = s3                                            *)
  (*************************************************************************)

IsString(str) == str \in STRING
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            The BNF Terminals                            *)
(***************************************************************************)
IsName(name) ==
  (*************************************************************************)
  (* A <Name> is any string of letters, digits, and "_" characters         *)
  (* containing at least one non-digit that is not a TLA+ reserved word or *)
  (* a +CAL reserved word.                                                 *)
  (*                                                                       *)
  (* Note: TLA+ defines a string to be a sequence of characters, but TLC   *)
  (* does not treat them as such and so it cannot evaluate this            *)
  (* definition.  The configuration file substitutes IsString for IsName.  *)
  (*************************************************************************)
  LET Letters == {"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_"[i] :
                    i \in 1..53}
      Digits  == {"0123456789"[i] : i \in 1..10}
  IN  name \in Seq(Letters \cup Digits) \
                 ( Seq(Digits) \cup
                   {"ASSUME", "ASSUMPTION", "AXIOM", "CASE", "CHOOSE",
                    "CONSTANT", "CONSTANTS", "DOMAIN", "ELSE", "ENABLED",
                    "EXCEPT", "EXTENDS", "IF", "IN", "INSTANCE", "LET",
                    "LOCAL", "MODULE", "OTHER", "UNION", "SUBSET", "THEN",
                    "THEOREM", "UNCHANGED", "VARIABLE", "VARIABLES", 
                    "WITH", "WF_", "SF_",
                    "assert", "begin", "call", "do", "either", "else",
                    "elsif", "end", "goto", "if", "macro", "or",
                    "print", "procedure", "process", "fair", "return", "skip",
                    "then", "variable", "variables", "while", "with"} )

IsLabel(label) == /\ IsName(label)
                  /\ label \notin {"Done", "Error"}

IsExpr(expr) == IsSeq(IsString, expr)
-----------------------------------------------------------------------------
(***************************************************************************)
(*             Non-Recursively Defined Simple Statement Nodes              *)
(***************************************************************************)

(***************************************************************************)
(* Very simple statements.                                                 *)
(***************************************************************************)
IsWhen(stmt) ==
  /\ IsRecord(stmt, {"type", "exp"})
  /\ stmt.type = "when"
  /\ IsExpr(stmt.exp)

IsPrint(stmt) ==
  /\ IsRecord(stmt, {"type", "exp"})
  /\ stmt.type = "print"
  /\ IsExpr(stmt.exp)

IsAssert(stmt) ==
  /\ IsRecord(stmt, {"type", "exp"})
  /\ stmt.type = "assert"
  /\ IsExpr(stmt.exp)

IsSkip(stmt) ==
  /\ IsRecord(stmt, {"type"})
  /\ stmt.type = "skip"


IsGoto(stmt) ==
  /\ IsRecord(stmt, {"type", "to"})
  /\ stmt.type = "goto"
  /\ IsLabel(stmt.to)          

(***************************************************************************)
(* Call and returns                                                       *)
(***************************************************************************)
IsCall(stmt) ==
  /\ IsRecord(stmt, {"type", "returnTo", "to", "args"})
  /\ stmt.type = "call"
  /\ stmt.returnTo = ""      
     (**********************************************************************)
     (* As a consequence of evolution by non-intelligent design, the Call  *)
     (* node has a returnTo field that always equals the empty string.     *)
     (**********************************************************************)
  /\ IsName(stmt.to)            \* The name of the procedure being called
  /\ IsSeq(IsExpr, stmt.args)

IsReturn(stmt)==
  /\ IsRecord(stmt, {"type", "from"})
  /\ stmt.type = "return"
  /\ IsName(stmt.from)           \* The name of the returning procedure

IsCallReturn(stmt) ==
  /\ IsRecord(stmt, {"type", "from", "to", "args"})
  /\ stmt.type = "callReturn"
  /\ IsName(stmt.from)         \* The procedure containing the call+return
  /\ IsName(stmt.to)           \* The name of the procedure being called 
  /\ IsSeq(IsExpr, stmt.args)

IsCallOrReturn(stmt) ==
  IsCall(stmt) \/ IsReturn(stmt) \/ IsCallReturn(stmt) 

(***************************************************************************)
(* Assignment.                                                             *)
(***************************************************************************)
IsSingleAssign(ass) ==
  /\ IsRecord(ass, {"lhs", "rhs"})
  /\ /\ IsRecord(ass.lhs, {"var", "sub"})
     /\ IsName(ass.lhs.var)
     /\ IsExpr(ass.lhs.sub)
  /\ IsExpr(ass.rhs)

IsAssign(stmt) ==
  /\ IsRecord(stmt, {"type", "ass"})
  /\ stmt.type = "assignment"
  /\ IsSeq(IsSingleAssign, stmt.ass)

(***************************************************************************)
(*             Recursively-Defined Simple Statement Nodes                  *)
(***************************************************************************)
(*RECURSIVE*) CONSTANT IsSimpleStmt(_), IsSimpleStmtSeq(_)

IsSimpleWith(stmt) ==
  /\ IsRecord(stmt, {"type", "var", "eqOrIn", "exp", "do"})
  /\ stmt.type = "with"
  /\ IsName(stmt.var)
  /\ stmt.eqOrIn \in {"=", "\\in"}
  /\ IsExpr(stmt.exp)
  /\ IsSimpleStmtSeq(stmt.do) /\ (stmt.do # << >>)

IsSimpleIf(stmt) ==
  /\ IsRecord(stmt, {"type", "test", "then", "else"})
  /\ stmt.type = "if"
  /\ IsExpr(stmt.test)
  /\ IsSimpleStmtSeq(stmt.then)
  /\ IsSimpleStmtSeq(stmt.else)

IsSimpleEither(stmt) ==
  /\ IsRecord(stmt, {"type", "ors"})
  /\ stmt.type = "either"
  /\ IsSeq(IsSimpleStmtSeq, stmt.ors) /\ (Len(stmt.ors) > 1)

XIsSimpleStmt(stmt) == 
  IsWhen(stmt)    \/  IsSkip(stmt)       \/  IsSimpleIf(stmt)      \/  
  IsPrint(stmt)   \/  IsAssign(stmt)     \/  IsSimpleEither(stmt)  \/  
  IsAssert(stmt)  \/  IsSimpleWith(stmt)                   

XIsSimpleStmtSeq(seq) == IsSeq(IsSimpleStmt, seq)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                         Labeled Statement Nodes                         *)
(***************************************************************************)
(*RECURSIVE*) CONSTANT IsNonWhileBody(_), IsWhile(_), IsFinalStmt(_)

IsLabeledStmt(stmt) ==
  /\ IsRecord(stmt, {"label", "stmts"})
  /\ IsLabel(stmt.label)
  /\ \/ /\ IsNonWhileBody(stmt.stmts)
        /\ stmt.stmts # << >>
     \/ /\ IsWhile(Head(stmt.stmts))
        /\ IsNonWhileBody(Tail(stmt.stmts))

XIsWhile(stmt) ==
  /\ IsRecord(stmt, {"type", "test", "unlabDo", "labDo"})
  /\ stmt.type = "while"
  /\ IsExpr(stmt.test)     
  /\ IsNonWhileBody(stmt.unlabDo)
  /\ IsSeq(IsLabeledStmt, stmt.labDo)

IsSimpleStmtSeqFinalStmt01(seq) ==
  \/ IsSimpleStmtSeq(seq)
  \/ /\ IsSimpleStmtSeq(Front(seq))
     /\ IsFinalStmt(Last(seq))

(*RECURSIVE*) CONSTANT IsLabelIf(_), IsLabelEither(_)

XIsNonWhileBody(seq) ==
  \/ IsSimpleStmtSeqFinalStmt01(seq)
  \/ /\ IsSimpleStmtSeq(Front(seq))
     /\ \/ IsLabelIf(Last(seq))
        \/ IsLabelEither(Last(seq))

XIsLabelIf(stmt) ==
  /\ IsRecord(stmt, {"type", "test", "unlabThen", 
                      "labThen", "unlabElse", "labElse"})
  /\ stmt.type = "labelIf"
  /\ IsExpr(stmt.test)
  /\ IsNonWhileBody(stmt.unlabThen)
  /\ IsSeq(IsLabeledStmt, stmt.labThen)
  /\ IsNonWhileBody(stmt.unlabElse)
  /\ IsSeq(IsLabeledStmt, stmt.labElse)

IsEitherClause(cls) ==
  /\ IsRecord(cls, {"unlabOr", "labOr"})
  /\ IsNonWhileBody(cls.unlabOr)
  /\ IsSeq(IsLabeledStmt, cls.labOr)

XIsLabelEither(stmt) ==
  /\ IsRecord(stmt, {"type", "clauses"})
  /\ stmt.type = "labelEither"
  /\ IsSeq(IsEitherClause, stmt.clauses) 

(***************************************************************************)
(*                         Final Statement Nodes                           *)
(***************************************************************************)
IsFinalIf(stmt) ==
  /\ IsRecord(stmt, {"type", "test", "then", "else"})
  /\ stmt.type = "if"
  /\ IsExpr(stmt.test)
  /\ IsSimpleStmtSeqFinalStmt01(stmt.then)
  /\ IsSimpleStmtSeqFinalStmt01(stmt.else)

IsFinalEither(stmt) ==
  /\ IsRecord(stmt, {"type", "ors"})
  /\ stmt.type = "either"
  /\ IsSeq(IsSimpleStmtSeqFinalStmt01, stmt.ors) 
         /\ (Len(stmt.ors) > 1)

IsFinalWith(stmt) ==
  /\ IsRecord(stmt, {"type", "var", "eqOrIn", "exp", "do"})
  /\ stmt.type = "with"
  /\ IsName(stmt.var)
  /\ stmt.eqOrIn \in {"=", "\\in"}
  /\ IsExpr(stmt.exp)
  /\ IsSimpleStmtSeqFinalStmt01(stmt.do) /\ (stmt.do # << >>)

XIsFinalStmt(stmt) ==
  IsFinalIf(stmt) \/ IsFinalWith(stmt) \/ IsCallOrReturn(stmt) \/ IsGoto(stmt)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                       Variable Declaration Nodes                        *)
(***************************************************************************)
IsVarDecl(decl) ==
  /\ IsRecord(decl, {"var", "eqOrIn", "val"})
  /\ IsName(decl.var)
  /\ decl.eqOrIn \in {"=", "\\in"}
  /\ IsExpr(decl.val)

IsPVarDecl(decl) ==
  /\ IsVarDecl(decl) 
  /\ decl.eqOrIn = "="
-----------------------------------------------------------------------------
(***************************************************************************)
(*                           High-Level Constructs                         *)
(***************************************************************************)
IsProcedure(prcd) ==
  /\ IsRecord(prcd, {"name", "params", "decls", "body"})
  /\ IsName(prcd.name)
  /\ IsSeq(IsPVarDecl, prcd.params)
  /\ IsSeq(IsPVarDecl, prcd.decls)
  /\ IsSeq(IsLabeledStmt, prcd.body)

IsProcess(proc) ==
  /\ IsRecord(proc, {"name", "decls", "id", "eqOrIn", "body"})
  /\ IsName(proc.name)
  /\ proc.eqOrIn \in {"=", "\\in"}
  /\ IsExpr(proc.id)
  /\ IsSeq(IsVarDecl, proc.decls)
  /\ IsSeq(IsLabeledStmt, proc.body)

(***************************************************************************)
(* The operators IsUniprocessAlgorithm, IsMultiprocessAlgorithm, and       *)
(* IsAlgorithm have no need for arguments.                                 *)
(***************************************************************************)
IsUniprocessAlgorithm ==
  /\ ast.type = "uniprocess"
  /\ IsRecord(ast, {"type", "name", "defs", "decls", "prcds", "body"})
  /\ IsName(ast.name)
  /\ IsExpr(ast.defs)
  /\ IsSeq(IsVarDecl, ast.decls)
  /\ IsSeq(IsProcedure, ast.prcds)
  /\ IsSeq(IsLabeledStmt, ast.body) 

IsMultiprocessAlgorithm ==
  /\ ast.type = "multiprocess"
  /\ IsRecord(ast, {"type", "name", "decls", "prcds", "procs", "defs"})
  /\ IsExpr(ast.defs)
  /\ IsName(ast.name)
  /\ IsSeq(IsVarDecl, ast.decls)
  /\ IsSeq(IsProcedure, ast.prcds)
  /\ IsSeq(IsProcess, ast.procs) 

IsAlgorithm  == \/ IsUniprocessAlgorithm
                \/ IsMultiprocessAlgorithm 
-----------------------------------------------------------------------------

(***************************************************************************)
(*                            PART II:  CHECKING LABELS                    *)
(*                                                                         *)
(* Before getting to the definition of CheckLabels, we define the operator *)
(* isMP and some operators for reporting errors that are used here and in  *)
(* Part III.                                                               *)
(***************************************************************************)

isMP == ast.type = "multiprocess" 
  (*************************************************************************)
  (* True iff this is a multiprocess rather than a uniprocess algorithm.   *)
  (*************************************************************************)

(***************************************************************************)
(* ERROR REPORTING                                                         *)
(* --------------                                                          *)
(* There are three operators that cause TLC to halt and produce an error   *)
(* message when it evaluates them.  They report either an error in the     *)
(* algorithm, an error in the specification, or an error in the AST file   *)
(* written by the parser.                                                  *)
(*                                                                         *)
(* The message is bracketed by "@Error@" and "@EndError@", which will      *)
(* cause it to be printed by the +cal translation program that invoked     *)
(* TLC.  The +cal translation program expects the translation to be        *)
(* printed as a sequence of strings, all on a single line.  It ignores all *)
(* output except for the first line that begins with "<<".  Therefore, the *)
(* error message must begin with "<<".                                     *)
(***************************************************************************)
Error(msg)     == /\ PrintT("<<@Error@" \o msg \o "@EndError@>>")
                  /\ Assert(FALSE, "")

SpecBug(msg)   == Assert(FALSE, "<<@Error@" \o "Bug in specification: " \o
                          msg \o "@EndError@>>")
ParserBug(msg) == Assert(FALSE, "<<@Error@" \o 
                          "Bug in AST written by parser: " \o msg \o 
                          "@EndError@>>")
-----------------------------------------------------------------------------
(***************************************************************************)
(* The definition of label checking is not very interesting.  It is quite  *)
(* obvious and is irrelevant for the rest of the specification.  The       *)
(* definition of the translation phase is perfectly reasonable if there    *)
(* are conflicting labels or if a the destination of a goto is a           *)
(* non-existent label.  If the labels are incorrect, the resulting         *)
(* specification will be weird--especially in the case of duplicate        *)
(* labels.  But since it's easy enough for the translator to check the     *)
(* labels, we have specified it here.                                      *)
(*                                                                         *)
(* Actually checking the labels is a straightforward exercise in           *)
(* programming.  It involves exploring the appropriate parts of the AST to *)
(* gather all the `label' fields of <LabeledStmt> nodes and all the `to'   *)
(* fields of <Goto> notes.  This is done by recursively defining operators *)
(* that return a record with the appropriate two fields.                   *)
(***************************************************************************)
Disjoint(seq) ==
  (*************************************************************************)
  (* True iff the sequence seq of sets are all mutually disjoint.          *)
  (*************************************************************************)
  \A i \in 1..Len(seq) : \A j \in (i+1)..Len(seq) : seq[i] \cap seq[j] = {}
    
(*RECURSIVE*) CONSTANT LabelsOfUnLabelStmt(_) , LabelsOfUnLabelStmtSeq(_), 
                       LabelsOfLabeledStmtSeq(_) 

XLabelsOfUnLabelStmtSeq(seq) ==
  LET head == LabelsOfUnLabelStmt(Head(seq))
      rest == LabelsOfUnLabelStmtSeq(Tail(seq))
  IN  IF seq = << >> 
       THEN [gotos |-> {}, labels |-> {}]
       ELSE IF Disjoint(<<head.labels, rest.labels>>)
              THEN [gotos  |-> head.gotos \cup rest.gotos,
                    labels |-> head.labels \cup rest.labels]
              ELSE Error("Duplicate label(s)")

XLabelsOfLabeledStmtSeq(seq) ==
  LET head == LabelsOfUnLabelStmtSeq(Head(seq).stmts)
      rest == LabelsOfLabeledStmtSeq(Tail(seq))
  IN  IF seq = << >> 
       THEN [gotos |-> {}, labels |-> {}]
       ELSE IF Disjoint(<<head.labels, rest.labels, {Head(seq).label}>>)
              THEN [gotos  |-> head.gotos \cup rest.gotos,
                    labels |-> {Head(seq).label} \cup head.labels 
                                \cup rest.labels]
              ELSE Error("Duplicate label(s)")

XLabelsOfUnLabelStmt(stmt) ==
  CASE stmt.type = "while" ->
         LET labDo   == LabelsOfLabeledStmtSeq(stmt.labDo)
             unlabDo == LabelsOfUnLabelStmtSeq(stmt.unlabDo)
         IN  IF Disjoint(<<labDo.labels, unlabDo.labels>>)
               THEN [gotos  |-> labDo.gotos  \cup unlabDo.gotos,
                    labels |-> labDo.labels \cup unlabDo.labels]
               ELSE Error("Duplicate label(s)")
    [] stmt.type = "if" -> 
         LET then == LabelsOfUnLabelStmtSeq(stmt.then)
             else == LabelsOfUnLabelStmtSeq(stmt.else)
         IN  IF Disjoint(<<then.labels, else.labels>>)
               THEN [gotos  |-> then.gotos  \cup else.gotos,
                     labels |-> then.labels \cup else.labels]
               ELSE Error("Duplicate label(s)")
    [] stmt.type = "labelIf" -> 
         LET labThen   == LabelsOfLabeledStmtSeq(stmt.labThen)
             unlabThen == LabelsOfUnLabelStmtSeq(stmt.unlabThen)
             labElse   == LabelsOfLabeledStmtSeq(stmt.labElse)
             unlabElse == LabelsOfUnLabelStmtSeq(stmt.unlabElse)
         IN  IF Disjoint(<<labThen.labels, unlabThen.labels,
                           labElse.labels, unlabElse.labels>>)
               THEN [gotos  |-> labThen.gotos  \cup unlabThen.gotos \cup
                     labElse.gotos  \cup unlabElse.gotos ,
                     labels |-> labThen.labels \cup unlabThen.labels \cup
                                labElse.labels \cup unlabElse.labels ]
               ELSE Error("Duplicate label(s)")
    [] stmt.type = "either" -> 
         LET ors(i) == LabelsOfUnLabelStmtSeq(stmt.ors[i])
         IN  IF Disjoint([i \in 1..Len(stmt.ors) |-> ors(i).labels])
               THEN [gotos  |-> UNION {ors(i).gotos : 
                                          i \in 1..Len(stmt.ors)},
                     labels |-> UNION {ors(i).labels : 
                                          i \in 1..Len(stmt.ors)}]
               ELSE Error("Duplicate label(s)")
    [] stmt.type = "labelEither" -> 
         LET labOrs(i)   == LabelsOfLabeledStmtSeq(stmt.clauses[i].labOr)
             unlabOrs(i) == LabelsOfUnLabelStmtSeq(stmt.clauses[i].unlabOr)
         IN  IF Disjoint([i \in 1..Len(stmt.clauses)   |-> labOrs(i).labels] \o
                         [i \in 1..Len(stmt.clauses) |-> unlabOrs(i).labels])
               THEN [gotos  |-> (UNION {labOrs(i).gotos : 
                                   i \in 1..Len(stmt.clauses)}) \cup
                                (UNION {unlabOrs(i).gotos : 
                                   i \in 1..Len(stmt.clauses)}),
                     labels |-> (UNION {labOrs(i).labels : 
                                   i \in 1..Len(stmt.clauses)}) \cup
                                (UNION {unlabOrs(i).labels : 
                                   i \in 1..Len(stmt.clauses)})]
               ELSE Error("Duplicate label(s)")
    [] stmt.type = "goto" -> [gotos |-> {stmt.to}, labels |-> {}]
    [] stmt.type = "with" -> LabelsOfUnLabelStmtSeq(stmt.do)
    [] OTHER -> [gotos |-> {}, labels |-> {}]

ReportBadLabels(seq, where) ==
  (*************************************************************************)
  (* Finds the labels and goto destinations in the sequence seq of         *)
  (* <LabeledStmt>s and reports an error if there is a goto with a         *)
  (* non-existent destination.                                             *)
  (*************************************************************************)
  LET lab == LabelsOfLabeledStmtSeq(seq)
  IN  IF lab.gotos \subseteq lab.labels \cup {"Done", "Error"}
        THEN TRUE
        ELSE Error("Bad goto label(s) " \o ToString(lab.gotos \ lab.labels) \o
                    " in " \o where)

CheckLabels ==
  /\ \A i \in 1..Len(ast.prcds) : 
         ReportBadLabels(ast.prcds[i].body, "procedure " \o ast.prcds[i].name)
  /\ IF isMP
       THEN \A i \in 1..Len(ast.procs) : 
              ReportBadLabels(ast.procs[i].body, 
                              "process " \o ast.procs[i].name)
       ELSE ReportBadLabels(ast.body, "main body of algorithm")
-----------------------------------------------------------------------------
(***************************************************************************)
(*                        PART III.  THE TRANSLATION                       *)
(*                                                                         *)
(* We now come to the interesting part, the actual translation.  We begin  *)
(* with some operators that will be useful.                                *)
(***************************************************************************)

Quote(id) == <<"\"", id, "\"" >>
  (*************************************************************************)
  (* Some identifiers in the algorithm appear as strings in the            *)
  (* tranlation.  For example, the statement                               *)
  (*                                                                       *)
  (*    goto foo                                                           *)
  (*                                                                       *)
  (* may be translated as the TLA+ formula                                 *)
  (*                                                                       *)
  (*    pc' = "foo"                                                        *)
  (*                                                                       *)
  (* As explained above, this formula is represented by the <Expr>         *)
  (* (string of tokens)                                                    *)
  (*                                                                       *)
  (*   << "pc", "'", "=", "\"", "foo", "\"" >>                             *)
  (*                                                                       *)
  (* This <Expr> can be written                                            *)
  (*                                                                       *)
  (*   << "pc", "'", "=" >> \o Quote("foo")                                *)
  (*************************************************************************)

(***************************************************************************)
(* We recursively define the operators SeqConcat and SepSeqConcat for      *)
(* concatenating the elements of a sequence, the latter inserting a value  *)
(* between those concatenated sequences.  They are defined so that if      *)
(* seq = << s1, s2, s3 >>, then                                            *)
(*   SeqConcat(seq)       == s1 \o s2 \o s3.                               *)
(*   SepSeqConcat(seq, e) == s1 \o << e >> \o s2 \o << e >> \o s3          *)
(***************************************************************************)
(*RECURSIVE*) CONSTANT SeqConcat(_), SepSeqConcat(_, _)
XSeqConcat(seq) == IF seq = << >> THEN << >> 
                                  ELSE Head(seq) \o SeqConcat(Tail(seq))
XSepSeqConcat(seq, e) == 
  IF Len(seq) = 0 
    THEN SpecBug("SepSeqConcat called with empty sequence")
    ELSE IF Len(seq) = 1 THEN Head(seq)
                         ELSE Head(seq) \o <<e>> \o SepSeqConcat(Tail(seq), e)

MakeConj(seq) ==
  (*************************************************************************)
  (* Equals the conjunction of the sequence seq of expressions, each       *)
  (* enclosed in parentheses.  Thus, If seq is the sequence                *)
  (* <<exp1, exp2, exp3>> of three expressions, then                       *)
  (*    MakeConj(seq) =  (exp1) /\ ...  /\ (expN).                         *)
  (*************************************************************************)
  SepSeqConcat([i \in 1..Len(seq) |-> <<"(">> \o seq[i] \o <<")">>], "/\\")

MakeDisj(seq) ==
  (*************************************************************************)
  (* Equals the disjunction of the sequence seq of expressions, each       *)
  (* enclosed in parentheses.  Thus, If seq is the sequence                *)
  (* <<exp1, exp2, exp3>> of three expressions, then                       *)
  (*    MakeDisj(seq) =  (exp1) \/ ...  \/ (expN).                         *)
  (*************************************************************************)
  SepSeqConcat([i \in 1..Len(seq) |-> <<"(">> \o seq[i] \o <<")">>], "\\/")


(***************************************************************************)
(* We now define some operators for forming sets and subsequences from     *)
(* sequences.                                                              *)
(***************************************************************************)
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}
  (*************************************************************************)
  (* The set of elements in the sequence seq.   Thus                       *)
  (*   SeqToSet( << 1, 2, 3 >> ) = SeqToSet( << 3, 2, 1 >> ) = {3, 1, 2}   *)
  (*************************************************************************)
  
SetToSubseq(S, seq) ==
  (*************************************************************************)
  (* The subsequence of seq containing those elements in S.  Thus,         *)
  (*    SetToSubseq( <<4, 3, 2, 1, 2>> , {2, 4} ) = <<4, 2, 2>>            *)
  (*************************************************************************)
  LET Test(e) == e \in S IN SelectSeq(seq, Test)

CompSetToSubseq(S, seq) ==
  (*************************************************************************)
  (* The subsequence of seq containing those elements not in S. Thus,      *)
  (*    CompSetToSubseq( <<4, 3, 2, 1, 2>> , {2, 4} ) = <<3, 1>>           *)
  (*************************************************************************)
  LET Test(e) == e \notin S IN SelectSeq(seq, Test)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                    Handling the Variables stack and pc                  *)
(*                                                                         *)
(* The translation introduces variables `pc' to keep track of the control  *)
(* state and `stack' to hold the procedure-calling stack, if there are     *)
(* procedures.  To avoid complicated special cases, we want the            *)
(* definition of the translation to treat these variables just like the    *)
(* algorithm's ordinary variables.  For example, we would like to define   *)
(* the translation of the statement `goto foo' to be the same as the       *)
(* translation of `pc := "foo"'.                                           *)
(*                                                                         *)
(* There is a problem with this.  These variables may also appear in the   *)
(* algorithm itself.  In a multiprocess algorithm, occurrences of these    *)
(* variables in the algorithm must be treated differently from the ones    *)
(* introduced by the translation.  We want to subscript instances of `pc'  *)
(* introduced by the translation.  For example, the statement  pc := "foo" *)
(* in a multiprocess algorithm might be handled as if it were really       *)
(* pc[self] := "foo" .  However, occurrences of pc in the algorithm should *)
(* not be subscripted.  For example, we should not add the subscript       *)
(* "[self]" to the occurrence of pc in                                     *)
(*                                                                         *)
(*    assert \A i \in ProcSet \ {"self"} : pc[i] # "cs"                    *)
(*                                                                         *)
(* To solve this problem, the translation is defined as if it were adding  *)
(* the variables @pc@ and @stack@ instead of pc and `stack'.  As the very  *)
(* last step of the translation, we replace @pc@ and @stack@ by pc and     *)
(* `stack'.                                                                *)
(*                                                                         *)
(* Note that the algorithm may assign to `stack'--for example, with        *)
(*                                                                         *)
(*    stack[(self + 1) % N][1].foo := 17                                   *)
(*                                                                         *)
(* The translation must detect that this is an error if this assignment    *)
(* statement occurs in the same step as a call or return, which will be    *)
(* translated as if it were an assignment to @stack@.  The translation     *)
(* does not allow the algorithm to assign to pc.  Although it might be     *)
(* nice to allow one process to abort another by setting its pc to "Done", *)
(* this complements the implementation more than it's worth.  Even         *)
(* allowing assignments to stack is of dubious value.  I am including the  *)
(* possibility because I have encountered one instance in which a          *)
(* Microsoft engineer was interested in verifying an algorithm that        *)
(* manipulated the stack in this way.                                      *)
(***************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                         Calls and Returns                               *)
(*                                                                         *)
(* We now define some procedures used for translating call and return      *)
(* statements.  They are used to convert calls and returns into assignment *)
(* statements, which are then translated.                                  *)
(*                                                                         *)
(* First, we define the operator NameToPrcd for mapping from a procedure   *)
(* name to the corresponding <Procedure> object.  This operator is used    *)
(* later as well.                                                          *)
(***************************************************************************)
NameToPrcd(name) ==
  (*************************************************************************)
  (* The procedure named `name'.  Evaluation causes an error if there is   *)
  (* no such procedure.                                                    *)
  (*************************************************************************)
  IF \E i \in 1..Len(ast.prcds) : ast.prcds[i].name = name
   THEN ast.prcds[CHOOSE i \in 1..Len(ast.prcds) : ast.prcds[i].name = name]
   ELSE Error("There is no procedure named " \o name)

SetPrcdVarsOnCall(call, prcd) ==
  (*************************************************************************)
  (* A sequence of Assign statements to set the variables of procedure     *)
  (* prcd when called by a Call or CallReturn statement `call'.  The       *)
  (* following example indicates that the order of assignments matters.    *)
  (*                                                                       *)
  (*   procedure P(a)                                                      *)
  (*   variables x = a ; y = x+1 ;                                         *)
  (*                                                                       *)
  (* Evaluation causes an error if the number of arguments in the call     *)
  (* does not equal the number of arguments of the procedure.              *)
  (*************************************************************************)
  IF Len(prcd.params) = Len(call.args)
    THEN (******************************************************************)
         (* Use a single assignment to set the parameter variables.        *)
         (******************************************************************)
         << [type |-> "assignment", 
             ass  |-> [i \in 1..Len(prcd.params) |-> 
                         [lhs |-> [var |->  prcd.params[i].var, 
                                   sub |-> << >>],
                          rhs |-> call.args[i]]]] >> \o

         (******************************************************************)
         (* Use a sequence of assignments to set the procedure's local     *)
         (* variables.                                                     *)
         (******************************************************************)
         [i \in 1..Len(prcd.decls) |->                    
            [type |-> "assignment", 
             ass  |-> <<[lhs |-> [var |-> prcd.decls[i].var, sub |-> << >>],
                         rhs |-> prcd.decls[i].val] >> ] ]

    ELSE Error("Procedure " \o prcd.name \o 
               " called with wrong number of arguments")

CallStackHead(returnTo, prcd) ==
  (*************************************************************************)
  (* An expression equal to the head of the stack in which are saved the   *)
  (* parameters and local variables of procedure prcd on a call that is to *)
  (* return to label returnTo.  It is a record of the following form,      *)
  (* where the param_i are the procedure's parameters and the vbl_i are    *)
  (* its local variables.                                                  *)
  (*                                                                       *)
  (*     [procedure |-> name,                                              *)
  (*      pc        |-> returnTo,                                          *)
  (*      param_1   |-> param1,                                            *)
  (*       ...                                                             *)
  (*      param_N   |-> paramN,                                            *)
  (*      vbl_1     |-> vbl1,                                              *)
  (*      ...                                                              *)
  (*      vbl_N     |-> vblN]                                              *)
  (*                                                                       *)
  (* Note: returnTo should be an expression, so if it's a label it should  *)
  (* be quoted.                                                            *)
  (*************************************************************************)
  <<"[">> \o
   SepSeqConcat(<< << "procedure", "|->">> \o Quote(prcd.name), 
                   << "pc", "|->">> \o returnTo           
                >> \o
                  [i \in 1..Len(prcd.params) |->
                     <<prcd.params[i].var, "|->", prcd.params[i].var>>] \o
                  [i \in 1..Len(prcd.decls) |->
                     <<prcd.decls[i].var, "|->", prcd.decls[i].var>>],
                ",") \o
  <<"]">>

SavePrcdVarOnStack(returnTo, prcd) ==
  (*************************************************************************)
  (* An assignment statement                                               *)
  (*                                                                       *)
  (*   @stack@ := << CallStackHead(returnTo, prcd) >> \o @stack@           *)
  (*                                                                       *)
  (* to push the parameters and local variables of a called procedure prcd *)
  (* on the head of the stack.                                             *)
  (*                                                                       *)
  (* Note: returnTo should be an expression, so if it's a label it should  *)
  (* be quoted.                                                            *)
  (*************************************************************************)
  [type |-> "assignment", 
   ass  |-> <<[lhs |-> [var |-> "@stack@", sub |-> << >>],
               rhs |-> <<"<<">> \o CallStackHead(returnTo, prcd)  \o 
                        <<">>", "\\o", "@stack@">> ] >>]

SavePrcdVarOnHeadOfStack(returnTo, prcd) ==
  (*************************************************************************)
  (* An assignment statement                                               *)
  (*                                                                       *)
  (*    @stack@[1] := CallStackHead(returnTo, prcd)                        *)
  (*                                                                       *)
  (* to save the parameters and local variables of a called procedure prcd *)
  (* in the head of the stack, overwriting the head's previous contents.   *)
  (*                                                                       *)
  (* Note: returnTo should be an expression, so if it's a label it should  *)
  (* be quoted.                                                            *)
  (*************************************************************************)
  [type |-> "assignment", 
   ass  |-> <<[lhs |-> [var |-> "@stack@", sub |-> <<"[", "1", "]" >>],
               rhs |-> CallStackHead(returnTo, prcd)  ] >> ]

AlmostRestoreVarsFromStack(prcd) ==
  (*************************************************************************)
  (* A single multiple-assignment statement to restore the parameters and  *)
  (* local variables of procedure prcd from the head of the stack, but not *)
  (* to change pc or `stack'.                                              *)
  (*************************************************************************)
  [type |-> "assignment",
   ass  |-> [i \in 1..Len(prcd.params) |->
               [lhs |->  [var |-> prcd.params[i].var, sub |-> << >>],
                rhs |-> <<"Head", "(", "@stack@", ")", ".", 
                            prcd.params[i].var>>] ] \o

            [i \in 1..Len(prcd.decls) |->
               [lhs |->  [var |-> prcd.decls[i].var, sub |-> << >>],
                rhs |-> <<"Head", "(", "@stack@", ")", ".", 
                            prcd.decls[i].var>>] ] ]

RestoreVarsFromStack(prcd) ==
  (*************************************************************************)
  (* A single multiple-assignment statement to set pc and restore the      *)
  (* parameters and local variables of procedure prcd from the top of the  *)
  (* stack, and to remove the head of the stack.                           *)
  (*************************************************************************)
  [type |-> "assignment",
   ass  |-> << [lhs |->  [var |-> "@stack@", sub |-> << >>],
                rhs |-> <<"Tail", "(", "@stack@", ")">>],

               [lhs |->  [var |-> "@pc@", sub |-> << >>],
                rhs |-> <<"Head", "(", "@stack@", ")", ".", "pc">>] >> \o

            [i \in 1..Len(prcd.params) |->
               [lhs |->  [var |-> prcd.params[i].var, sub |-> << >>],
                rhs |-> <<"Head", "(", "@stack@", ")", ".", 
                            prcd.params[i].var>>] ] \o

            [i \in 1..Len(prcd.decls) |->
               [lhs |->  [var |-> prcd.decls[i].var, sub |-> << >>],
                rhs |-> <<"Head", "(", "@stack@", ")", ".", 
                            prcd.decls[i].var>>] ] ]

  
-----------------------------------------------------------------------------
(***************************************************************************)
(*                       Parameters of the Operators                       *)
(*                                                                         *)
(* Because of the recursive nature of the AST of an algorithm, many of     *)
(* the operators used in defining the translation definition must be       *)
(* defined recursively.  Because we cannot recursively define operators    *)
(* within a LET, those operators require many arguments.  For example, we  *)
(* might have                                                              *)
(*                                                                         *)
(*   RECURSIVE Foo(_, _), Bar(_, _)                                        *)
(*   Foo(A, B) == ...                                                      *)
(*   Bar(A, C) == ..                                                       *)
(*                                                                         *)
(* where argument A of an operator Foo is within the definition of Foo     *)
(* only in an expression Bar(A, ...).  If the definitions of Foo and Bar   *)
(* can be put in a LET, then the argument A of both operators can be       *)
(* eliminated by writing                                                   *)
(*                                                                         *)
(*   LET A == ...                                                          *)
(*       RECURSIVE Foo(_), Bar(_)                                          *)
(*       Foo(B) == ...                                                     *)
(*       Bar(C) == ...                                                     *)
(*                                                                         *)
(* But our trick for simulating recursion with TLC doesn't work inside a   *)
(* LET, so we can't do that here.  Therefore, we have lots of arguments to *)
(* keep track of.  To help, we use the same name to denote corresponding   *)
(* argument of different operators--just as in this little example, we     *)
(* used the same parameter name A in the definitions of both Foo and Bar.  *)
(*                                                                         *)
(* Here are the meanings for the arguments represented by some parameter   *)
(* names in the operators defined below.                                   *)
(*                                                                         *)
(*    localVars  : The set of all variables that should be subscripted,    *)
(*                 where a subscript is something like "[self]"            *)
(*                 appended to an occurrence of a variable.                *)
(*                                                                         *)
(*    sub        : The expression to be added as a subscript to the        *)
(*                 variables in localVars.                                 *)
(*                                                                         *)
(*    scopeVars  : The set of all variables declared in the current        *)
(*                 scope of the +cal algorithm.                            *)
(*                                                                         *)
(*    primedVars : The set of variables in an expression that should be    *)
(*                 primed.                                                 *)
(*                                                                         *)
(*    nextLabel  : The next location to which control should go in the     *)
(*                 absence of a call, return, or goto.                     *)
(***************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                      Adding Subscripts and Primes                       *)
(*                                                                         *)
(* We now define the operators used to modify an expression to add a       *)
(* subscript to local variables in a multiprocess algorithm, and to prime  *)
(* occurrences of variables.                                               *)
(*                                                                         *)
(* We first recursively define AddSub(expr, localVars, sub) to be the      *)
(* expression obtained from expr by inserting the expression sub           *)
(* immediately after each occurrence of a variable in the set localVars.   *)
(* The tricky part of the definition is distinguishing a variable from a   *)
(* record-field name or a quoted string.  This is done by the rule that    *)
(* the expression sub should not be inserted after an identifier that      *)
(* occurs in any of the following contexts:                                *)
(*                                                                         *)
(*   - Preceded and followed by "\""                                       *)
(*                                                                         *)
(*   - Preceded by "."                                                     *)
(*                                                                         *)
(*   - Preceded by "[" or "," and followed by ":" or "|->"                 *)
(***************************************************************************)
(*RECURSIVE*) CONSTANT AddSub(_, _, _)
XAddSub(expr, localVars, sub) ==
  IF expr = << >>
    THEN << >>
    ELSE CASE Head(expr) = "\"" ->
               IF Len(expr) < 3 
                 THEN ParserBug("Unmatched quote in expression "
                                  \o expr)
                 ELSE SubSeq(expr, 1, 3) \o
                       AddSub(SubSeq(expr, 4, Len(expr)), localVars, sub)
           [] Head(expr) = "."  ->
               IF Len(expr) < 2
                 THEN ParserBug("Expression ending with `.': " \o expr)
                 ELSE SubSeq(expr, 1, 2) \o
                       AddSub(SubSeq(expr, 3, Len(expr)), localVars, sub)
           [] Head(expr) \in {"[", ","} ->
               IF Len(expr) < 3
                 THEN ParserBug("Premature end of expression " \o expr)
                 ELSE IF expr[3] \in {":", "|->"}
                        THEN SubSeq(expr, 1, 3) \o 
                                AddSub(SubSeq(expr, 4, Len(expr)), 
                                         localVars, sub)
                         ELSE <<Head(expr)>> \o 
                                  AddSub(Tail(expr), localVars, sub)
           [] OTHER -> <<Head(expr)>> \o
                         (IF Head(expr) \in localVars THEN sub ELSE << >>) 
                         \o AddSub(Tail(expr), localVars, sub)


(***************************************************************************)
(* We now define PrimeAndAddSub(expr, localVars, sub, primedVars) to be    *)
(* the expression obtained from expression expr by first inserting the     *)
(* expression sub immediately after each occurrence of a variable in the   *)
(* set localVars, and then priming all occurrences of variables in         *)
(* primedVars.                                                             *)
(*                                                                         *)
(* Note: An explicit assignment to `stack' is treated as an assignment to  *)
(* @stack@.  This means that if PrimeAndAddSub is being called in a        *)
(* context in which instances of `stack' should be primed, then primedVars *)
(* will contain "@stack@", not "stack".  Because a call or return occurs   *)
(* at the end of a step, the assignment to @stack@ produced by the call or *)
(* return cannot cause an occurrence of `stack' in the original algorithm  *)
(* to be primed.                                                           *)
(***************************************************************************)
PrimeAndAddSub(expr, localVars, sub, primedVars) ==
  LET pV == primedVars \cup IF "@stack@" \in primedVars THEN {"stack"}
                                                        ELSE {}
  IN AddSub(AddSub(expr, localVars, sub), pV, <<"'">>)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            Translating Assignments                      *)
(*                                                                         *)
(* We now define the operator XLSingleAssignSeq for translating a sequence *)
(* of <SingleAssign> nodes.  It is applied to the `ass' field of an        *)
(* <Assign> node to translate an assignment statement.  However, it is     *)
(* also used to translate assignments constructed in the process of        *)
(* translating a call or return.  The value of the operator is a record    *)
(* with two fields:                                                        *)
(*                                                                         *)
(*    conjs      : The sequence of action conjuncts constituting the       *)
(*                 translation of the sequence of <SingleAssign> nodes.    *)
(*                                                                         *)
(*    primedVars : The set of variables assigned to by the sequence of     *)
(*                 assignments unioned with the value of the primedVars    *)
(*                 argument.  (This is useful for recursive applications.) *)
(***************************************************************************)

(*RECURSIVE*) CONSTANT XLSingleAssignSeq(_, _, _, _, _)
XXLSingleAssignSeq(seq, localVars, scopeVars, sub, primedVars) ==
  (*************************************************************************)
  (* The seq argument is the sequence of <SingleAssign> records; the other *)
  (* arguments are described above.                                        *)
  (*************************************************************************)
  LET (*********************************************************************)
      (* nxtVar == The variable of the first assignment of seq.            *)
      (*           (Report an error if it is in primedVars.)               *)
      (* nxtAss == The subsequence of seq containing all assignments to    *)
      (*           nxtVar.                                                 *)
      (* rest   == The subsequence of seq containing all elements not      *)
      (*           in nxtAss.                                              *)
      (*********************************************************************)
      nxtVar == LET var == seq[1].lhs.var
                IN IF var \in primedVars
                     THEN Error("Multiple assignment to variable " \o var)
                     ELSE IF var \notin scopeVars
                            THEN Error("Assignment to undeclared variable "
                                        \o var)
                            ELSE var
      nxtAss == LET Test(e) == e.lhs.var = nxtVar IN  SelectSeq(seq, Test)
      rest   == LET Test(e) == e.lhs.var # nxtVar IN  SelectSeq(seq, Test)

      (*********************************************************************)
      (* modNxtAss == The sequence of SingleAssign records obtained        *)
      (*              from nxtAss by appending the "subscript" sub         *)
      (*              after all occurrences of variables in                *)
      (*              localVars (including left-hand side                  *)
      (*              occurrences if nxtVar is in localVars) and           *)
      (*              priming all variables in primedVars that             *)
      (*              occur in right-hand side expressions.                *)
      (*                                                                   *)
      (*              Reports an error if nxtAss has more than one         *)
      (*              assignment and one of those assignments is not       *)
      (*              subscripted                                          *)
      (*********************************************************************)
      modNxtAss == 
        IF /\ Len(nxtAss) > 1
           /\ \E i \in 1..Len(nxtAss) : nxtAss[i].lhs.sub = << >>
          THEN Error("Multiple unsubscripted assignment to " \o nxtVar)
          ELSE [i \in 1..Len(nxtAss) |->
                 [lhs |-> [var |-> nxtVar,
                           sub |-> LET paSub == PrimeAndAddSub(
                                                  nxtAss[i].lhs.sub,
                                                  localVars, sub, primedVars)
                                   IN  IF nxtVar \in localVars 
                                         THEN sub \o paSub
                                         ELSE paSub ],
                  rhs |-> PrimeAndAddSub(nxtAss[i].rhs, localVars, 
                                           sub, primedVars)]]

      (*********************************************************************)
      (* XLnxtAss == The single action conjunct of the form                *)
      (*             `nxtVar' = ...'  that is the translation of           *)
      (*              modNxtAss.                                           *)
      (*********************************************************************)
      XLnxtAss == 
        IF (Len(modNxtAss) = 1) /\ (modNxtAss[1].lhs.sub = << >>)
          THEN <<nxtVar, "'",  "=">> \o  modNxtAss[1].rhs
          ELSE <<nxtVar, "'",  "=", "[", nxtVar, "EXCEPT" >> \o
                SepSeqConcat([i \in 1..Len(modNxtAss) |->
                               <<"!">> \o modNxtAss[i].lhs.sub \o
                               <<"=">> \o modNxtAss[i].rhs],
                             ",") \o <<"]">>

      (*********************************************************************)
      (* XLRest == The result of applying XLSingleAssignSeq recursively    *)
      (*           to `rest'.                                              *)
      (*********************************************************************)
      XLRest == XLSingleAssignSeq(rest, localVars, scopeVars, sub, primedVars)

  IN  IF seq = << >> THEN [conjs      |-> << >>,
                           primedVars |-> primedVars]
                     ELSE [conjs      |-> <<XLnxtAss>> \o XLRest.conjs,
                           primedVars |-> XLRest.primedVars]
-----------------------------------------------------------------------------
(***************************************************************************)
(*                             Setting pc                                  *)
(*                                                                         *)
(* When translating a step, the operator SetPC adds a conjunct assigning a *)
(* new value to pc iff the step does not explicitly transfer control with  *)
(* a goto, call, or return.                                                *)
(***************************************************************************)
SetPC(rcd, nextLabel, localVars, sub) ==
  (*************************************************************************)
  (* If rcd is a record with fields                                        *)
  (*                                                                       *)
  (*   conjs      : A sequence of action conjuncts.                        *)
  (*                                                                       *)
  (*   primedVars : A set of primed variables.                             *)
  (*                                                                       *)
  (* and the arguments localVars and sub have the meaning indicated above, *)
  (* then this equals the conjs field, with an extra conjunct assigning    *)
  (* `nextLabel' to @pc@ that is added iff @pc@ is not an element of the   *)
  (* primedVars field.  It is defined in terms of XLSingleAssignSeq.       *)
  (*************************************************************************)
  LET Assign == XLSingleAssignSeq(<<[lhs |-> [var |-> "@pc@", sub |-> << >>],  
                                     rhs |-> Quote(nextLabel)]>>,
                                  localVars, {"@pc@"}, sub, rcd.primedVars)
  IN  IF "@pc@" \in rcd.primedVars THEN rcd.conjs
                                   ELSE rcd.conjs \o Assign.conjs
-----------------------------------------------------------------------------
(***************************************************************************)
(*                        Some Miscellaneous Operators                     *)
(***************************************************************************)
prcdVars(prcd) ==
  (*************************************************************************)
  (* The set of parameters and local variables of procedure prcd.          *)
  (*************************************************************************)
  {prcd.params[i].var : i \in 1..Len(prcd.params)} \cup 
  {prcd.decls[i].var  : i \in 1..Len(prcd.decls)}    

procVars(proc) == {proc.decls[j].var : j \in 1..Len(proc.decls)}
  (*************************************************************************)
  (* The set of local variables of process proc.                           *)
  (*************************************************************************)
  
(***************************************************************************)
(* If seq is a sequence of strings, then CommaSeq(seq) is defined          *)
(* recursively to be the sequence with commas inserted between the         *)
(* strings.  Thus,                                                         *)
(*                                                                         *)
(*    CommaSeq( << "foo", "bar", "x" >> = << "foo", "," "bar", ",", "x" >>  *)
(***************************************************************************)
(*RECURSIVE*) CONSTANT CommaSeq(_)
XCommaSeq(seq) ==
  IF Len(seq) = 1 THEN seq
                  ELSE <<Head(seq), ",">> \o CommaSeq(Tail(seq))

hasPrcds == ast.prcds # << >>
  (*************************************************************************)
  (* True iff the algorithm contains one or more procedures (which implies *)
  (* that the translation declares the variable `stack').                  *)
  (*************************************************************************)
  
preDefsVars  == 
  (*************************************************************************)
  (* If there is a `defines' section, then this is the sequence of TLA+    *)
  (* variables that should be declared before that section.                *)
  (*************************************************************************)
   [i \in  1..Len(ast.decls) |-> ast.decls[i].var] \o 
      <<"@pc@">> \o IF hasPrcds THEN <<"@stack@">> ELSE << >>

postDefsVars == 
  (*************************************************************************)
  (* If there is a `defines' section, then this is the sequence of TLA+    *)
  (* variables that should be declared after that section.                 *)
  (*************************************************************************)
  SeqConcat([i \in  1..Len(ast.prcds) |-> 
               [j \in 1..Len(ast.prcds[i].params) |->  
                            ast.prcds[i].params[j].var] \o 
               [j \in 1..Len(ast.prcds[i].decls) |-> 
                            ast.prcds[i].decls[j].var]]) 
    \o IF isMP THEN SeqConcat([i \in 1..Len(ast.procs) |-> 
                                   [j \in 1..Len(ast.procs[i].decls) |->
                                      ast.procs[i].decls[j].var]])
               ELSE << >>

varSeq == preDefsVars \o postDefsVars
  (*************************************************************************)
  (* The sequence of all TLA+ variables.                                   *)
  (*************************************************************************)

(***************************************************************************)
(* The following two operators are used to construct UNCHANGED conjuncts.  *)
(* Note that the variables in the UNCHANGED appear in the same order as in *)
(* allVars.                                                                *)
(***************************************************************************)
UC(vars) ==
  (*************************************************************************)
  (* A sequence containing either one element, which is an UNCHANGED       *)
  (* conjunct for all variables in vars, which should be a subset of the   *)
  (* variables in the sequence varSeq.                                     *)
  (*************************************************************************)
  LET ucVars == SetToSubseq(vars, varSeq)
  IN  IF ucVars = << >> 
        THEN << >>
        ELSE << <<  "UNCHANGED", "<<" >> \o CommaSeq(ucVars) \o << ">>" >>
             >>
UCExcept(vars) ==
  (*************************************************************************)
  (* A sequence containing either one element, which is an UNCHANGED       *)
  (* conjunct for all variables in varSeq NOT in vars, or else the empty   *)
  (* sequence if vars contains all variables in varSeq.                    *)
  (*************************************************************************)
  LET ucVars == CompSetToSubseq(vars, varSeq)
  IN  IF ucVars = << >> 
        THEN << >>
        ELSE << <<  "UNCHANGED", "<<" >> \o CommaSeq(ucVars) \o << ">>" >>
             >>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                        Translating Statements                           *)
(*                                                                         *)
(* We recursively define the operator XLLabeledStmtSeq that translates a   *)
(* sequence of <LabeledStmt> nodes.  Its value is a sequence of            *)
(* labeled-actions, where a labeled action is a record                     *)
(*                                                                         *)
(*    [label |-> lab, action |-> Act]                                      *)
(*                                                                         *)
(* where Act is the TLA+ action (an <Expr>) that is the translation of     *)
(* the +cal algorithm step beginning at label lab.                         *)
(*                                                                         *)
(* XLLabeledStmtSeq is defined in terms of two other recursively-defined   *)
(* operators XLUnlabStmt and XLUnlabStmtSeq, which translate an            *)
(* UnlabeledStatement and a sequence of UnlabeledStatements, respectively. *)
(* An UnlabeledStatement is any AST node that represents a statement other *)
(* than a <While> or <LabeledStmt> node.  The value of each of these two   *)
(* operators is a record with fields.                                      *)
(*                                                                         *)
(*   conjs        : The sequence of conjuncts produced by the sequence.    *)
(*                                                                         *)
(*   primedVars   : The set of variables that occur primed in those        *)
(*                  conjuncts unioned with the primedVars argument.        *)
(*                  (Useful for recursive application.)                    *)
(*                                                                         *)
(*   innerActions : A sequence of records with `label' and `action'        *)
(*                  fields produced as a result of using                   *)
(*                  XLLabeledStmtSeq to translate any labeled statements   *)
(*                  nested within the UnlabeledStatement(s).               *)
(***************************************************************************)
(*RECURSIVE*) CONSTANT XLUnlabStmt(_, _, _, _, _, _),  
                       XLUnlabStmtSeq(_, _, _, _, _, _),  
                       XLLabeledStmtSeq(_, _, _, _, _)

XXLUnlabStmtSeq(seq, nextLabel, localVars, 
                   scopeVars, sub, primedVars) ==   
  (*************************************************************************)
  (* As described immediately above, translates a sequence seq of          *)
  (* UnlabeledStatements.  The other arguments are the standard ones       *)
  (* described above.                                                      *)
  (*************************************************************************)
  LET xlfirst == XLUnlabStmt(seq[1], nextLabel, localVars, scopeVars, sub, 
                             primedVars)
      xlrest  == XLUnlabStmtSeq(Tail(seq), nextLabel, localVars, scopeVars, 
                                sub, xlfirst.primedVars)
  IN  IF seq = << >>
        THEN [conjs        |-> << >>,
             primedVars   |-> primedVars,
             innerActions |-> << >> ]
        ELSE [conjs        |-> xlfirst.conjs \o xlrest.conjs,
              primedVars   |-> xlrest.primedVars,
              innerActions |-> xlfirst.innerActions \o xlrest.innerActions]


(***************************************************************************)
(* We next define the operators that XLUnlabStmt calls to translate If and *)
(* Either statements.                                                      *)
(***************************************************************************)
XLIf(stmt, nextLabel, localVars, scopeVars, sub, primedVars,
     thenNext, elseNext) == 
  (*************************************************************************)
  (* Perform XLUnlabStmt for a statement of type "if".  The thenNext and   *)
  (* elseNext arguments are the nextLabel arguments for the `then' and     *)
  (* `else' clauses.  They will be different iff XLIf is called to process *)
  (* a LabelIf, in which case the THEN and ELSE clauses of the resulting   *)
  (* action must set pc.                                                   *)
  (*************************************************************************)
  LET test == PrimeAndAddSub(stmt.test, localVars, sub, primedVars)
      then == XLUnlabStmtSeq(stmt.then, thenNext, localVars, 
                             scopeVars, sub, primedVars)
      else == XLUnlabStmtSeq(stmt.else, elseNext, localVars, 
                             scopeVars, sub, primedVars)
      (*********************************************************************)
      (* `final' equals true iff the THEN and ELSE clauses must set pc.    *)
      (*********************************************************************)
      final == \/ thenNext # elseNext
               \/ "@pc@" \in (then.primedVars \cup else.primedVars)
      thenC == (IF final THEN SetPC(then, thenNext, localVars, sub)
                         ELSE then.conjs) 
                 \o UC(else.primedVars \ (then.primedVars \cup {"@pc@"}))
      elseC == (IF final THEN SetPC(else, elseNext, localVars, sub)
                         ELSE else.conjs) 
                 \o UC(then.primedVars \ (else.primedVars \cup {"@pc@"}))

  IN  [conjs        |-> << <<"IF">> \o test 
                               \o <<"THEN">> \o MakeConj(thenC) 
                               \o <<"ELSE">> \o MakeConj(elseC) >>,
       primedVars   |-> then.primedVars \cup else.primedVars
                                     \cup IF final THEN {"@pc@"} ELSE {},
       innerActions |-> then.innerActions \o else.innerActions]

XLEither(stmt, nextLabel, localVars, scopeVars, sub, primedVars,
         nextSeq) == 
  (*************************************************************************)
  (* Perform XLUnlabStmt for a statement of type "either".  The nextSeq    *)
  (* argument is a sequence of nextLabel arguments for the `or' clauses,   *)
  (* which must have the same length as stmt.ors.  These labels will not   *)
  (* all be identical iff XLEither is called to process a LabelEither, in  *)
  (* the translation must make all the clauses must set pc.                *)
  (*************************************************************************)
  LET or(i) == XLUnlabStmtSeq(stmt.ors[i], nextSeq[i], localVars, 
                              scopeVars, sub, primedVars)
      allPrimed == UNION {or(i).primedVars : i \in 1..Len(stmt.ors)}
      (*********************************************************************)
      (* `final' equals true iff the `or' clauses must set pc.             *)
      (*********************************************************************)
      final  == \/ \E i \in 2..Len(nextSeq) : nextSeq[i] # nextSeq[1] 
                \/ "@pc@" \in allPrimed
      orC(i) == MakeConj((IF final THEN SetPC(or(i), nextSeq[i], localVars, 
                                             sub)
                                   ELSE or(i).conjs)
                          \o UC(allPrimed \ (or(i).primedVars \cup {"@pc@"})))

  IN  [conjs        |-> << MakeDisj([i \in 1..Len(stmt.ors) |-> orC(i)]) >>,
       primedVars   |-> allPrimed \cup IF final THEN {"@pc@"} ELSE {},
       innerActions |-> SeqConcat([i \in 1..Len(stmt.ors) |-> 
                                    or(i).innerActions]) ]

XXLUnlabStmt(stmt, nextLabel, localVars, scopeVars, sub, primedVars) ==  
  (*************************************************************************)
  (* As explained above, translates an UnlabeledStatement other than a     *)
  (* `while' and produces a record with the following fields.              *)
  (*                                                                       *)
  (*   conjs        : The sequence of conjuncts produced translating       *)
  (*                  the sequence.                                        *)
  (*                                                                       *)
  (*   primedVars   : The set of variables that occur primed in those      *)
  (*                  conjuncts unioned with the primedVars argument.      *)
  (*                                                                       *)
  (*   innerActions : A sequence of records with `label' and `action'      *)
  (*                  fields produced as a result of translating any       *)
  (*                  labeled statements nested within stmt.               *)
  (* This is defined as a big CASE statement, with one case for every type *)
  (* of UnlabeledStatement node.                                           *)
  (*************************************************************************)
  LET (*********************************************************************)
      (* We define some abbreviations of some frequently called operators  *)
      (* to avoid having to type all their standard arguments.             *)
      (*********************************************************************)
      XLexpr(expr) == PrimeAndAddSub(expr, localVars, sub, primedVars)
      XLulSeq(seq, nxt) == XLUnlabStmtSeq(seq, nextLabel, localVars, 
                                          scopeVars, sub, primedVars) 
      XLlabSeq(seq) == XLLabeledStmtSeq(seq, nextLabel, localVars, scopeVars,
                                       sub)

  IN  CASE 
       (********************************************************************)
       (* Higher-Level Statements                                          *)
       (* ^^^^^^^^^^^^^^^^^^^^^^^                                          *)
       (* These statements are translated in a straightforward way by      *)
       (* recursively calling PrimeAndAddSub (XLexpr), XLUnlabStmtSeq      *)
       (* (XLulSeq), and XLLabeledStmtSeq (XLlabSeq).                      *)
       (********************************************************************)
           stmt.type = "if" -> 
            XLIf(stmt, nextLabel, localVars, scopeVars, sub, 
                 primedVars, nextLabel, nextLabel) 
        [] stmt.type = "labelIf" -> 
             LET ulIf   == [type |-> "if",
                            test |-> stmt.test,
                            then |-> stmt.unlabThen,
                            else |-> stmt.unlabElse]
                 thenNext == IF stmt.labThen = << >> 
                               THEN nextLabel
                               ELSE stmt.labThen[1].label
                 elseNext == IF stmt.labElse = << >> 
                               THEN nextLabel
                               ELSE stmt.labElse[1].label
                 XLulIf == XLIf(ulIf, nextLabel, localVars, scopeVars, 
                                sub, primedVars, thenNext, elseNext)
             IN  [XLulIf EXCEPT !.innerActions = XLulIf.innerActions
                                                  \o XLlabSeq(stmt.labThen)
                                                   \o XLlabSeq(stmt.labElse)]

        [] stmt.type = "either" -> 
             XLEither(stmt, nextLabel, localVars, scopeVars, sub, primedVars, 
                      [i \in 1..Len(stmt.ors) |-> nextLabel])

        [] stmt.type = "labelEither" -> 
             LET ulEither == [type |-> "either",
                              ors  |-> [i \in 1..Len(stmt.clauses) |->
                                         stmt.clauses[i].unlabOr]]
                 nextSeq  == [i \in 1..Len(stmt.clauses) |->
                               IF stmt.clauses[i].labOr = << >>
                                 THEN nextLabel
                                 ELSE stmt.clauses[i].labOr[1].label]
                 XLulEither == XLEither(ulEither, nextLabel, localVars, 
                                        scopeVars, sub, primedVars, 
                                        nextSeq)
             IN  [XLulEither EXCEPT !.innerActions =
                    XLulEither.innerActions \o
                      SeqConcat([i \in 1..Len(stmt.clauses) |->
                                         XLlabSeq(stmt.clauses[i].labOr)])]
        [] stmt.type = "with" -> 
             LET exp  == XLexpr(stmt.exp)
                 do   == XLulSeq(stmt.do, nextLabel)
                 conj == (IF stmt.eqOrIn = "="
                            THEN <<"LET", stmt.var, "==">> \o exp \o <<"IN">> 
                            ELSE <<"\\E", stmt.var, "\\in">> \o exp \o <<":">>)
                          \o MakeConj(do.conjs) 
             IN  [conjs        |-> << conj >>,
                  primedVars   |-> do.primedVars, 
                  innerActions |-> do.innerActions ]

        (*******************************************************************)
        (* Assignment Statement                                            *)
        (* ^^^^^^^^^^^^^^^^^^^^                                            *)
        (* Calls XLSingleAssignSeq to translate the statement's sequence of *)
        (* <SingleAssign> nodes.                                           *)
        (*******************************************************************)
        [] stmt.type = "assignment" ->
             LET xlAss == XLSingleAssignSeq(stmt.ass, localVars, scopeVars, 
                                            sub, primedVars)
             IN  [conjs        |-> xlAss.conjs,
                  primedVars   |-> 
                     xlAss.primedVars \cup
                       {IF stmt.ass[i].lhs.var = "stack"
                          THEN "@stack@" 
                          ELSE stmt.ass[i].lhs.var : i \in 1..Len(stmt.ass)},
                       (****************************************************)
                       (* As part of the method, explained earlier, to     *)
                       (* handle explicit references to `stack' in the     *)
                       (* algorithm, we allow an assignment to `stack' as  *)
                       (* a non-local variable, but we then consider the   *)
                       (* dummy variable `@stack@' to have been primed.    *)
                       (****************************************************)
                  innerActions |-> << >> ]

        (*******************************************************************)
        (* Call and Return Statements                                      *)
        (* ^^^^^^^^^^^^^^^^^^^^^^^^^^                                      *)
        (* <Call> and <Return> statements are translated in a              *)
        (* straight-forward way.  They use the operators like              *)
        (* SetPrcdVarsOnCall defined above to create an assignment         *)
        (* statement or sequence of assignment statements that set         *)
        (* procedure variables on a call or return and to modify the       *)
        (* stack.  They then use XLUnLabStmt or XLUnLabStmtSeq to          *)
        (* translate the assignment(s).  To translate a call, SetPC is     *)
        (* used to add the conjunct that modifies the pc.                  *)
        (*                                                                 *)
        (* The tricky part is translating the <CallReturn>, which          *)
        (* represents a call followed by a return in the same step.  In    *)
        (* this explanation, let's define the "variables of a procedure"   *)
        (* to consist of its local variables and its parameters.           *)
        (*                                                                 *)
        (* The translation is simple when the call is to the current       *)
        (* procedure.  Suppose the call is executed within an invocation i *)
        (* of procedure P to initiate invocation i+1 of P. In that case,   *)
        (* P's variables are set and the stack is left unchanged.          *)
        (* Executing a return from invocation i+1 then restores the        *)
        (* variables to the values they had immediately before the call of *)
        (* invocation i, and the return goes to the location from where    *)
        (* invocation i had been called.                                   *)
        (*                                                                 *)
        (* The case of a call from procedure P to a different procedure Q  *)
        (* is trickier.  The call must do the following.                   *)
        (*                                                                 *)
        (*  - Modify the head of the stack so it saves the current values  *)
        (*    of Q's variables, and saves as the return location the       *)
        (*    location to which the return from P should return.           *)
        (*                                                                 *)
        (*  - Set the variables of Q.  In the expressions to which the     *)
        (*    parameters of Q are set, the current values of P's           *)
        (*    variables must be used.                                      *)
        (*                                                                 *)
        (*  - Reset the variables of P to the values that had been saved   *)
        (*    on the stack when P was called, which were at the head of    *)
        (*    the stack, before the stack was changed in the first step.   *)
        (*                                                                 *)
        (* This requires that the current head of the stack be used in the *)
        (* third step after having been set in the first step.             *)
        (* Fortunately, that's not a problem in a TLA+ action, since an    *)
        (* unprimed occurrence of stack can come after the "stack' = ..."  *)
        (* conjunct.                                                       *)
        (*******************************************************************)
        [] stmt.type = "call" -> 
             LET prcd == NameToPrcd(stmt.to)
                 toLabel == prcd.body[1].label
                 xl == XLUnlabStmtSeq(
                         <<SavePrcdVarOnStack(Quote(nextLabel), prcd)>> \o
                            SetPrcdVarsOnCall(stmt, prcd),
                         "", (* nextLabel isn't used. *)
                         IF isMP THEN localVars \cup prcdVars(prcd) ELSE {}, 
                         scopeVars \cup prcdVars(prcd), 
                         sub, 
                         primedVars)
             IN [conjs        |-> SetPC(xl, toLabel, localVars, sub),
                 primedVars   |-> xl.primedVars \cup {"@pc@"}, 
                 innerActions |-> << >> ]

        [] stmt.type = "return" -> 
             LET prcd == NameToPrcd(stmt.from)
             IN  XLUnlabStmt(
                         RestoreVarsFromStack(prcd),
                         "",  (* nextLabel isn't used. *)
                         IF isMP THEN localVars \cup prcdVars(prcd) ELSE {}, 
                         scopeVars \cup prcdVars(prcd), 
                         sub, 
                         primedVars)

        [] stmt.type = "callReturn" ->  
             LET prcd == NameToPrcd(stmt.to) 
                 toLabel == prcd.body[1].label IN
             IF stmt.from = stmt.to
               THEN (*******************************************************)
                    (* The call is to the current procedure.               *)
                    (*******************************************************)
                    LET xl == XLUnlabStmtSeq(
                                SetPrcdVarsOnCall(stmt, prcd) ,
                                "", (* nextLabel isn't used. *)
                                IF isMP THEN localVars \cup prcdVars(prcd) 
                                        ELSE {}, 
                                scopeVars \cup prcdVars(prcd), 
                                sub, 
                                primedVars)
                    IN  [conjs        |-> SetPC(xl, toLabel, localVars, sub),
                         primedVars   |-> xl.primedVars \cup {"@pc@"}, 
                         innerActions |-> << >> ]
                     
               ELSE (*******************************************************)
                    (* The call is to a different procedure.               *)
                    (*******************************************************)
                    LET fromPrcd == NameToPrcd(stmt.from)
                        (***************************************************)
                        (* xl1 saves the current values of the parameters  *)
                        (* and local variables in the head of the stack,   *)
                        (* replacing the head's current value, and sets    *)
                        (* the parameters and local variables of the       *)
                        (* called procedure.                               *)
                        (***************************************************)
                        xl1 == XLUnlabStmtSeq(
                                 << SavePrcdVarOnHeadOfStack(
                                      <<"Head", "(", "@stack@", ")", ".", 
                                           "pc" >>,
                                      prcd) >> \o
                                   SetPrcdVarsOnCall(stmt, prcd) ,
                                 "", \* nextLabel isn't used.
                                 IF isMP THEN localVars \cup prcdVars(prcd) 
                                         ELSE {}, 
                                 scopeVars \cup prcdVars(prcd), 
                                 sub, 
                                 primedVars)

                       (****************************************************)
                       (* xl2 resets the parameters and local variables of *)
                       (* the current procedure from the head of the       *)
                       (* stack.  Note that because XLUnlabStmt is called  *)
                       (* with "@stack@" not in primedVars, it uses the    *)
                       (* original ("unprimed") value of the stack for     *)
                       (* this purpose.                                    *)
                       (****************************************************)
                       xl2 == XLUnlabStmt(
                                AlmostRestoreVarsFromStack(fromPrcd),
                                "", \* nextLabel isn't used.
                                IF isMP THEN localVars \cup prcdVars(fromPrcd) 
                                        ELSE {}, 
                                scopeVars \cup prcdVars(fromPrcd), 
                                sub, 
                                primedVars)
                    IN  [conjs        |-> xl1.conjs \o
                                          SetPC(xl2, toLabel, localVars, sub),
                         primedVars   |-> xl1.primedVars \cup xl2.primedVars
                                            \cup {"@pc@"}, 
                         innerActions |-> << >> ]

       (********************************************************************)
       (* Goto                                                             *)
       (* ^^^^                                                             *)
       (* A <Goto> statement is translated directly using the operator     *)
       (* SetPC.                                                           *)
       (********************************************************************)
        [] stmt.type = "goto" -> 
             [conjs        |-> SetPC([conjs |-> << >>, primedVars |-> {}], 
                                      stmt.to, localVars, sub),
              primedVars   |-> {"@pc@"} \cup primedVars, 
              innerActions |-> << >> ]

        (*******************************************************************)
        (* Very Simple Statements                                          *)
        (* ^^^^^^^^^^^^^^^^^^^^^^                                          *)
        (* The remaining statements are very simple, just generating a     *)
        (* single predicate containing the translation of their            *)
        (* expression--except for <Skip>, which has the null translation.  *)
        (*******************************************************************)
        [] stmt.type = "when" -> 
             [conjs        |-> << XLexpr(stmt.exp) >>,
              primedVars   |-> primedVars, 
              innerActions |-> << >> ]
        [] stmt.type = "print" ->
             [conjs        |-> << <<"PrintT", "(">> \o XLexpr(stmt.exp) 
                                    \o << ")">> >>,
              primedVars   |-> primedVars, 
              innerActions |-> << >> ]
        [] stmt.type = "assert" -> 
             [conjs        |-> << <<"Assert", "(">> \o XLexpr(stmt.exp) 
                                    \o <<",">> \o Quote("Assertion Failed")
                                    \o << ")">> >>,
              primedVars   |-> primedVars, 
              innerActions |-> << >> ]
        [] stmt.type = "skip" ->  
             [conjs        |-> << >>,
              primedVars   |-> primedVars, 
              innerActions |-> << >> ]

        [] OTHER -> SpecBug("Encountered unknown statement type " \o stmt.type)



XLLabeledStmt(stmt, nextLabel, localVars, scopeVars, sub) ==
  (*************************************************************************)
  (* Translates a <LabeledStmt>, producing a sequence of labeled-action    *)
  (* records, each having fields                                           *)
  (*                                                                       *)
  (*    label  : The label attached to the action.                         *)
  (*    action : The action.                                               *)
  (*                                                                       *)
  (* If the body contains no <While>, then the translation is performed by *)
  (* simply calling XLUnlabStmtSeq to translate the body and then calling  *)
  (* SetPC to add a conjunct to set the pc, if necessary.                  *)
  (*                                                                       *)
  (* If the body contains a <While>, which must be its first statement, then *)
  (* the translation produces a single TLA+ IF formula plus the translations *)
  (* obtained from the labeled statements within the <While>, in the node's *)
  (* labDo field.  The THEN clause of the IF formula is the translation of *)
  (* of the unlabDo field, containing the unlabeled statements at the      *)
  (* beginning of the `do' loop, with a conjunct to set the pc added by    *)
  (* SetPC if necessary.  The ELSE clause is the translation of the        *)
  (* UnlabeledStatments that follow the <While> in the body of the         *)
  (* <LabeledStmt>, again with a setting of pc added by SetPC if needed.   *)
  (*************************************************************************)
  LET pcTest == << "@pc@">> \o sub \o << "=" >> \o Quote(stmt.label)  IN
  IF Head(stmt.stmts).type = "while" 
    THEN LET test == PrimeAndAddSub(Head(stmt.stmts).test, localVars, sub, {}) 
             unlabDoNxt == IF Head(stmt.stmts).labDo = << >>
                             THEN stmt.label
                             ELSE Head(stmt.stmts).labDo[1].label
             unlabDo == XLUnlabStmtSeq
                          (Head(stmt.stmts).unlabDo, 
                           unlabDoNxt,
                           localVars, scopeVars, sub, {})
             labDo == XLLabeledStmtSeq(Head(stmt.stmts).labDo, 
                                       stmt.label, 
                                       localVars, scopeVars, sub) 
             rest == XLUnlabStmtSeq(Tail(stmt.stmts), 
                                    nextLabel, localVars, scopeVars, sub, 
                                    {})
         IN  << [label  |-> stmt.label,
                 action |-> <<"(">> \o pcTest \o <<")", "/\\", "(">> \o 
                            << "IF" >> \o test \o
                            << "THEN" >> \o 
                            MakeConj(SetPC(unlabDo, unlabDoNxt, 
                                            localVars, sub) \o
                                     UCExcept(unlabDo.primedVars 
                                              \cup {"@pc@"})) \o
                            << "ELSE" >> \o 
                            MakeConj(SetPC(rest, 
                                           nextLabel, localVars, sub) \o
                                     UCExcept(rest.primedVars 
                                              \cup {"@pc@"})) \o
                            <<")">> ]  >> 

             \o unlabDo.innerActions \o labDo \o rest.innerActions
                 

    ELSE LET body == XLUnlabStmtSeq(stmt.stmts, nextLabel, localVars, 
                                    scopeVars, sub, {})
         IN  << [label  |-> stmt.label,
                 action |-> MakeConj( <<pcTest>> \o 
                                      SetPC(body, 
                                           nextLabel, localVars, sub) \o
                                      UCExcept(body.primedVars 
                                              \cup {"@pc@"}))] >> 
             \o body.innerActions

XXLLabeledStmtSeq(seq, nextLabel, localVars, scopeVars, sub) ==  
  (*************************************************************************)
  (* Translates a sequence of <LabeledStmt>s by calling XLLabeledStmt and  *)
  (* recursively calling itself.  Its value is a sequence of records with  *)
  (* fields:                                                               *)
  (*                                                                       *)
  (*    label  : The label attached to the action.                         *)
  (*    action : The action.                                               *)
  (*************************************************************************)
  IF seq = << >> 
    THEN << >>
    ELSE XLLabeledStmt(Head(seq),
                       IF Len(seq) = 1 THEN nextLabel ELSE seq[2].label,
                       localVars, scopeVars, sub)
          \o
         XLLabeledStmtSeq(Tail(seq), nextLabel, localVars, scopeVars, sub)
-----------------------------------------------------------------------------
(***************************************************************************)
(*              THE DEFINITION OF Translation                              *)
(*                                                                         *)
(* We now put all the pieces together to define Translation to be the      *)
(* complete translation of the algorithm.                                  *)
(***************************************************************************)
Translation ==
  LET FixPCandStack(expr) ==
        (*******************************************************************)
        (* As explained above, the operators that translate statements us  *)
        (* the pseudo-identifiers "@pc@" and "@stack@" in place of "pc"    *)
        (* and "stack".  To perform the necessary final renaming, we       *)
        (* define FixPCandStack(expr) to be the expression obtained from   *)
        (* expr by replacing all instances of "@pc@" and "@stack@" by "pc" *)
        (* and "stack", respectively.  Instances in strings are ignored,   *)
        (* just in case the algorithm happens to use either of these       *)
        (* strings.  (We don't worry about their appearing in record-field *)
        (* names, because such names should not include the character      *)
        (* "@".)                                                           *)
        (*******************************************************************)
        [i \in 1..Len(expr) |-> 
          IF /\ (1 < i) /\ (i < Len(expr))
             /\ expr[i-1] = "\""
             /\ expr[i+1] = "\""
           THEN expr[i]
           ELSE CASE expr[i] = "@pc@"    -> "pc"
                  [] expr[i] = "@stack@" -> "stack"
                  [] OTHER               -> expr[i]  ]

      globalVars == SeqToSet(preDefsVars) \cup
                      IF hasPrcds THEN {"stack"} ELSE {}
        (*******************************************************************)
        (* The set of variables always in scope, used to check that an     *)
        (* assignment is made to a legal variable.  The variable "stack"   *)
        (* is included for variables with procedures, in case the          *)
        (* algorithm is assigning a value to it.                           *)
        (*******************************************************************)

      Defs(seq, sub) ==
        (*******************************************************************)
        (* If seq is a sequence of records with `label' and `action'       *)
        (* fields, as produced by XLLabeledStmtSeq, this equals the        *)
        (* sequence of definitions of the corresponding labeled actions,   *)
        (* where the expression sub is the definition's parameter, which   *)
        (* will be either "(self)" or empty.                               *)
        (*******************************************************************)
        SeqConcat([i \in 1..Len(seq) |-> 
                    <<seq[i].label>> \o sub \o <<"==">> \o seq[i].action] )

      DefDisj(seq, sub, id) ==
        (*******************************************************************)
        (* If seq is a sequence of records with `label' and `action'       *)
        (* fields, as produced by XLLabeledStmtSeq, this is the            *)
        (* defininition of id to equal the disjunction of all the labeled  *)
        (* actions, where the expression sub (either "(self)" or empty)    *)
        (* gives the definition's parameter.                               *)
        (*******************************************************************)
        <<id>> \o sub \o <<"==">> \o
          SepSeqConcat([i \in 1..Len(seq) |-> <<seq[i].label>> \o sub],
                       "\\/")
            (***************************************************************)
            (* We useSepSeqConcat here because there's no need for the     *)
            (* parentheses added by MakeDisj.                              *)
            (***************************************************************)


      Fairness(wsf) ==
        (*******************************************************************)
        (* The fairness condition for the algorithm if either "wf" or "sf" *)
        (* is specified, where the argument wsf is either "WF_vars" or     *)
        (* "SF_vars"                                                       *)
        (*******************************************************************)
        IF ast.type = "uniprocess"
          THEN << wsf, "(", "Next", ")" >>
          ELSE MakeConj( [i \in 1..Len(ast.procs) |->
                           IF ast.procs[i].eqOrIn = "="
                             THEN << wsf, "(", ast.procs[i].name , ")" >>
                             ELSE << "\\A", "self", "\\in">> 
                                    \o ast.procs[i].id 
                                    \o << ":",
                                      wsf, "(", ast.procs[i].name , 
                                                "(", "self", ")", ")" >>
                         ] \o
                         [i \in 1..Len(ast.prcds) |->  
                               <<"\\A", "self", "\\in", "ProcSet", ":", 
                                    wsf, "(", ast.prcds[i].name, 
                                         "(", "self", ")", ")" >>
                              
                         ] ) 

  IN (**********************************************************************)
     (* An outer application of FixPCandStack performs the substitutions   *)
     (* "@pc@" -> "pc" and "@stack@" -> "stack"                            *)
     (**********************************************************************)
     FixPCandStack(

      (*********************************************************************)
      (* Add a declaration of the constant defaultInitValue.               *)
      (* Added by LL on 22 Aug 2007.                                       *)
      (*********************************************************************)
      <<"CONSTANT", "defaultInitValue">> \o

      (*********************************************************************)
      (* The VARIABLES declaration(s) and the `define' section, if any.    *)
      (*********************************************************************)
      <<"VARIABLES">> \o 
      (IF ast.defs = << >>
         THEN CommaSeq(varSeq)
         ELSE CommaSeq(preDefsVars) \o ast.defs \o
              (IF postDefsVars # << >> 
                 THEN <<"VARIABLES">> \o CommaSeq(postDefsVars)
                 ELSE << >>)
      ) \o

      (*********************************************************************)
      (* The definition of the tuple vars of all variables.                *)
      (*********************************************************************)
      <<"vars", "==", "<<">> \o CommaSeq(varSeq) \o <<">>">> \o

      (*********************************************************************)
      (* For a multiprocess algorithm, the definition of ProcSet.  It is   *)
      (* the union of all process-set identifiers unioned with the set of  *)
      (* all single-process identifiers.                                   *)
      (*********************************************************************)
      (IF isMP
        THEN <<"ProcSet", "==">> \o
                (LET IsSet(proc)    == proc.eqOrIn # "="
                     IsNotSet(proc) == proc.eqOrIn = "="
                     setProcs    == SelectSeq(ast.procs, IsSet)
                     nonSetProcs == SelectSeq(ast.procs, IsNotSet)
                 IN  (IF setProcs # << >>
                        THEN SepSeqConcat([i \in 1..Len(setProcs) |->
                                            <<"(">> \o setProcs[i].id \o
                                            <<")">>],
                                          "\\cup") \o
                             (IF nonSetProcs # << >> THEN <<"\\cup">>
                                                     ELSE << >>)
                        ELSE << >>) 
                       \o
                     (IF nonSetProcs # << >>
                        THEN <<"{">> \o 
                             SepSeqConcat([i \in 1..Len(nonSetProcs) |->
                                             nonSetProcs[i].id],
                                          ",") \o <<"}">>
                        ELSE << >>) 
                 ) 

        ELSE << >>) \o

      (*********************************************************************)
      (* The definition of the initial predicate Init.                     *)
      (*********************************************************************)
      <<"Init", "==">> \o
        (********************************************************************)
        (* Init is a conjunction, with one conjunct for each TLA+ variable. *)
        (********************************************************************)
        MakeConj(
         (******************************************************************)
         (* The initialization of the global variables.                    *)
         (******************************************************************)
         [i \in 1..Len(ast.decls) |-> 
           <<ast.decls[i].var, ast.decls[i].eqOrIn>> \o ast.decls[i].val] \o

         (******************************************************************)
         (* The initialization of pc.                                      *)
         (******************************************************************)
         << <<"pc", "=">> \o
            (IF isMP
              THEN <<"[", "self", "\\in", "ProcSet", "|->", "CASE">> \o
                   SepSeqConcat([i \in 1..Len(ast.procs) |->
                                   <<"self", ast.procs[i].eqOrIn>> \o
                                   ast.procs[i].id \o <<"->">> \o
                                   Quote(ast.procs[i].body[1].label)],
                                "[]") \o
                   << "]" >>
              ELSE Quote(ast.body[1].label) ) >> \o
         
         (******************************************************************)
         (* The initialization of `stack'.                                 *)
         (******************************************************************)
         (IF hasPrcds THEN << <<"stack", "=">> \o
                              (IF isMP
                                 THEN << "[", "self", "\\in", "ProcSet", 
                                         "|->", "<<", ">>", "]" >>
                                 ELSE << "<<", ">>" >>) 
                           >>
            ELSE << >>) \o

         (******************************************************************)
         (* The initialization of procedure-parameter variables.           *)
         (******************************************************************)
         SeqConcat([i \in 1..Len(ast.prcds) |-> 
                     [j \in 1..Len(ast.prcds[i].params) |->
                        <<ast.prcds[i].params[j].var, "=">> \o
                        (IF isMP 
                           THEN <<"[", "self", "\\in", "ProcSet", "|->">> \o  
                                XAddSub(ast.prcds[i].params[j].val,
                                        prcdVars(ast.prcds[i]),
                                        <<"[", "self", "]">>)  \o << "]">>
                           ELSE ast.prcds[i].params[j].val  )]]) \o

         (******************************************************************)
         (* The initialization of local procedure variables.               *)
         (******************************************************************)
         SeqConcat([i \in 1..Len(ast.prcds) |-> 
                     [j \in 1..Len(ast.prcds[i].decls) |->
                        <<ast.prcds[i].decls[j].var, "=">> \o
                        (IF isMP 
                           THEN <<"[", "self", "\\in", "ProcSet", "|->">> \o  
                                XAddSub(ast.prcds[i].decls[j].val,
                                        prcdVars(ast.prcds[i]),
                                        <<"[", "self", "]">>)  \o << "]">>
                           ELSE ast.prcds[i].decls[j].val  )]]) \o
                  
         (******************************************************************)
         (* The initialization of local process variables.                 *)
         (*                                                                *)
         (* This is tricky for declarations of the form v \in exp.  For    *)
         (* example, consider                                              *)
         (*                                                                *)
         (*    process Proc \in S                                          *)
         (*    variables n = ... ; x = {1..n}; v \in x                     *)
         (*                                                                *)
         (* The initializations should be                                  *)
         (*                                                                *)
         (*     /\ n = ...                                                 *)
         (*     /\ x = [self \in Proc |-> {1..n[self]}]                    *)
         (*     /\ v \in [Proc -> x[some element in Proc]]                 *)
         (*                                                                *)
         (* To express the element in Proc, it would be nice to have an    *)
         (* operator AnyOf so we could just write AnyOf(Proc).  However,   *)
         (* rather than have to add this somewhere, we use the expression  *)
         (*                                                                *)
         (*    CHOOSE self \in Proc : TRUE                                 *)
         (*                                                                *)
         (* since we assume that `self' is not assigned a meaning.         *)
         (******************************************************************)
         (IF isMP
            THEN SeqConcat(
                   [i \in 1..Len(ast.procs) |-> 
                     [j \in 1..Len(ast.procs[i].decls) |->
                       << ast.procs[i].decls[j].var, 
                          ast.procs[i].decls[j].eqOrIn >> \o
                       (IF ast.procs[i].eqOrIn = "="
                          THEN ast.procs[i].decls[j].val
                          ELSE IF ast.procs[i].decls[j].eqOrIn = "="
                                THEN <<"[", "self", "\\in">> \o
                                     ast.procs[i].id \o <<"|->">> \o
                                     XAddSub(ast.procs[i].decls[j].val,
                                             procVars(ast.procs[i]),
                                             <<"[", "self", "]">>) \o <<"]">>
                                ELSE <<"[">> \o ast.procs[i].id \o 
                                     <<"->">> \o 
                                      XAddSub(ast.procs[i].decls[j].val,
                                             procVars(ast.procs[i]),
                                             <<"[", "CHOOSE", "self", 
                                               "\\in">> \o ast.procs[i].id
                                               \o <<":", "TRUE", "]">>) \o
                                     <<"]">> )]])
            ELSE << >>) 
           ) 
           (****************************************************************)
           (* End of definition of Init.                                   *)
           (****************************************************************)
          \o

         (******************************************************************)
         (* For each procedure, the definitions of the actions from the    *)
         (* translation of its body, followed by the definition of the     *)
         (* procedure's next-state action to be the disjunction of all     *)
         (* those actions.                                                 *)
         (******************************************************************)
         SeqConcat(
           [i \in 1..Len(ast.prcds) |->
             LET localVars == prcdVars(ast.prcds[i]) \cup {"@pc@", "@stack@"}
                 sub    == IF isMP THEN <<"[", "self", "]">> ELSE << >>
                 subD   == IF isMP THEN <<"(", "self", ")">> ELSE << >>
                 xlBody == XLLabeledStmtSeq(ast.prcds[i].body,
                                            "Error",
                                             IF isMP THEN localVars ELSE {},
                                             globalVars \cup localVars,
                                             sub)
             IN  Defs(xlBody, subD) \o 
                   DefDisj(xlBody, subD, ast.prcds[i].name)]
          ) \o  

        (*******************************************************************)
        (* The definition of Next, the next-state action.  It is preceded  *)
        (* by the definitions of the processes' actions for a multiprocess *)
        (* algorithm, or the definitions of the main body's actions for a  *)
        (* uniprocess algorithm.                                           *)
        (*******************************************************************)
        (IF isMP
           THEN (***********************************************************)
                (* For a Multiprocess Algorithm.                           *)
                (*                                                         *)
                (* For each process, the actions from the translation of   *)
                (* the process's body followed by the definition of the a  *)
                (* complete process action to be the disjunction of its    *)
                (* body's actions.  (This is not really the process's      *)
                (* next-state action because it does not describe steps    *)
                (* performed by the process when inside a procedure.)      *)
                (***********************************************************)
                SeqConcat(
                  [i \in 1..Len(ast.procs) |->
                    LET localVars == procVars(ast.procs[i]) \cup {"@pc@"} 
                                     \cup IF hasPrcds THEN {"@stack@"} ELSE {}
                        subVars == IF ast.procs[i].eqOrIn = "="
                                     THEN {"@pc@", "@stack@"}
                                     ELSE localVars
                        sub == IF ast.procs[i].eqOrIn = "="
                                 THEN <<"[">> \o ast.procs[i].id \o <<"]">>
                                 ELSE <<"[", "self", "]">>
                        subD == IF ast.procs[i].eqOrIn = "="
                                 THEN << >>
                                 ELSE <<"(", "self", ")">>
                        xlBody == XLLabeledStmtSeq(ast.procs[i].body,
                                                   "Done",
                                                    subVars,
                                                    localVars \cup globalVars,
                                                    sub)
                    IN  Defs(xlBody, subD) \o 
                        DefDisj(xlBody, subD, ast.procs[i].name) ] ) \o

                (***********************************************************)
                (* The next-state action Next.                             *)
                (***********************************************************)
                <<"Next", "==", "(">> \o

                (***********************************************************)
                (* The disjunction of the complete process actions.        *)
                (***********************************************************)
                SepSeqConcat(
                  (*********************************************************)
                  (* SepSeqConcat is used instead of MakeDisj because      *)
                  (* extra parentheses are not needed.                     *)
                  (*********************************************************)
                  [i \in 1..Len(ast.procs) |->
                    IF ast.procs[i].eqOrIn = "="
                      THEN <<ast.procs[i].name>>  
                      ELSE <<"(", "\\E", "self", "\\in">> \o
                           ast.procs[i].id \o 
                           <<":", ast.procs[i].name, "(", "self", ")", ")">>], 
                  "\\/") \o

                 (**********************************************************)
                 (* The disjunction of the procedure actions, if any.      *)
                 (**********************************************************)
                 (IF ~ hasPrcds
                    THEN << >>
                    ELSE <<"\\/", "(", "\\E", "self", "\\in",
                              "ProcSet", ":">> \o
                         SepSeqConcat([i \in 1..Len(ast.prcds)|-> 
                                        <<ast.prcds[i].name>> \o
                                        <<"(", "self", ")">> ],
                                      "\\/") \o 
                          << ")" >>) \o
                  << ")" >> \o

                  (*********************************************************)
                  (* The disjunct to prevent deadlock on termination.      *)
                  (*********************************************************)
                  <<"\\/", "(", "(", "\\A", "self", "\\in", "ProcSet", 
                     ":", "@pc@", "[", "self", "]", "=" >> \o 
                     Quote("Done") \o <<")", "/\\", "UNCHANGED", "vars", ")">> 

           ELSE (***********************************************************)
                (* For a Uniprocess Algorithm.                             *)
                (***********************************************************)
                LET xlBody == XLLabeledStmtSeq(ast.body,
                                               "Done",
                                               {},
                                               globalVars,
                                               << >>)
                IN  (*******************************************************)
                    (* The definitions of actions from the translation of  *)
                    (* the body.                                           *)
                    (*******************************************************)
                    Defs(xlBody, << >>) \o 

                    (*********************************************************)
                    (* Next == the disjunction of the actions from the body. *)
                    (*********************************************************)
                    DefDisj(xlBody, << >>, "Next") \o
                    (IF ~ hasPrcds 
                       THEN << >>
                       ELSE <<"\\/">> \o
                             SepSeqConcat([i \in 1..Len(ast.prcds)|-> 
                                           <<ast.prcds[i].name>>],
                                           "\\/")) \o
                   (********************************************************)
                   (* Disjunct to prevent deadlock on termination.         *)
                   (********************************************************)
                   <<"\\/", "(", "(","@pc@", "=" >> \o  Quote("Done") \o
                    <<")", "/\\", "UNCHANGED", "vars", ")">> 
         ) \o

        (*******************************************************************)
        (* The definition of the complete specification Spec.              *)
        (*******************************************************************)
        << "Spec", "==", "Init", "/\\", "[]", "[", "Next", "]_", "vars" >>
         \o
        (CASE fairness = ""       -> << >>
           [] fairness = "wf"     -> <<"/\\">> \o Fairness("WF_vars")
           [] fairness = "sf"     -> <<"/\\">> \o Fairness("SF_vars")
           [] fairness = "wfNext" -> << "/\\", "WF_vars", "(", "Next", 
                                         ")" >>) \o

        (*******************************************************************)
        (* The definition of the formula Termination.                      *)
        (*******************************************************************)
        << "Termination", "==", "<>", "(" >> \o 
        (IF ast.type = "uniprocess"  
           THEN << "@pc@", "=" >> 
           ELSE << "\\A", "self" , "\\in" , "ProcSet", ":", "@pc@", 
                   "[", "self", "]", "=" >> ) \o
        Quote("Done") \o <<")">>
    ) \* End of FixPCandStack

ASSUME 
  /\ PrintT("Begin checking")

     (**********************************************************************)
     (* Check if the ast is legal.                                         *)
     (**********************************************************************)
  /\ IF IsAlgorithm
       THEN TRUE
       ELSE ParserBug("AST of algorithm is incorrect")

     (**********************************************************************)
     (* Check the labels.                                                  *)
     (**********************************************************************)
  /\ CheckLabels
  /\ PrintT("AST OK")

     (**********************************************************************)
     (* Print the translation.                                             *)
     (**********************************************************************)
  /\ PrintT(Translation)
=============================================================================
Approximate length of spec (excluding comments)
   Part I   : 200 lines
   Part II  : 100 lines
   Part III : 685 lines
   Total    : 985 lines
