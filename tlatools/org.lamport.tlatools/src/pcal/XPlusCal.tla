last modified on Fri 23 Dec 2005 at 23:01:09 UT by lamport

------------------------------- MODULE XPlusCal ------------------------------
(***************************************************************************)
(* INTRODUCTION                                                            *)
(*                                                                         *)
(* This module specifies the translation from the abstract syntax tree of  *)
(* a (global-naming) +CAL algorithm to its TLA+ description.  The          *)
(* specification consists of two parts:                                    *)
(*                                                                         *)
(*   1. A specification of the grammar of an algorithm's abstract          *)
(*      syntax tree.                                                       *)
(*                                                                         *)
(*   2. The specification of an operator Translation such that             *)
(*      Translation(alg, fairnessOption) is a TLA+ specification of        *)
(*      the +CAL algorithm with abstract syntax tree alg, where            *)
(*      fairnessOption is one of:                                          *)
(*                                                                         *)
(*         ""       - No fainess condition.                                *)
(*         "wf"     - Weak fairness of all process actions.                *)
(*         "wfNext" - Weak fairness of entire next-state action.           *)
(*         "sf"     - Strong fairness of all process actions.              *)
(*                                                                         *)
(* For a uniprocess algorithm, "wf", "wfNext" and "sf", are all            *)
(* equivalent (strong and weak fairness are equivalent for a uniprocess    *)
(* algorithm).                                                             *)
(*                                                                         *)
(* The purpose of the specification is to serve as a partial spec of a     *)
(* algorithm to translate +CAL algorithms into TLA+.  It is not a complete *)
(* specification because:                                                  *)
(*                                                                         *)
(*  - It assumes that macro expansion has been performed.                  *)
(*                                                                         *)
(*  - It assume that all labels and variable names are distinct.  (The     *)
(*    translation program should rename labels and variables where         *)
(*    necessary to eliminate name collisions.)                             *)
(*                                                                         *)
(*  - It does not describe the formatting of the output.  Formulas that    *)
(*    the translation program should write for readability as              *)
(*                                                                         *)
(*       /\ A                                                              *)
(*       /\ ...                                                            *)
(*       /\ Z                                                              *)
(*                                                                         *)
(*    are instead written (A) /\ ...  /\ (Z).  Also, the formatting of     *)
(*    formulas that result from expressions in the algorithm is not        *)
(*    specified.  The translation program must preserve indentation in     *)
(*    such expressions both for readability and to maintain the meaning    *)
(*    of expressions that use TLA+'s conjunction/disjunction lists.        *)
(*                                                                         *)
(*  - It describes only the translation of algorithms that should be       *)
(*    successfully translated.  It does not specify when and how the       *)
(*    translation program should report errors.                            *)
(*                                                                         *)
(*  - It does not properly handle instances of `pc' and `stack' in         *)
(*    the a multiprocess algorithm.  (Instances occurring                  *)
(*    in the user algorithm have `self' subscripts added, when they        *)
(*    should not.                                                          *)
(*                                                                         *)
(* This specification should be modified as necessary to keep up with any  *)
(* changes to the +CAL language or how it should be translated.            *)
(*                                                                         *)
(* We assume that the reader is familiar with the text document describing *)
(* the +CAL language and the translation, titled "+CAL: A Programming      *)
(* Language for TLA+", herein referred to as the +CAL document.            *)
(*                                                                         *)
(* OUTPUT FORMATING                                                        *)
(*                                                                         *)
(* In the abstract syntax tree of a +CAL algorithm, a TLA+ expression is   *)
(* described as a sequence of lexemes, where a lexeme is a string.  The    *)
(* algorithm's TLA+ description is similarly described as a sequence of    *)
(* lexemes.  Missing from such a description is the two-dimensional        *)
(* aspect of TLA+.  In particular, a TLA+ expression such as               *)
(*                                                                         *)
(*     /\ C \/ D                                                           *)
(*     /\ E                                                                *)
(*                                                                         *)
(* is not described by the sequence `/\ C \/ D /\ E' of lexemes.  For      *)
(* Translation(alg, ...)  to produce a correct TLA+ specification, this    *)
(* TLA+ expression must be written as (C \/ D) /\ E.                       *)
(*                                                                         *)
(* This specification therefore omits an important part of the             *)
(* specification of an actual program to translate +CAL algorithms to its  *)
(* TLA+ version--namely, the precise formatting of the TLA+ version.       *)
(* Even if TLA+ expressions were not two-dimensional, the formatting of    *)
(* the output would be important because the user should be able to read   *)
(* and understand the output.  Formatting of the translation is discussed  *)
(* in the +CAL document.                                                   *)
(*                                                                         *)
(*                                                                         *)
(* ERRORS                                                                  *)
(*                                                                         *)
(* The definition of Translation is not a complete specification of        *)
(* an actual translation program because it does not adequately describe   *)
(* error detection and reporting.  Any +CAL algorithm text that satisfies  *)
(* the BNF grammar yields an abstract syntax tree.  However, the algorithm *)
(* and its syntax tree may have "semantic" errors such as declaring the    *)
(* same variable twice in the same context.  There are five ways errors in *)
(* a syntax tree `alg' could manifest itself in the definition of          *)
(* Translation(alg, ...).                                                  *)
(*                                                                         *)
(*   1. Translation(alg, ...) may contain a sequence of strings that       *)
(*      represents an error message rather than TLA+ -- for example:       *)
(*                                                                         *)
(*          Error : multiple assignemnt to variable var                    *)
(*                                                                         *)
(*   2. Translation(alg, ...) is undefined--more precisely, it equals      *)
(*      a "silly expression" (see Section 6.2, page 67 of the TLA+         *)
(*      book).  This means that TLC would report an error if it            *)
(*      tried to compute Translation(alg, ...).                            *)
(*                                                                         *)
(*   3. Translation(alg, ... ) is syntactically incorrect TLA+, so SANY    *)
(*      will complain when run on the output.                              *)
(*                                                                         *)
(*   4. Translation(alg, ...) will be syntactically correct TLA+ but will  *)
(*      produce an error when run by TLC.                                  *)
(*                                                                         *)
(*   5. Translation(alg, ...) will be syntactically correct TLA+ and will  *)
(*      be run without error by TLC, but will produce strange behavior.    *)
(*                                                                         *)
(* Errors of the first type are benign, since it is obvious from this      *)
(* specification how they can be detected and reported by a translation    *)
(* program.                                                                *)
(*                                                                         *)
(* All known errors of type 2 are clearly indicated in the specification   *)
(* and are similarly benign.  (They could be turned into type 1 errors,    *)
(* but this would complicate the specification.)  Other errors of type 2   *)
(* might exist; they could result in unexpected exceptions in a            *)
(* translation program.                                                    *)
(*                                                                         *)
(* Known errors of types 3-5 should be detected by a translation program   *)
(* Some of these errors can't be detected because they depend on other     *)
(* parts of the module containing the algorithm.  For example, the         *)
(* algorithm might declare a variable x when x is declared or defined      *)
(* elsewhere in the module.                                                *)
(*                                                                         *)
(* I know of the following type 3 errors:                                  *)
(*                                                                         *)
(*  - Most illegal multiple uses of the same identifier--for example,      *)
(*    two identical labels in the same procedure.                          *)
(*                                                                         *)
(* I know of the following errors that might produce type 4 or type 5      *)
(* errors.                                                                 *)
(*                                                                         *)
(*  - An algorithm or process variable initialized with non-constant       *)
(*    expressions.                                                         *)
(*                                                                         *)
(*  - A process or procedure using a variable that is local to             *)
(*    another process or procedure.                                        *)
(*                                                                         *)
(* There's a fuzzy line between type 5 errors and features that allow the  *)
(* user to take advantage of the translation to do things that could not   *)
(* be done with an ordinary programming language.  We'll probably have to  *)
(* decide on a case-by-case basis what should be considered an error       *)
(* rather than a feature.                                                  *)
(*                                                                         *)
(*                                                                         *)
(* EXECUTING THE SPECIFICATION WITH TLC                                    *)
(*                                                                         *)
(* The definitions were written so that they could be executed by TLC. In  *)
(* particular, TLC can, in principle, compute Translation(alg, ...  ) for  *)
(* any abstract syntax tree alg of a correct algorithm.  In practice, it   *)
(* probably can't do this for very complicated algorithms, where           *)
(* complexity is measured by how deeply nested the algorithm statements    *)
(* are.  Making the specification executable required doing some things in *)
(* a somewhat complicated way.  One such complication involves the         *)
(* representation of strings in TLA+ expressions.  Because TLC does not    *)
(* implement the TLA+ definition of a string as a sequence of characters,  *)
(* strings in a TLA+ expressions are represented in the following somewhat *)
(* strange way.  Recall that a TLA+ expression is represented in the       *)
(* abstract syntax tree and in the output as a sequence of strings, so     *)
(* `x+y' is represented as <<"x", "+", "y">>.  Recall also that special    *)
(* characters such as double-quote are preceded by a backslash when they   *)
(* appear in a string.  For example,                                       *)
(*                                                                         *)
(*    `. "\"x\\" .'                                                        *)
(* `~ Note: if you're reading this in the ASCII file rather than the       *)
(* output produced by TLATeX, ignore the strings `.  and .' , which are    *)
(* TLATeX formatting commands.  ~'                                         *)
(*                                                                         *)
(* is the string consisting of the three characters double-quote, x, and   *)
(* backslash.  In this specification, a string "foo" that appears in a     *)
(* TLA+ expression is represented by the sequence of three strings         *)
(*                                                                         *)
(*   `. "\""   "foo"   "\""  .'                                            *)
(*                                                                         *)
(* For example, the TLA+ expression `a["foo"]' is represented as           *)
(*                                                                         *)
(*   `. <<"a", "[", "\"", "foo", "\"", "]">> .'                            *)
(*                                                                         *)
(* There are also several hacks used in the specification to get around    *)
(* some TLC performance problems.  These are explained where they are      *)
(* first used.                                                             *)
(*                                                                         *)
(* CAVEAT                                                                  *)
(*                                                                         *)
(* This specification has not been carefully read or extensively tested.   *)
(* While it has been tested with a number of algorithms, that testing was  *)
(* not extensive enough to catch errors in corner cases.  Such errors      *)
(* undoubtedly exist.                                                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets , TLC, AST

-----------------------------------------------------------------------------
(***************************************************************************)
(*                          ABSTRACT SYNTAX TREES                          *)
(*                                                                         *)
(* We specify the set of all abstract syntax trees.  It closely follows    *)
(* the BNF grammar described in the "+CAL document.  A non-terminal node   *)
(* of the BNF such as `Process' corresponds to a set of records--namely,   *)
(* the set of all records that represent possible `Process' nodes in the   *)
(* abstract syntax tree corresponding to some +CAL algorithm.              *)
(*                                                                         *)
(* The construction of an abstract syntax tree from the algorithm text is  *)
(* a standard parsing problem, except that for simplicity we assume that   *)
(* the the following transformations have been made:                       *)
(*                                                                         *)
(*   - Every `elsif' construct has been removed and replaced with nested   *)
(*     `if/then/else' statements.                                          *)
(*                                                                         *)
(*   - Every `return' has associated with it the name of the               *)
(*     procedure from which it is returning.                               *)
(*                                                                         *)
(*   - A `call' followed by a `return' has been transformed into a single  *)
(*     combined `call/return' statement.                                   *)
(*                                                                         *)
(* For convenience, we assume an extra nonterminal CallOrReturn in the     *)
(* BNF grammar with the production                                         *)
(*                                                                         *)
(*   <<CallOrReturn>> ::= <<Call>> | <<Return>> | <<Call>> <<Return>>      *)
(*                                                                         *)
(* Also, we use PrintS and AssertS instead of `Print' and `Assert' to      *)
(* avoid conflict with the `Print' and `Assert' operators defined in the   *)
(* TLC module.                                                             *)
(*                                                                         *)
(* The following recursive equations explain the abstract syntax tree      *)
(* elements that correspond to the syntactic elements of the same name.  A *)
(* comparison of these equations with the corresponding BNF productions    *)
(* should explain the fields of the various records.  The definitions use  *)
(* the following operators:                                                *)
(***************************************************************************)

NonemptySeq(S) == Seq(S) \ {<< >>}
  (*************************************************************************)
  (* The set of nonempty sequences of elements of S.                       *)
  (*************************************************************************)
  
(***************************************************************************)
(* Here are the recursive definitions of the abstract syntax tree          *)
(* element, in the same order as the corresponding syntactic elements      *)
(* appear in the BNF grammar of +CAL. They use the following definitions:  *)
(*                                                                         *)
(*    PostPend(S, E) == {s \o <<e>> : s \in Seq(S), e \in E}               *)
(*                                                                         *)
(*    The set of all sequences obtained by appending an element of E to    *)
(*    the end of a sequence of elements in S. TLC cannot evaluate this     *)
(*    set because it is infinite.  But even if Seq(S) is replaced by a     *)
(*    finite set, TLC can evaluate it only by enumerating all elements of  *)
(*    this set and of E, which is usually infeasible.                      *)
(*                                                                         *)
(*                                                                         *)
(*    PostPend01(S, E) == PostPend(S, E) \cup Seq(S)                       *)
(*                                                                         *)
(*    The set of all sequences obtained by optionally appending an element *)
(*    of E to a sequence of elements in S.                                 *)
(*                                                                         *)
(* `.                                                                      *)
(*                                                                         *)
(* Algorithm  = [type   : {"uniprocess"},                                  *)
(*               name   : Name,                                            *)
(*               defs   : Expr,                                            *)
(*               decls  : Seq(VarDecl),                                    *)
(*               prcds  : Seq(Procedure),                                  *)
(*               body   : NonemptySeq(LabeledStmt)]                        *)
(*           \cup                                                          *)
(*            [type   : {"multiprocess"},                                  *)
(*             name   : Name,                                              *)
(*             decls  : Seq(VarDecl),                                      *)
(*             defs   : Expr,                                              *)
(*             prcds  : Seq(Procedure),                                    *)
(*             procs  : NonemptySeq(Process)]                              *)
(*                                                                         *)
(* Procedure = [name   : Name,                                             *)
(*              params : Seq(PVarDecl),                                    *)
(*              decls  : Seq(PVarDecl),                                    *)
(*              body   : Seq(LabeledStmt)]                                 *)
(*                                                                         *)
(* Process   = [name   : Name,                                             *)
(*              eqOrIn : {"=", "\\in"},                                    *)
(*              id     : Expr,                                             *)
(*              decls  : Seq(VarDecl),                                     *)
(*              body   : NonemptySeq(LabeledStmt)]                         *)
(*                                                                         *)
(* VarDecls  NOT DEFINED                                                   *)
(*                                                                         *)
(* VarDecl  = [var : Variable,  eqOrIn : {"=", "\\in"},  val : Expr]       *)
(*                                                                         *)
(* PVarDecls  NOT DEFINED                                                  *)
(*                                                                         *)
(* PVarDecl = [var : Variable,  eqOrIn : {"="}, val : Expr]                *)
(*    The val component is the initial value.  We assume that the parser   *)
(*    has added a default initialization if one is not specified.          *)
(*                                                                         *)
(* AlgorithmBody  NOT DEFINED                                              *)
(*                                                                         *)
(* LabeledStmt = [label : Label,                                           *)
(*                stmts : LabelSeq                                         *)
(*                          \cup                                           *)
(*                        {<<w>>> \o s : w \in While, s \in LabelSeq}      *)
(*                                                                         *)
(* While       = [type    : {"while"},                                     *)
(*                test    : Expr,                                          *)
(*                unlabDo : LabelSeq,                                      *)
(*                labDo   : Seq(LabeledStmt)]                              *)
(*                                                                         *)
(* LabelSeq    = PostPend01(SimpleStmt,                                    *)
(*                          LabelIf \cup LabelEither \cup FinalStmt)       *)
(*                                                                         *)
(* SimpleStmt  = Assign \cup If \cup Either \cup With \cup When            *)
(*                 \cup PrintS \cup AssertS \cup Skip                      *)
(*                                                                         *)
(*   Note: PrintS is used insteadof Print to avoid conflict with the TLC   *)
(*         Print operator                                                  *)
(*                                                                         *)
(* Assign = [type : {"assignment"},                                        *)
(*           ass  : NonemptySeq([lhs: LHS, rhs : Expr])]                   *)
(*                                                                         *)
(* LHS    = [var : Variable, sub : Expr]                                   *)
(*                                                                         *)
(* If     = [type : {"if"},                                                *)
(*           test : Expr,                                                  *)
(*           then : Seq(SimpleStmt)                                        *)
(*           else : Seq(SimpleStmt)]                                       *)
(*   Note: If is not explicitly defined, but is a subset of SimpleStmt.    *)
(*                                                                         *)
(* Either = [type : {"either"},                                            *)
(*           ors  : Seq(SimpleStmt)]                                       *)
(*   Note: Either is not explicitly defined, but is a subset of            *)
(*   SimpleStmt.                                                           *)
(*                                                                         *)
(* With   = [type   : {"with"},                                            *)
(*           var    : Variable,                                            *)
(*           eqOrIn : {"=", "\\in"},                                       *)
(*           exp    : Expr,                                                *)
(*           do     : NonemptySeq(SimpleStmt)]                             *)
(*   Note: With is not explicitly defined, but is a subset of SimpleStmt.  *)
(*                                                                         *)
(* When    = [type : {"when"},  exp : Expr]                                *)
(* PrintS  = [type : {"print"}, exp : Expr]                                *)
(* AssertS = [type : {"assert"}, exp : Expr]                               *)
(* Skip    = [type : {"skip"}]                                             *)
(*                                                                         *)
(* LabelIf     = [type      : {"labelIf"},                                 *)
(*                test      : Expr,                                        *)
(*                unlabThen : LabelSeq,                                    *)
(*                labThen   : Seq(LabeledStmt),                            *)
(*                unlabElse : LabelSeq,                                    *)
(*                labElse   : Seq(LabeledStmt)]                            *)
(*   Note: LabelIf is not explicitly defined, but is a subset of           *)
(*         LabeledStmt.                                                    *)
(*                                                                         *)
(* LabelEither = [type    : {"labelEither"},                               *)
(*                clauses : Seq([unlabOr : LabelSeq,                       *)
(*                               labOr   : Seq(LabeledStmt)])]             *)
(*   Note: LabelEither is not explicitly defined, but is a subset of       *)
(*         LabeledStmt.                                                    *)
(*                                                                         *)
(* FinalStmt   = FinalIf \cup FinalEither \cup FinalWith                   *)
(*                 \cup CallOrReturn \cup Goto                             *)
(*   Note: FinalStmt is not explicitly defined, but is a subset of         *)
(*         LabeledStmt.                                                    *)
(*                                                                         *)
(* FinalIf     = [type : {"if"},                                           *)
(*                test : Expr,                                             *)
(*                then : PostPend01(SimpleStmt, FinalStmt),                *)
(*                else : PostPend01(SimpleStmt, FinalStmt)]                *)
(*                                                                         *)
(* FinalEither = [type : {"either"},                                       *)
(*                ors  : Seq(PostPend01(SimpleStmt, FinalStmt))]           *)
(*                                                                         *)
(* FinalWith   = [type   : {"with"},                                       *)
(*                var    : Variable,                                       *)
(*                eqOrIn : {"=", "\\in"},                                  *)
(*                exp    : Expr,                                           *)
(*                do     : NonemptySeq(SimpleStmt)                         *)
(*                          \cup PostPend(SimpleStmt, FinalStmt)]          *)
(*                                                                         *)
(* Call = [type : {"call"}, returnTo : Label, to : Name, args : Seq(Expr)] *)
(*     The returnTo field holds the label of the statement to which the    *)
(*     called procedure should return.  This field is computed by          *)
(*     the translation and need not be filled in by the parser.            *)
(*                                                                         *)
(*     Note: Call is not explicitly defined, but is a subset of            *)
(*           CallOrReturn.                                                 *)
(*                                                                         *)
(* Return = [type : {"return"}, from : Name]                               *)
(*    The from field is the name of the procedure that the return is       *)
(*    returning from.  (There is no returnTo field because the label of    *)
(*    the statement to which the procedure returns is obtained from the    *)
(*    stack.)                                                              *)
(*                                                                         *)
(*    Note: Return is not explicitly defined, but is a subset of           *)
(*          CallOrReturn.                                                  *)
(*                                                                         *)
(* CallOrReturn = Call \cup Return \cup                                    *)
(*                 [type : {"callReturn"},                                 *)
(*                  from : Name,                                           *)
(*                  to   : Name,                                           *)
(*                  args : Seq(Expr)]                                      *)
(*    A record of type "callReturn" represents a Call immediately followed *)
(*    by a Return.                                                         *)
(*                                                                         *)
(* Goto = [type : {"goto"},                                                *)
(*         to   : Label]                                                   *)
(*                                                                         *)
(* Variable = STRING                                                       *)
(* Field    = STRING                                                       *)
(* Name     = STRING                                                       *)
(* Label    = STRING                                                       *)
(* Expr     = Seq(STRING)   .'                                             *)
(*                                                                         *)
(*                                                                         *)
(* Because TLA+ requires that symbols be defined before they are used, the *)
(* definitions appear in a bottom-up fashion rather than in the top-down   *)
(* order in which they appear above and in the BNF grammar.                *)
(***************************************************************************)

(***************************************************************************)
(* Some of the sets of ASTs require recursive definitions.  Instead        *)
(* of defining such a set S recursively, it is easier to define            *)
(* recursively a predicate IsS so that IsS(x) is true iff x is an element  *)
(* of S.  We then define                                                   *)
(*                                                                         *)
(*    S == {x \in Object : IsS(x)}                                         *)
(*                                                                         *)
(* where Object is an infinite set that includes all the ASTs in S. TLC    *)
(* will not be able to evaluate S, but it will be able to compute IsS(x)   *)
(* for any x that is an element of S. We now define Object to be the set   *)
(* of all objects consisting of strings, sequences of strings, and         *)
(* records whose components are all objects.                               *)
(*                                                                         *)
(* We will later define recursive functions with domain Object.  TLC will  *)
(* evaluate these by substituting `Any' for `Object', using a hack         *)
(* recently added to TLC.                                                  *)
(***************************************************************************)
Object ==
  LET RcdDomain == {S \in SUBSET STRING : IsFiniteSet(S)}
      Records(T) == UNION {[S -> T] : S \in RcdDomain}
      Obj[n \in Nat] == IF n = 0 THEN STRING \cup Seq(STRING)
                                 ELSE Obj[n-1] \cup Records(Obj[n-1])
  IN  UNION {Obj[n] : n \in Nat}

ErrorVal == CHOOSE x \in {} : FALSE
  (*************************************************************************)
  (* An expression whose value should never matter.  TLC will report an    *)
  (* error if it has to evaluate it.                                       *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the terminals Variable, Field, etc.  These are all        *)
(* strings.  For simplicity, we don't bother defining precisely what       *)
(* strings they can be.  (Although it is not hard to define those sets of  *)
(* strings in TLA+, TLC would not be able to cope with the definitions     *)
(* very well.)                                                             *)
(***************************************************************************)
Variable == STRING  \* variable names
Field    == STRING  \* record-component names
Name     == STRING  \* names of algorithms, processes, etc.
Label    == STRING  \* algorithm labels

Expr == Seq(STRING)
  (*************************************************************************)
  (* As explained above, a TLA+ expression is represented as a sequence of *)
  (* lexemes, each of which is a string.  It would be tedious and          *)
  (* pointless to specify exactly what sequences of lexemes are legal TLA+ *)
  (* formulas.  The +CAL grammar was designed so the translator does not   *)
  (* have to parse TLA+ expressions.                                       *)
  (*************************************************************************)
-----------------------------------------------------------------------------
Quote(id) == <<"\"", id, "\"" >>
  (*************************************************************************)
  (* If id is an identifier such as a `Label', then this is the Expr that  *)
  (* represents "id" -- that is, id as a quoted string.  This              *)
  (* representation of strings in expressions is explained above.          *)
  (*************************************************************************)

LHS == [var : Variable, sub : Expr]
  (*************************************************************************)
  (* The set of all left-hand sides of an assignment.  The left-hand side  *)
  (* x[i+1].r is represented by the record                                 *)
  (*                                                                       *)
  (*    [var |-> "x",                                                      *)
  (*     sub |-> << "[", "i", "+", "1", "]", ".", "r" >>]                  *)
  (*************************************************************************)

Assign == 
  (*************************************************************************)
  (* The set of (multiple) assignments.                                    *)
  (*************************************************************************)
  [type : {"assignment"}, 
   ass  : NonemptySeq([lhs: LHS, rhs : Expr])]

When    == [type : {"when"},  exp : Expr]
PrintS  == [type : {"print"}, exp : Expr]
AssertS == [type : {"assert"}, exp : Expr]
Skip    == [type : {"skip"}]
-----------------------------------------------------------------------------
IsRecord(r, D) == r = [x \in D |-> r[x]]
  (*************************************************************************)
  (* If D is a set of strings, then this is true iff r is a record with    *)
  (* set D of components.                                                  *)
  (*************************************************************************)

IsSeq(s) == DOMAIN s = 1..Len(s)
  (*************************************************************************)
  (* True if s is a sequence; TLC will evaluate it to true iff s is a      *)
  (* sequence.                                                             *)
  (*************************************************************************)
  
IsSimpleStmt(ss) ==
  (*************************************************************************)
  (* Here again are the mutually recursive equations that define the sets  *)
  (* SimpleStmt, With, and If                                              *)
  (*                                                                       *)
  (* `.                                                                    *)
  (*  SimpleStmt = Assign \cup When \cup PrintS \cup AssertS               *)
  (*                 \cup Skip With \cup If \cup Either                    *)
  (*                                                                       *)
  (*  With       = [type   : {"with"},                                     *)
  (*                var    : Variable,                                     *)
  (*                eqOrIn : {"=", "\\in"},                                *)
  (*                exp    : Expr,                                         *)
  (*                do     : NonemptySeq(SimpleStmt)]                      *)
  (*                                                                       *)
  (*  If         = [type : {"if"},                                         *)
  (*                test : Expr,                                           *)
  (*                then : Seq(SimpleStmt)                                 *)
  (*                else : Seq(SimpleStmt)]                                *)
  (*                                                                       *)
  (*  Either     = [type : {"either"},                                     *)
  (*                ors  : Seq(SimpleStmt)]                     .'         *)
  (*************************************************************************)
  LET ISS[tp \in {"SimpleStmt", "With", "If", "Either"},
          st \in Object] ==
            CASE tp = "SimpleStmt" -> 
                      \/ st \in Assign \cup When \cup PrintS \cup AssertS 
                                 \cup Skip
                      \/ ISS["With", st]
                      \/ ISS["If", st]
                      \/ ISS["Either", st]
            []   tp = "With"       -> 
                      /\ IsRecord(st, {"type", "var", "eqOrIn", "exp", "do"})
                      /\ st.type   = "with"
                      /\ st.var    \in Variable
                      /\ st.eqOrIn \in {"=", "\\in"}
                      /\ st.exp    \in Expr
                      /\ Len(st.do) > 0
                      /\ \A i \in 1..Len(st.do) : 
                            ISS["SimpleStmt", st.do[i]]
            []   tp = "If"         -> 
                      /\ IsRecord(st, {"type", "test", "then", "else"})
                      /\ st.type =  "if"
                      /\ st.test \in Expr
                      /\ \A i \in 1..Len(st.then) : 
                            ISS["SimpleStmt", st.then[i]]
                      /\ \A i \in 1..Len(st.else) : 
                            ISS["SimpleStmt", st.else[i]]
            []   tp = "Either"     ->
                      /\ IsRecord(st, {"type", "ors"})
                      /\ st.type =  "either"
                      /\ IsSeq(st.ors)
                      /\ \A n \in 1 .. Len(st.ors) :
                            \A i \in 1..Len(st.ors[n]) : 
                               ISS["SimpleStmt", st.ors[n][i]]

  IN  ISS["SimpleStmt", ss]

SimpleStmt == {o \in Object : IsSimpleStmt(o)}
-----------------------------------------------------------------------------

CallOrReturn == 
  (*************************************************************************)
  (* This is the set of records representing the BNF expression            *)
  (*   `.                                                                  *)
  (*      <Call>  |  <Return>  |  <Call> ; <Return>   .'                   *)
  (*                                                                       *)
  (* We assume that the parser has inserted the name of the procedure that *)
  (* a return is returning from.  For convenience, we let a `Call' node    *)
  (* contain a `returnTo' field that will be used to hold the label of the *)
  (* statement to which the called procedure should return.  However, this *)
  (* field will be computed; we do not assume that the parser inserts is.  *)
  (* (There is no corresponding field for a `Return' because the label of  *)
  (* the statement to which the procedure returns is obtained from the     *)
  (* stack.)                                                               *)
  (*************************************************************************)
        [type : {"return"},     from : Name]
   \cup [type : {"callReturn"}, from : Name,  to : Name, args : Seq(Expr)]
   \cup [type : {"call"},   returnTo : Label, to : Name, args : Seq(Expr)]

Goto == [type : {"goto"}, to : Label]

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the sets LabeledStmt, While, LabelSeq, LabelIf,           *)
(* LabelEither, FinalStmt, FinalIf, and FinalWith.                         *)
(* Recall that the recursive equations are as follows.  `.                 *)
(*                                                                         *)
(* LabeledStmt = [label : Label,                                           *)
(*                stmts : LabelSeq \cup                                    *)
(*                         {<<w>> \o s : w \in While, s \in LabelSeq}      *)
(*                                                                         *)
(* While       = [type    : {"while"},                                     *)
(*                test    : Expr,                                          *)
(*                unlabDo : LabelSeq,                                      *)
(*                labDo   : Seq(LabeledStmt)]                              *)
(*                                                                         *)
(* LabelSeq    = PostPend01(SimpleStmt,                                    *)
(*                          LabelIf \cup LabelEither \cup FinalStmt)       *)
(*                                                                         *)
(* LabelIf     = [type      : {"labelIf"},                                 *)
(*                test      : Expr,                                        *)
(*                unlabThen : LabelSeq,                                    *)
(*                labThen   : Seq(LabeledStmt),                            *)
(*                unlabElse : LabelSeq,                                    *)
(*                labElse   : Seq(LabeledStmt)]                            *)
(*                                                                         *)
(* LabelEither = [type    : {"labelEither"},                               *)
(*                clauses : Seq([unlabOr : LabelSeq,                       *)
(*                               labOr   : Seq(LabeledStmt)])]             *)
(*                                                                         *)
(* FinalStmt   = FinalIf \cup FinalWith \cup CallOrReturn \cup Goto        *)
(*                                                                         *)
(* FinalIf     = [type : {"if"},                                           *)
(*                test : Expr,                                             *)
(*                then : PostPend01(SimpleStmt, FinalStmt),                *)
(*                else : PostPend01(SimpleStmt, FinalStmt)]                *)
(*                                                                         *)
(* FinalEither = [type : {"either"},                                       *)
(*                ors  : Seq(PostPend01(SimpleStmt, FinalStmt))]           *)
(*                                                                         *)
(* FinalWith   = [type : {"with"},                                         *)
(*                var    : Variable,                                       *)
(*                eqOrIn : {"=", "\\in"},                                  *)
(*                exp    : Expr,                                           *)
(*                do     : NonemptySeq(SimpleStmt)                         *)
(*                          \cup Post(SimpleStmt, FinalStmt)]  .'          *)
(***************************************************************************)
Front(s) == SubSeq(s, 1, Len(s)-1)
  (*************************************************************************)
  (* The sequence obtained from s by removing the last element if it has   *)
  (* one.                                                                  *)
  (*************************************************************************)

IsSimpleStmtSeq(ss) == \A n \in 1..Len(ss) : IsSimpleStmt(ss[n])
  (*************************************************************************)
  (* True iff ss is a sequence of elements of SimpleStmt.                  *)
  (*************************************************************************)

IsStmt(type, stmt) == 
  (*************************************************************************)
  (* We define IsLabeledStmt, etc. in terms of the recursively-defined     *)
  (* operator IsStmt, where IsLabeledStmt(s) equals                        *)
  (* IsStmt("IsLabeledStmt", s), etc.                                      *)
  (*************************************************************************)
  LET IsT[tp \in {"LabeledStmt", "While", "LabelSeq", "LabelIf", 
                  "LabelEither", "FinalStmt", "FinalIf", "FinalEither", 
                  "FinalWith"},
          st \in Object] ==
        CASE tp = "LabeledStmt" -> 
               /\ IsRecord(st, {"label", "stmts"})
               /\ st.label \in Label
               /\ \/ /\ IsT["While", st.stmts[1]]
                     /\ IsT["LabelSeq", Tail(st.stmts)]
                  \/ IsT["LabelSeq", st.stmts]

        []   tp = "While" -> 
               /\ IsRecord(st, {"type", "test", "unlabDo", "labDo"})
               /\ st.type = "while"
               /\ st.test \in Expr
               /\ IsT["LabelSeq", st.unlabDo]
               /\ \A i \in 1..Len(st.labDo) : IsT["LabeledStmt", st.labDo[i]]

        []   tp = "LabelSeq" ->  
               \/ IsSimpleStmtSeq(st)
               \/ /\ Len(st) > 0
                  /\ IsSimpleStmtSeq(Front(st))
                  /\ \/ IsT["LabelIf", st[Len(st)]]
                     \/ IsT["LabelEither", st[Len(st)]]
                     \/ IsT["FinalStmt", st[Len(st)]]

        []   tp = "LabelIf" -> 
               /\ IsRecord(st, {"type", "test", "unlabThen", "labThen",
                                "unlabElse", "labElse"})
               /\ st.type = "labelIf"
               /\ st.test \in Expr
               /\ IsT["LabelSeq", st.unlabThen]
               /\ \A i \in 1..Len(st.labThen) :
                      IsT["LabeledStmt", st.labThen[i]]
               /\ IsT["LabelSeq", st.unlabElse]
               /\ \A i \in 1..Len(st.labElse) :
                      IsT["LabeledStmt", st.labElse[i]]

        []   tp = "LabelEither" ->
               /\ IsRecord(st, {"type", "clauses"})
               /\ st.type = "labelEither"
               /\ IsSeq(st.clauses)
               /\ \A n \in 1..Len(st.clauses) :
                     /\ IsRecord(st.clauses[n], {"unlabOr", "labOr"})
                     /\ IsT["LabelSeq", st.clauses[n].unlabOr]
                     /\ \A i \in 1..Len(st.clauses[n].labOr) :
                            IsT["LabeledStmt", st.clauses[n].labOr[i]]

        []   tp = "FinalStmt" ->
               \/ st \in (CallOrReturn \cup Goto)
               \/ IsT["FinalIf", st]
               \/ IsT["FinalEither", st]
               \/ IsT["FinalWith", st]

        []   tp = "FinalIf" -> 
               /\ IsRecord(st, {"type", "test", "then", "else"})
               /\ st.type = "if"
               /\ st.test \in Expr
               /\ \/ IsSimpleStmtSeq(st.then)
                  \/ /\ Len(st.then) > 0
                     /\ IsT["FinalStmt", st.then[Len(st.then)]]
                     /\ IsSimpleStmtSeq(Front(st.then))
               /\ \/ IsSimpleStmtSeq(st.else)
                  \/ /\ Len(st.else) > 0
                     /\ IsT["FinalStmt", st.else[Len(st.else)]]
                     /\ IsSimpleStmtSeq(Front(st.else))

        []   tp = "FinalEither" ->
               /\ IsRecord(st, {"type", "ors"})
               /\ st.type = "either"
               /\ IsSeq(st.ors)
               /\ \A n \in 1..Len(st.ors) :
                    \/ IsSimpleStmtSeq(st.ors[n])
                    \/ /\ Len(st.ors[n]) > 0
                       /\ IsT["FinalStmt", st.ors[n][Len(st.ors[n])]]
                       /\ IsSimpleStmtSeq(Front(st.ors[n]))

        []   tp = "FinalWith" -> 
               /\ IsRecord(st, {"type", "var", "eqOrIn", "exp", "do"})
               /\ st.type = "with"
               /\ st.var \in Variable
               /\ st.eqOrIn \in {"=", "\\in"}
               /\ st.exp \in Expr
               /\ Len(st.do) > 0
               /\ \/ IsSimpleStmtSeq(st.do) 
                  \/ /\ IsT["FinalStmt", st.do[Len(st.do)]]
                     /\ IsSimpleStmtSeq(Front(st.do))
  IN  IsT[type, stmt]

IsLabeledStmt(stmt) == IsStmt("LabeledStmt", stmt)
IsLabelSeq(stmt)    == IsStmt("LabelSeq", stmt)
IsFinalIf(stmt)     == IsStmt("FinalIf", stmt)
IsFinalEither(stmt) == IsStmt("FinalEither", stmt)
IsFinalWith(stmt)   == IsStmt("FinalWith", stmt)

LabeledStmt == {stmt \in Object : IsLabeledStmt(stmt)}
LabelSeq    == {stmt \in Object : IsLabelSeq(stmt)}
FinalIf     == {stmt \in Object : IsFinalIf(stmt)}
FinalEither == {stmt \in Object : IsFinalEither(stmt)}
FinalWith   == {stmt \in Object : IsFinalWith(stmt)}
-----------------------------------------------------------------------------
(***************************************************************************)
(* The remaining non-terminal definitions are all straightforward.         *)
(***************************************************************************)
VarDecl == [var : Variable,  eqOrIn : {"=", "\\in"},  val : Expr]

PVarDecl == [var : Variable,  eqOrIn : {"="}, val : Expr]
  (*************************************************************************)
  (* We assume that the parser has added a default initialization if one   *)
  (* is not specified.                                                     *)
  (*************************************************************************)

IsProcedure(prcd) ==
  /\ IsRecord(prcd, {"name", "decls", "params", "body"})
  /\ prcd.name   \in Name
  /\ prcd.params \in Seq(PVarDecl)
  /\ prcd.decls  \in Seq(PVarDecl)
  /\ \A i \in 1..Len(prcd.body) : IsLabeledStmt(prcd.body[i])

Procedure == {prcd \in Object : IsProcedure(prcd)}

IsProcess(proc) ==
  /\ IsRecord(proc, {"name", "decls", "id", "eqOrIn", "body"})
  /\ proc.name   \in Name
  /\ proc.eqOrIn \in {"=", "\\in"}
  /\ proc.id     \in Expr
  /\ proc.decls  \in Seq(VarDecl)
  /\ \A i \in 1..Len(proc.body) : IsLabeledStmt(proc.body[i])

Process == {proc \in Object : IsProcess(proc)}

IsAlgorithm(alg) ==
  \/ /\ alg.type = "uniprocess"
     /\ IsRecord(alg, {"type", "name", "decls", "prcds", "body", "defs"})
     /\ alg.defs  \in Expr
     /\ alg.name  \in Name
     /\ alg.decls \in Seq(VarDecl)
     /\ \A i \in 1..Len(alg.prcds) : IsProcedure(alg.prcds[i])
     /\ \A i \in 1..Len(alg.body) : IsLabeledStmt(alg.body[i]) 
  \/ /\ alg.type = "multiprocess"
     /\ IsRecord(alg, {"type", "name", "decls", "prcds", "procs", "defs"})
     /\ alg.defs \in Expr
     /\ alg.name  \in Name
     /\ alg.decls \in Seq(VarDecl)
     /\ \A i \in 1..Len(alg.prcds) : IsProcedure(alg.prcds[i])
     /\ \A i \in 1..Len(alg.procs) : IsProcess(alg.procs[i]) 

Algorithm == {alg \in Object : IsAlgorithm(alg)}
-----------------------------------------------------------------------------
(***************************************************************************)
(*                        THE DEFINITION OF `Translation'                  *)
(*                                                                         *)
(* A major part in the translation from a +CAL algorithm to a TLA+         *)
(* specification is the translation from the body of a uniprocess          *)
(* algorithm, process, or procedure to a sequence of TLA+ actions.  This   *)
(* part of the translation proceeds in two steps.  In the first, we        *)
(* translate a sequence of statements in `LabeledStmt' to a sequence of    *)
(* simple labeled statements, each of which corresponds to a single TLA+   *)
(* action.                                                                 *)
(*                                                                         *)
(* A simple labeled statement is one whose stmts field consists of a       *)
(* labeled sequence of statements in `SimpleStmt'.  In translating from    *)
(* labeled statements to simple labeled statements, `While', `LabelIf',    *)
(* and `LabelEither' statements are exploded into their component actions, *)
(* explicit statements of the form `when pc = ...' and `pc := ...' are     *)
(* added to describe the flow of control, and `CallOrReturn' statements    *)
(* are replaced by explicit assignments to procedure variables and to      *)
(* `stack'.                                                                *)
(*                                                                         *)
(* This first part of the translation is embodied in the definition of     *)
(* the operator FullyExplodeSeq.  It is defined so that if lsseq is a      *)
(* sequence of statements in LabeledStmt, then                             *)
(* FullyExplodeSeq(lsseq, ...) is the resulting sequence of simple         *)
(* labeled statements.  (The other arguments of FullyExplodeSeq are        *)
(* described below.)  We define FullyExplodeSeq in terms of the operator   *)
(* `Explode' that translates a single statement in LabeledStmt to an       *)
(* "almost simple labeled statements".  An almost simple labeled statement *)
(* is like a simple labled statement, except that the statements in        *)
(* its stmts field can include CallOrReturn or Goto statements.            *)
(*                                                                         *)
(* Before defining Explode, we define an operator for coalescing a         *)
(* sequence of sequences into a single sequence.                           *)
(*                                                                         *)
(* Note: We use the strings "@pc@" and "@stack@" instead of "pc" and       *)
(* "stack" for the variables that we introduce.  As the final step of the  *)
(* translation, we replace them with "pc" and "stack".  This means that    *)
(* any "pc" and "stack" in user expressions are not subscripted.  This     *)
(* makes the translation handle user-introduced instances of these         *)
(* variables almost correctly.  It still does not handle an assignment to  *)
(* "stack", which it should.                                               *)
(*                                                                         *)
(* This introduces the bug that any strings "@pc@" and "@stack@" in        *)
(* expressions will be translated to "pc" and "stack", but we're not going *)
(* to worry about that.                                                    *)
(***************************************************************************)

SeqConcat(s) ==
  (************************************************************************)
  (* If s is a sequence of sequences, then this is the concatenation of   *)
  (* those sequences.                                                     *)
  (************************************************************************)
  LET SC[i \in 0..Len(s)] ==
       (********************************************************************)
       (* The concatenation of the first i sequences of s.                 *)
       (********************************************************************)
       IF i = 0 THEN << >>
                ELSE SC[i-1] \o s[i]
  IN  SC[Len(s)]
  
(***************************************************************************)
(* Next comes the definition of `Explode'.  If xls is a labeled statement  *)
(* whose following statement is labeled xnext, then Explode(xls, xnext)    *)
(* equals the sequence of almost simple labeled statements that xls        *)
(* comprises.  Each of these almost simple labeled statements has a stmts  *)
(* field that is a sequence of elements of SimpleStmt that explicitly set  *)
(* the pc, and callOrReturn statements.  Moreover, each call statement's   *)
(* returnTo field is set to the label to which the call returns.  (In a    *)
(* return or call/return statement, the new pc value is obtained from the  *)
(* stack.)                                                                 *)
(*                                                                         *)
(* `Explode' is really a recursively defined function.  However, it is     *)
(* made an operator by defining its function form `Xplode' in a LET and    *)
(* defining Explode(xls, xnext) to equal Xplode[xls, xnext].  This is done *)
(* because, for uniformity, I like to make all outer-level definitions be  *)
(* of operators rather than functions.                                     *)
(***************************************************************************)
Explode(xls, xnext) ==
  LET Xplode[ls \in Object, next \in Label] ==
      (*********************************************************************)
      (* The call of Xplode checks that ls \in LabeledStmt.                *)
      (*********************************************************************)
      LET ExplodeSeq[lseq \in Object, nxt \in Label] ==
            (***************************************************************)
            (* The union of all labeled statements obtained by applying    *)
            (* Xplode to each element of the sequence lseq of labeled      *)
            (* statements.  It is called only when lseq \in LabeledStmt.   *)
            (* [I think that should be lseq \in Seq(LabeledStmt).]         *)
            (***************************************************************)
            IF lseq = << >>
              THEN << >>
              ELSE IF Len(lseq) = 1
                     THEN Xplode[Head(lseq), nxt]
                     ELSE Xplode[Head(lseq), Head(Tail(lseq)).label] 
                            \o ExplodeSeq[Tail(lseq), nxt]

          IsFinal[st \in Object] ==
            (***************************************************************)
            (* Should be called with st in                                 *)
            (* FinalIf \cup FinalEither \cup FinalWith.                    *)
            (*                                                             *)
            (* True of an `If' or `Either' or `With' statement iff it      *)
            (* contains a CallOrReturn.                                    *)
            (***************************************************************)
            IF IsFinalIf(st) \/ IsFinalEither(st) \/ IsFinalWith(st)
              THEN CASE st.type = "if" ->
                          \/ /\ st.then # << >>
                             /\ \/ st.then[Len(st.then)].type \in 
                                     {"call", "return", "callReturn", "goto"}
                                \/ /\ st.then[Len(st.then)].type \in 
                                        {"if", "either", "with"}
                                   /\ IsFinal[st.then[Len(st.then)]]
                          \/ /\ st.else # << >>
                             /\ \/ st.else[Len(st.else)].type \in 
                                     {"call", "return", "callReturn", "goto"}
                                \/ /\ st.else[Len(st.else)].type \in 
                                       {"if", "either", "with"}
                                   /\ IsFinal[st.else[Len(st.else)]]
                     [] st.type = "either" ->
                          \E n \in 1..Len(st.ors) :
                              \/ st.ors[n][Len(st.ors[n])].type \in 
                                     {"call", "return", "callReturn", "goto"}
                              \/ /\ st.ors[n][Len(st.ors[n])].type \in 
                                        {"if", "either", "with"}
                                 /\ IsFinal[st.ors[n][Len(st.ors[n])]]
                     [] st.type = "with" ->
                          \/ st.do[Len(st.do)].type \in 
                               {"call", "return", "callReturn", "goto"}
                          \/ /\ st.do[Len(st.do)].type \in 
                                    {"if", "either", "with"}
                             /\ IsFinal[st.do[Len(st.do)]]
              ELSE ErrorVal

          IsFinalSeq(s) ==
            (***************************************************************)
            (* True iff s is a nonempty sequence ending in a CallOrReturn  *)
            (* or Goto or in an `If' or `Either' or `When' that contains a *)
            (* CallOrReturn.                                               *)
            (***************************************************************)
            /\ s # << >>
            /\ LET last == s[Len(s)]
               IN  \/ last.type \in {"call", "return", "callReturn", "goto"}
                   \/ /\ last.type \in {"if", "either", "with"}
                      /\ IsFinal[last]

          DoLabelSeq[s \in Object, nxt \in Label]  ==
            (***************************************************************)
            (* We should have s \in LabelSeq                               *)
            (*                                                             *)
            (* This is a record with two fields:                           *)
            (*                                                             *)
            (*   stmts : The sequence of statements in the "prefix" of     *)
            (*           s that produces a single atomic action.  That     *)
            (*           sequence ends with an assignment to pc if         *)
            (*           addPC = TRUE and there is no call or return in    *)
            (*           that prefix.  (That comment is obsolete, and      *)
            (*           addPC has been removed.  I think the current      *)
            (*           behavior is the one obtained with addPC = TRUE.)  *)
            (*                                                             *)
            (*   expl  : The sequence of almost simple labeled statements  *)
            (*           produced by labeled statements nested within s.   *)
            (*                                                             *)
            (* Note that, because s is in LabelSeq, it does not begin with *)
            (* a `While' statement.                                        *)
            (***************************************************************)
            IF IsLabelSeq(s)
              THEN IF /\ s # << >>
                      /\ s[Len(s)].type \in {"labelIf", "labelEither"}
                     THEN IF s[Len(s)].type = "labelIf"
                           THEN  \* a LabelIf
                             LET lif == s[Len(s)]
              
                                 DoThen == DoLabelSeq[
                                             lif.unlabThen,
                                             IF lif.labThen = << >>
                                               THEN nxt
                                               ELSE Head(lif.labThen).label]
                                 DoElse == DoLabelSeq[
                                             lif.unlabElse,
                                             IF lif.labElse = << >>
                                               THEN nxt
                                               ELSE Head(lif.labElse).label]
                             IN  [stmts |-> SubSeq(s, 1, Len(s)-1)
                                              \o
                                            << [type |-> "if",
                                                test |-> lif.test,
                                                then |-> DoThen.stmts,
                                                else |-> DoElse.stmts] >>,
                                  expl  |->    DoThen.expl 
                                            \o ExplodeSeq[lif.labThen, nxt]
                                            \o DoElse.expl
                                            \o ExplodeSeq[lif.labElse, nxt]]
                           ELSE  \* a LabelEither
                             LET ethr == s[Len(s)]
              
                                 DoClauses == 
                                   [n \in 1..Len(ethr.clauses) |->
                                     DoLabelSeq[
                                      ethr.clauses[n].unlabOr,
                                      IF ethr.clauses[n].labOr = << >>
                                       THEN nxt
                                       ELSE Head(ethr.clauses[n].labOr).label]]
                             IN  [stmts |-> 
                                    SubSeq(s, 1, Len(s)-1)
                                       \o
                                    <<[type |-> "either",
                                       ors  |-> 
                                          [i \in 1..Len(DoClauses)
                                             |-> DoClauses[i].stmts]]>>,
                                  expl  |-> 
                                     SeqConcat(
                                       [i \in 1..Len(DoClauses) |->
                                         DoClauses[i].expl \o 
                                          ExplodeSeq[ethr.clauses[i].labOr, 
                                                     nxt]] ) ]

                     ELSE [stmts |-> 
                             IF IsFinalSeq(s)
                               THEN 
                                 CASE s[Len(s)].type \in 
                                         {"call", "return", 
                                           "callReturn", "goto"} ->
                                        IF s[Len(s)].type = "call"
                                          THEN [s EXCEPT 
                                                 ![Len(s)].returnTo =nxt]
                                          ELSE s
                                   []
                                       s[Len(s)].type = "if" ->
                                         [s EXCEPT 
                                           ![Len(s)].then = 
                                              DoLabelSeq[@, nxt].stmts,
                                           ![Len(s)].else = 
                                              DoLabelSeq[@, nxt].stmts]
                                   []
                                       s[Len(s)].type = "either" ->
                                         [s EXCEPT 
                                           ![Len(s)].ors = 
                                              [i \in 1..Len(@) |->
                                                DoLabelSeq[@[i], nxt].stmts]]
                                   [] 
                                       s[Len(s)].type = "with" ->
                                         [s EXCEPT 
                                           ![Len(s)].do  = 
                                              DoLabelSeq[@, nxt].stmts]
           
                               ELSE s \o 
                                         << [type |-> "assignment",
                                             ass  |-> 
                                                << [lhs |-> [var |-> "@pc@",
                                                             sub |-> << >>],
                                                    rhs |-> Quote(nxt)]>>] >>,
                           expl |-> <<>> ]
              ELSE ErrorVal

          DoStmts == 
            (***************************************************************)
            (* Like DoLabelSeq[ls.stmts, next], except it handles the      *)
            (* `While' that may appear as the head of ls.stmts.            *)
            (***************************************************************)
            IF (ls.stmts # << >>) /\ (Head(ls.stmts).type = "while")
              THEN LET while   == Head(ls.stmts)
                       DoRest  == DoLabelSeq[Tail(ls.stmts), next]
                       DoUnlDo == DoLabelSeq[while.unlabDo,
                                             IF while.labDo = <<>>
                                               THEN ls.label
                                               ELSE Head(while.labDo).label]
                   IN  [stmts |-> 
                         <<[type |-> "if",
                            test |-> while.test,
                            then |-> DoUnlDo.stmts,
                            else |-> DoRest.stmts]>> ,
                        expl  |->    DoUnlDo.expl
                                  \o ExplodeSeq[while.labDo, ls.label]
                                  \o DoRest.expl]
              ELSE DoLabelSeq[ls.stmts, next]

      IN    << [label |-> ls.label, stmts |-> DoStmts.stmts] >>
         \o DoStmts.expl

  IN IF IsLabeledStmt(xls) THEN Xplode[xls, xnext]
                           ELSE ErrorVal
-----------------------------------------------------------------------------
(***************************************************************************)
(*                TRANSLATING CALLS, RETURNS, AND GOTOS                    *)
(*                                                                         *)
(* We now define a sequence of operators that are used to replace a        *)
(* CallOrReturn statement or a Goto with a (multiple) assignment statement *)
(* that implements it by the appropriate commands to set pc, `stack', and  *)
(* procedure variables.                                                    *)
(***************************************************************************)

NameToPrcd(name, pseq) ==
  (*************************************************************************)
  (* Assumes pseq is a sequence of procedures and `name' is a `Name'.  If  *)
  (* `name' is the name of one of those procedures, then this equals that  *)
  (* procedure; otherwise it equals a dummy procedure whose name is the    *)
  (* empty string, has no parameters or declarations, and has a body       *)
  (* containing a single statement with name the empty string.             *)
  (*************************************************************************)
  LET IsProc(i) == pseq[i].name = name
  IN  IF \E i \in 1..Len(pseq) : IsProc(i)
           THEN pseq[CHOOSE i \in 1..Len(pseq) : IsProc(i)]
           ELSE [name   |-> "",
                 params |-> << >>,
                 decls  |-> << >>,
                 body   |-> << [label |-> "",
                                stmts |-> << >>] >>]

SetPrcdVarsOnCall(call, prcd) ==
  (*************************************************************************)
  (* A sequence of assignment statements to set the variables of procedure *)
  (* prcd when called by a `call' or callReturn `call'.  This equals a     *)
  (* nonsensical expression (one that will produce a TLC error) if the     *)
  (* number of arguments in the call does not equal the number of          *)
  (* arguments of the procedure.                                           *)
  (*************************************************************************)
   LET ParamsAssignment ==
         (******************************************************************)
         (* The multiple assignment                                        *)
         (*                                                                *)
         (*       prcd.params[1] := call.args[1]                           *)
         (*    || ...                                                      *)
         (*    || prcd.params[Len(prcd.params)] :=                         *)
         (*           call.args[Len(prcd.params)]                          *)
         (*                                                                *)
         (* However, it produces a record of type `error' if               *)
         (* Len(prcd.params) # Len(call.args) with val field containing an *)
         (* error message.  The value of SetPrcdVarsOnCall(call, prcd)     *)
         (* depends on ParamsAssignment.ass, which is a nonsensical value  *)
         (* if ParamsAssignment is such an error record.                   *)
         (******************************************************************)
         IF Len(prcd.params) = Len(call.args)
           THEN [type |-> "assignment", 
                 ass  |-> [i \in 1..Len(prcd.params) |-> 
                            [lhs |-> [var |->  prcd.params[i].var, 
                                      sub |-> << >>],
                             rhs |-> call.args[i]]]]
           ELSE [type |-> "error",
                 val  |-> <<"Procedure", prcd.name, 
                            "called with wrong number of arguments">>]

       PVblsAssignment ==
         (******************************************************************)
         (* The multiple assignment                                        *)
         (*                                                                *)
         (*       prcd.decls[1].var := prcd.decls[1].val                   *)
         (*    || ...                                                      *)
         (*    || prcd.decls[Len(prcd.decls)].var :=                       *)
         (*           prcd.decls[Len(prcd.decls)].val                      *)
         (******************************************************************)
         [type |-> "assignment", 
          ass  |-> [i \in 1..Len(prcd.decls) |-> 
                     [lhs |-> [var |->  prcd.decls[i].var, sub |-> << >>],
                      rhs |-> prcd.decls[i].val ]]]

   IN  (IF Len(ParamsAssignment.ass) > 0 THEN <<ParamsAssignment>>
                                         ELSE << >>)
          \o
       (IF Len(PVblsAssignment.ass) > 0 THEN <<PVblsAssignment>>
                                        ELSE << >> )

XlateGoto(goto) ==
  (*************************************************************************)
  (* The sequence of statements consisting of the single assignment to pc  *)
  (* that implements a goto statement.                                     *)
  (*************************************************************************)
  << [type |-> "assignment",
      ass  |-> << [lhs |-> [var |-> "@pc@", sub |-> << >>],
                   rhs |-> Quote(goto.to) ] >>] >>

  
XlateCall(call, pseq) == 
   (************************************************************************)
   (* If pseq is a sequence of Procedures and `call' is a `call' statement *)
   (* to one of them, then this is its translation as a sequence of        *)
   (* unlabeled statements.                                                *)
   (************************************************************************)
   LET prcd == NameToPrcd(call.to, pseq)
       NewStack == 
         (******************************************************************)
         (* The Expr described informally as follows                       *)
         (* `.                                                             *)
         (*    << [ procedure |-> call.to,                                 *)
         (*         pc        |-> call.returnTo  ,                         *)
         (*         prcd.params[1] |-> prcd.params[i] ,                    *)
         (*         ...                                                    *)
         (*         prcd.params[Len(prcd.params)] |->                      *)
         (*               prcd.params[Len(prcd.params)],                   *)
         (*         prcd.decls[i].var |-> prcd.decls[i].var],              *)
         (*         ...                                                    *)
         (*         prcd.decls[Len(prcd.decls)].var |->                    *)
         (*               prcd.decls[Len(prcd.decls)].var ] >> \o stack  .'*)
         (******************************************************************)
         << "<<", "[", "procedure", "|->">> 
              \o  Quote(call.to) 
              \o  << ",", "@pc@", "|->" >> 
              \o  Quote(call.returnTo) 
           \o
         SeqConcat([i \in 1..Len(prcd.params) |-> 
                      <<",", prcd.params[i].var, "|->",  prcd.params[i].var >> 
                   ]) 
           \o
         SeqConcat([i \in 1..Len(prcd.decls) |-> 
                      <<",", prcd.decls[i].var, "|->", prcd.decls[i].var >> 
                   ]) 
           \o
         << "]", ">>", "\\o", "@stack@" >>
       
   IN  (********************************************************************)
       (* pc := prcd.body[1].label ;                                       *)
       (* stack := NewStack ;                                              *)
       (* SetPrcdVarsOnCall(call, prcd)                                    *)
       (********************************************************************)
       << [type |-> "assignment",
           ass  |-> << [lhs |-> [var |-> "@pc@", sub |-> << >>],
                        rhs |-> Quote(prcd.body[1].label) ] >>],
          [type |-> "assignment",
           ass  |-> << [lhs |-> [var |-> "@stack@", sub |-> << >>],
                        rhs |-> NewStack  ] >>] >>  
        \o 
       SetPrcdVarsOnCall(call, prcd) 


RestorePrcdVarsFrom(prcd) ==
   (************************************************************************)
   (* A sequence of assignment statements to restore the variables of      *)
   (* procedure prcd when returning from the procedure.  The saved values  *)
   (* are obtained from Head(stack).  In the comments below, stkElement    *)
   (* denotes Head(stack).                                                 *)
   (************************************************************************)
   LET ParamsAssignment ==
         (******************************************************************)
         (* The multiple assignment                                        *)
         (*                                                                *)
         (*       prcd.params[1] := stkElement.prcd.params[1]              *)
         (*    || ...                                                      *)
         (*    || prcd.params[Len(prcd.params)] := stkElement.prcd.params  *)
         (******************************************************************)
         [type |-> "assignment", 
          ass  |-> [i \in 1..Len(prcd.params) |-> 
                     [lhs |-> [var |->  prcd.params[i].var, sub |-> << >>],
                      rhs |-> <<"Head", "(", "@stack@", ")" >> \o 
                                  <<".", prcd.params[i].var>>]]]

       PVblsAssignment ==
         (******************************************************************)
         (* The multiple assignment                                        *)
         (*                                                                *)
         (*       prcd.decls[1].var := stkElement.prcd.decls[1].var        *)
         (*    || ...                                                      *)
         (*    || prcd.decls[Len(prcd.decls)].var :=                       *)
         (*           stkElement.prcd.decls[Len(prcd.decls)].var           *)
         (******************************************************************)
         [type |-> "assignment", 
          ass  |-> [i \in 1..Len(prcd.decls) |-> 
                     [lhs |-> [var |->  prcd.decls[i].var, sub |-> << >>],
                      rhs |-> <<"Head", "(", "@stack@", ")" >> \o 
                                   <<".", prcd.decls[i].var >>]]]
  IN  (IF Len(ParamsAssignment.ass) > 0 THEN <<ParamsAssignment>>
                                        ELSE << >>)
        \o
      (IF Len(PVblsAssignment.ass) > 0 THEN <<PVblsAssignment>>
                                       ELSE << >> )


XlateReturn(rtn, pseq) == 
   (************************************************************************)
   (* If pseq is a sequence of procedures and rtn is a `return' statement  *)
   (* to one of them, then this is its translation as a sequence of        *)
   (* assignment statements.                                               *)
   (************************************************************************)
   LET prcd == NameToPrcd(rtn.from, pseq)
   IN  (********************************************************************)
       (*`. pc := Head(stack).pc ;                                         *)
       (*   ParamsAssignment (if nonempty) ;                               *)
       (*   PVblsAssignment  (if nonempty) ;                               *)
       (*   stack := Tail(stack)                                        .' *)
       (********************************************************************)
       << [type |-> "assignment",
           ass  |-> << [lhs |-> [var |-> "@pc@", sub |-> << >>],
                        rhs |-> <<"Head", "(", "@stack@", ")", ".", "@pc@">> 
                       ] >>] >>
        \o 
       RestorePrcdVarsFrom(prcd)
        \o
       << [type |-> "assignment",
           ass  |-> << [lhs |-> [var |-> "@stack@", sub |-> << >>],
                        rhs |-> <<"Tail", "(", "@stack@", ")">>] >>] >>  

AssSeqToMultiAss(aseq) ==
  (*************************************************************************)
  (* If aseq is the sequence <<A1, A2, ...  , An>> of assignment           *)
  (* statements, then this equals the single multi-assignment              *)
  (* A1 || A2 || ...  || An                                                *)
  (*************************************************************************)
  [type |->  "assignment",
   ass  |-> SeqConcat([i \in 1..Len(aseq) |-> aseq[i].ass]) ]

XlateCallReturn(crtn, pseq) == 
   (************************************************************************)
   (* If pseq is a sequence of procedures and crtn is a call/return        *)
   (* statement in one of them that calls one of them, then this is the    *)
   (* translation of that call/return as a sequence of unlabeled           *)
   (* assignment statements.                                               *)
   (*                                                                      *)
   (* The call/return is an optimization that causes the return from the   *)
   (* procedure being called to return directly to the caller of the       *)
   (* current procedure.  When the current procedure and the called        *)
   (* procedures are the same, then this is the usual optimization that    *)
   (* effectively replaces tail recursion with a loop.  When the two       *)
   (* procedures are different, it makes the return from the called        *)
   (* procedure produce the same state as would have been produced by      *)
   (* executing it and then executing the return from the current          *)
   (* procedure.                                                           *)
   (*                                                                      *)
   (* To explain the translation, let the variables of a procedure         *)
   (* consist of its local variables and its parameters.  The translation  *)
   (* is simple when the call is to the current procedure.  Suppose the    *)
   (* call is executed within an invocation i of procedure P to initiate   *)
   (* invocation i+1 of P. In that case, P's variables are set and the     *)
   (* stack is left unchanged.  Executing a return from invocation i+1     *)
   (* then restores the variables to the values they had immediately       *)
   (* before the call of invocation i, and the return goes to the          *)
   (* location from where invocation i had been called.                    *)
   (*                                                                      *)
   (* The case of a call from procedure P to a different procedure Q is    *)
   (* trickier.  The call must do the following.                           *)
   (*                                                                      *)
   (*  - Save the current values of Q's variables on the stack,            *)
   (*    and set the return location on the head of the stack              *)
   (*    to the location to which the return from P should                 *)
   (*    return.                                                           *)
   (*                                                                      *)
   (*  - Set the variables of Q.  In the expressions to which              *)
   (*    the parameters of Q are set, the current values of P's            *)
   (*    variables must be used.                                           *)
   (*                                                                      *)
   (*  - Reset the variables of P to the values that had been saved        *)
   (*    on the stack when P was called, which were at the head of the     *)
   (*    stack, before the stack was changed in the first step.            *)
   (*                                                                      *)
   (* This requires that the current head of the stack be used in the      *)
   (* third step after having been set in the first step.  Fortunately,    *)
   (* that's not a problem when all the assignments are done with a single *)
   (* multiple assignment.  For historical reasons, this is done by        *)
   (* applying AssSeqToMultiAss to a sequence of ordinary assignments.     *)
   (************************************************************************)
   LET cprcd == NameToPrcd(crtn.to, pseq)   \* The called procedure
       rprcd == NameToPrcd(crtn.from, pseq) \* The calling procedure 
       NewStack == 
         (******************************************************************)
         (* The new stack if the two procedures are different.  It is an   *)
         (* Expr described informally as follows                           *)
         (* `.                                                             *)
         (*    [stack EXCEPT ![1] =                                        *)
         (*       [ procedure |-> crtn.to,                                 *)
         (*         pc        |-> Head(stack).pc,                          *)
         (*         cprcd.params[1] |-> cprcd.params[i] ,                  *)
         (*         ...                                                    *)
         (*         cprcd.params[Len(cprcd.params)] |->                    *)
         (*               cprcd.params[Len(cprcd.params)],                 *)
         (*         cprcd.decls[i].var |-> cprcd.decls[i].var,             *)
         (*         ...                                                    *)
         (*         cprcd.decls[Len(cprcd.decls)].var |->                  *)
         (*               cprcd.decls[Len(cprcd.decls)].var ] ]         .' *)
         (******************************************************************)
         << "[", "@stack@", "EXCEPT", "!", "[", "1", "]", "=",
                   "[", "procedure", "|->">> \o 
         Quote(crtn.to) \o 
         <<",", "@pc@", "|->", "Head", "(", "@stack@", ")",".", "@pc@">> 
          \o
         SeqConcat([i \in 1..Len(cprcd.params) |-> 
                      <<",", cprcd.params[i].var, "|->",  
                              cprcd.params[i].var >> 
                   ]) 
          \o
         SeqConcat([i \in 1..Len(cprcd.decls) |-> 
                      <<",", cprcd.decls[i].var, "|->", cprcd.decls[i].var >> 
                   ]) 
          \o
         << "]", "]">>
       
   IN  (********************************************************************)
       (* `. pc := prcd.body[1].label  ;                                   *)
       (*    SetPrcdVarsOnCall(crtn, prcd) ;                               *)
       (*    If the two procedures are different, then                     *)
       (*      RestorePrcdVarsFromStack(rprcd) ;                           *)
       (*      stack := NewStack                                           *)
       (********************************************************************)
       << [type |-> "assignment",
           ass  |-> << [lhs |-> [var |-> "@pc@", sub |-> << >>],
                        rhs |-> Quote(cprcd.body[1].label) ] >>] >> 
        \o  
       IF crtn.to # crtn.from
         THEN  << AssSeqToMultiAss(
                   << [type |-> "assignment",
                        ass  |-> << [lhs |-> [var |-> "@stack@", sub |-> << >>],
                                     rhs |-> NewStack  ] >>]
                    >>
                      \o 
                    SetPrcdVarsOnCall(crtn, cprcd) 
                     \o 
                    RestorePrcdVarsFrom(rprcd)
                   ) >>
         ELSE SetPrcdVarsOnCall(crtn, cprcd) 
-----------------------------------------------------------------------------
(***************************************************************************)
(*                   THE DEFINITION OF `FullyExplodeSeq'                   *)
(*                                                                         *)
(* If lsseq is a sequence of LabeledStmts with `next' as the label that    *)
(* follows them, and pseq is a sequence of procedures, then                *)
(*                                                                         *)
(*    FullyExplodeSeq(lsseq, pseq, next)                                   *)
(*                                                                         *)
(* is the sequence of simple labeled statements that they translate to,    *)
(* each of those statements having a stmts field that is a sequence of     *)
(* statements in SimpleStmt, all calls and returns having been translated  *)
(* to assignments.  Each statement with label lbl begins with the          *)
(* statement `when pc=lbl'.                                                *)
(***************************************************************************)
FullyExplodeSeq(lsseq, pseq, next) ==
  LET RemoveCAndR[stmts \in Object] ==
        (*******************************************************************)
        (* Should be called with stmts \in LabelSeq.                       *)
        (*                                                                 *)
        (* If stmts is the stmts field of a labeled statement produced by  *)
        (* evaluating Xplode, then this is the sequence of unlabeled       *)
        (* statements obtained by removing all calls and returns.  For     *)
        (* simplicity, we define it for domain LabelSeq, though we apply   *)
        (* it only to elements of LabelSeq with no LabelIf (or             *)
        (* LabelEither) statements.                                        *)
        (*******************************************************************)
        IF IsLabelSeq(stmts) 
          THEN IF stmts = << >>
                THEN << >>
                ELSE LET last  == stmts[Len(stmts)]
                         front == SubSeq(stmts, 1, Len(stmts)-1)
                     IN  CASE last.type = "if" ->
                                Append(front,
                                       [last EXCEPT !.then = RemoveCAndR[@],
                                                    !.else = RemoveCAndR[@]]) 
                         []   last.type = "either" ->
                                 Append(front,
                                        [last EXCEPT 
                                          !.ors = 
                                            [i \in 1..Len(@) |->
                                               RemoveCAndR[@[i]]]])
                         []   last.type = "with" ->
                                Append(front,
                                       [last EXCEPT !.do = RemoveCAndR[@]])   
                         []   last.type = "call" ->                     
                                 front \o XlateCall(last, pseq)       
                         []   last.type = "return" ->                     
                                 front \o XlateReturn(last, pseq)     
                         []   last.type = "callReturn" ->                     
                                 front \o XlateCallReturn(last, pseq) 
                         []   last.type = "goto" ->                     
                                 front \o XlateGoto(last) 
                         []   OTHER -> stmts
          ELSE ErrorVal

      ExplodeSeq ==
        SeqConcat([i \in 1..Len(lsseq) |->
                     Explode(lsseq[i], IF i = Len(lsseq) 
                                         THEN next
                                         ELSE lsseq[i+1].label)])
      AddWhen(ls) == 
        [ls EXCEPT !.stmts = <<[type |-> "when",
                                exp  |-> <<"@pc@", "=">> \o 
                                             Quote(ls.label)]>> \o @]

  IN  [i \in 1..Len(ExplodeSeq) |-> 
          [AddWhen(ExplodeSeq[i]) EXCEPT !.stmts = RemoveCAndR[@]]]
   
-----------------------------------------------------------------------------
(***************************************************************************)
(*                    ADDING SUBSCRIPTS                                    *)
(*                                                                         *)
(* The operator FullyExplodeSeq maps a sequence of statements in           *)
(* LabeledStmt into a sequence of simple labeled statements with calls and *)
(* returns removed and with the control set by assigments to the variable  *)
(* pc.  If those statements are in a process or in a procedure of a        *)
(* multiprocess algorithm, then subscripts need to be added to all         *)
(* occurrences of local variables.  This is done by the operator           *)
(* AddSubscript.  To define it, we first define the operator ProcessVars   *)
(* such that                                                               *)
(*                                                                         *)
(*    ProcessVars(vars, addExpr, expr)                                     *)
(*                                                                         *)
(* is the Expr obtained from the expression expr by inserting the          *)
(* sequence addExpr of strings after every occurrence of a variable in     *)
(* the set vars of variables.  We will also use ProcessVars to prime       *)
(* variables in expressions.                                               *)
(*                                                                         *)
(* The definition of ProcessVars is tricky because we want to do the       *)
(* insertion after an occurrence of the string "v" only if that string     *)
(* represents an occurrence of variable v, not if it represents a record   *)
(* field as in:                                                            *)
(*                                                                         *)
(*    a.v   [v : S, ... , ]   [v |-> e, ..., ]                             *)
(*                                                                         *)
(* The heart of the definition is the recursive function                   *)
(* PV[done, stk, rest] that returns a record with components `done', stk,  *)
(* and `rest', where                                                       *)
(*                                                                         *)
(*  - done is the part of expr already processed.                          *)
(*                                                                         *)
(*  - rest is the unprocessed part of expr.                                *)
(*                                                                         *)
(*  - stk is a sequence of Booleans whose length is the number of          *)
(*    unmatched "["s at the current point in expr, and an element of       *)
(*    this sequence equals TRUE iff the corresponding unmatched "["        *)
(*    began an expression of the form [v : S, ...  ] or [v |-> S, ...  ]   *)
(*                                                                         *)
(* This specification assumes that [] (the temporal box operator and CASE  *)
(* separator) is a single lexeme, and that the "[" and "]" in an           *)
(* expression of the form "[exp]_sub" are represented as ordinary square   *)
(* brackets.  (It's possible, though extremely unlikely, for a +CAL        *)
(* algorithm to contain an expression like ENABLED [A]_v.)  This           *)
(* assumption is not strictly kosher because "]_" is really a single       *)
(* lexeme.  A translation program will probably parse "]_" as a single     *)
(* lexeme and then treat it as a special case for square-bracket matching. *)
(* The program should be tested on an example with an expression like      *)
(* ENABLED [A]_v.                                                          *)
(***************************************************************************)
ProcessVars(vars, addExpr, expr) ==
  LET PV[done \in Expr, 
         stk  \in Seq(BOOLEAN), 
         rest \in Expr] ==
        LET Error(msg) == [done |-> done \o <<"Error", msg>> ,
                           stk  |-> << >>,
                           rest |-> << >>]
            nDone == done \o <<Head(rest)>>
            nRest == Tail(rest)
            
        IN  IF rest = << >>
             THEN [done |-> IF stk = << >> 
                              THEN done
                              ELSE done \o <<"Error", "unmatched [s">>, 
                   stk  |-> << >>,
                   rest |-> << >>]
                                 
             ELSE LET callVal ==
                       CASE Head(rest) = "[" ->
                             IF Len(rest) < 3
                               THEN Error("premature end")
                               ELSE IF rest[3] \in {":", "|->"}
                                      THEN [done |-> 
                                              done \o SubSeq(rest, 1,3),
                                            stk  |-> <<TRUE>> \o stk,
                                            rest |-> 
                                              SubSeq(rest, 4, Len(rest))]
                                      ELSE [done |-> done \o <<"[">>,
                                            stk  |-> <<FALSE>> \o stk,
                                            rest |-> nRest ]
        
                       []   Head(rest) = "]" ->
                              IF stk = <<>>
                                THEN Error("Extra ]")
                                ELSE [done |-> nDone, 
                                      stk  |-> Tail(stk),
                                      rest |-> nRest]
                       []   Head(rest) = "." ->
                              [done |-> done \o SubSeq(rest, 1,2),
                               stk  |-> stk,
                               rest |-> SubSeq(rest, 3, Len(rest))]
                       []   Head(rest) = ","   ->
                              IF /\ stk # << >>
                                 /\ Head(stk) = TRUE
                                 /\ \/ Len(rest) < 3
                                    \/ rest[3] \in {":", "|->"}
                                THEN IF Len(rest) < 3
                                       THEN Error("premature end")
                                       ELSE [done |-> 
                                               done \o SubSeq(rest, 1,3),
                                             stk  |-> stk,
                                             rest |-> 
                                               SubSeq(rest, 4, Len(rest))]
                                ELSE [done |-> nDone, 
                                      stk  |-> stk, 
                                      rest |-> nRest]

                       (****************************************************)
                       (* The following clause was added 25 Oct 05 to      *)
                       (* handle quoted strings properly.                  *)
                       (****************************************************)
                       []   Head(rest) = "\"" -> 
                              IF \/ Len(rest) < 3
                                 \/ rest[3] # "\""
                                THEN Error("unmatched quote")
                                ELSE [done |-> done \o SubSeq(rest, 1,3),
                                             stk  |-> stk,
                                             rest |-> 
                                               SubSeq(rest, 4, Len(rest))]
                       []   OTHER ->
                             [done |-> nDone \o (IF Head(rest) \in vars
                                                   THEN addExpr
                                                   ELSE << >> ),
                              stk  |-> stk,
                              rest |-> nRest]
                  IN  PV[callVal.done, callVal.stk, callVal.rest]
 IN PV[<<>>, <<>>, expr].done

AddSubscript(vars, sub, stmts) ==
  (*************************************************************************)
  (* If stmts is a sequence of simple statements, then this produces the   *)
  (* sequence of simple statements obtained by replacing every instance of *)
  (* a variable `v' in the set vars of variables by `v' followed by `sub', *)
  (* where `sub' is an Expr.                                               *)
  (*************************************************************************)
  LET PV(expr) == ProcessVars(vars, sub, expr)
      DoAssignment(stmt) ==
        (*******************************************************************)
        (* The assignment obtained from assignment statement stmt by doing *)
        (* the substitution.                                               *)
        (*******************************************************************)
        LET DoAss[ass \in Seq([lhs: LHS, rhs : Expr])] ==
              IF ass = << >>
                THEN << >>
                ELSE << [lhs |-> IF ass[1].lhs.var \in vars
                                   THEN [ass[1].lhs EXCEPT 
                                           !.sub = sub \o PV(@)]
                                   ELSE [ass[1].lhs EXCEPT !.sub = PV(@)],
                         rhs |-> PV(ass[1].rhs)] >>
                       \o DoAss[Tail(ass)]
        IN  [type |-> "assignment", ass  |-> DoAss[stmt.ass]]

      DoWhenOrPrintOrAssert(stmt) == [stmt EXCEPT !.exp = PV(@)]
        (*******************************************************************)
        (* The `when' or `print' or `assert' obtained from a `when' or     *)
        (* `print' or `assert' statement stmt by doing the substitution.   *)
        (*******************************************************************)

      \* TLCAlgorithms: Should be  AS[sseq \in Seq(SimpleStmt(1))]
      AS[sseq \in Object] ==
       (********************************************************************)
       (* The recursively defined operator that performs the substitution  *)
       (* on a sequence sseq of simple statements.                         *)
       (********************************************************************)
     IF \A i \in 1..Len(sseq) : IsSimpleStmt(sseq[i]) THEN
       IF sseq = << >>
         THEN << >>
         ELSE CASE Head(sseq).type = "assignment" ->
                     <<DoAssignment(Head(sseq))>> \o AS[Tail(sseq)]
              []   Head(sseq).type \in {"when", "print", "assert"} ->
                     <<DoWhenOrPrintOrAssert(Head(sseq))>> \o AS[Tail(sseq)]   
              []   Head(sseq).type = "with" ->
                     <<[Head(sseq) EXCEPT
                         !.exp = PV(@),
                         !.do  = AS[@]]>> \o AS[Tail(sseq)]
              []   Head(sseq).type = "if" ->
                     <<[Head(sseq) EXCEPT
                         !.test = PV(@),
                         !.then = AS[@],
                         !.else = AS[@]]>> \o AS[Tail(sseq)]
              []   Head(sseq).type = "either" ->
                     <<[Head(sseq) EXCEPT
                         !.ors = [i \in 1..Len(@) |-> AS[@[i]]]]>> 
                        \o AS[Tail(sseq)]
              []   Head(sseq).type = "skip" ->
                     <<Head(sseq)>> \o AS[Tail(sseq)] 
     ELSE (\A i \in 1..Len(sseq) :
              (IF IsSimpleStmt(sseq[i]) 
                THEN TRUE
                ELSE Print(sseq[i], TRUE)))
             /\ ErrorVal
          
  IN  AS[stmts]                
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            SOME USEFUL OPERATORS                        *)
(*                                                                         *)
(* Before going further, we define two useful operators on sequences and   *)
(* some operators for combining expressions into larger expressions.       *)
(***************************************************************************)
SeqToSet(s) == {s[i] : i \in 1..Len(s)}
  (*************************************************************************)
  (* The set of elements in the sequence s                                 *)
  (*************************************************************************)
  
SeqMinus(s, t) ==
  (*************************************************************************)
  (* The subsequence of sequence s consisting of those elements not in     *)
  (* sequence t.                                                           *)
  (*************************************************************************)
  LET T == SeqToSet(t)
      Test(e) == e \notin T
  IN  SelectSeq(s, Test)  

CommaSeq(s) ==
  (*************************************************************************)
  (* If s is a sequence of strings, then this equals the sequence obtained *)
  (* by inserting "," between each element of the sequence s.              *)
  (*************************************************************************)
   [i \in 1..(2*Len(s)-1) |-> IF i % 2 = 0 THEN "," 
                                           ELSE s[(i + 1) \div 2]]
AppendCommaSeq(s) ==
  (*************************************************************************)
  (* Like CommaSeq(s), except it puts a "," at the head of the sequence    *)
  (* iff s is nonempty.                                                    *)
  (*************************************************************************)
  IF s = << >> THEN << >> ELSE <<",">> \o CommaSeq(s)

CommaConcatSeq(s) ==
  (*************************************************************************)
  (* If s is a sequence of sequence of strings, then this equals the       *)
  (* sequence obtained by concatenating those sequences, with commas       *)
  (* inserted between them.  For example,                                  *)
  (*                                                                       *)
  (*   CommaConcatSeq(<< <<"a", "b">>, <<"c">> >>) =                       *)
  (*         <<"a", "b", ",", "c">>                                        *)
  (*************************************************************************)
  SeqConcat([i \in 1..(2*Len(s)-1) |-> IF i % 2 = 0 THEN <<",">>
                                                    ELSE s[(i + 1) \div 2]])
  
MakeConj(eseq) ==
  (*************************************************************************)
  (* If eseq is a sequence of expressions, then this is their conjunction. *)
  (* Conjunctions are written with the usual binary operator /\ , with     *)
  (* each conjunct enclosed in parentheses.  A translation program would   *)
  (* translate the sequence of expressions into a /\-bulleted list of      *)
  (* conjuncts.                                                            *)
  (*                                                                       *)
  (* The conjunction of an empty sequence of expressions is defined to     *)
  (* equal TRUE. The only way I can think of an explicit formulat TRUE     *)
  (* being created by the translation is in a null ELSE clause, which can  *)
  (* arise in translating a statement like                                 *)
  (*  `.                                                                   *)
  (*    if x > 0 then when y = 0;                                     .'   *)
  (*                                                                       *)
  (*************************************************************************)
  CASE eseq = << >>  -> << "TRUE" >>
  []   Len(eseq) = 1 -> <<"(">> \o eseq[1] \o <<")">>
  []   OTHER -> 
         <<"(">> 
           \o SeqConcat([i \in 1..(2*Len(eseq)-1) |-> 
                         IF i % 2 = 0 THEN IF i > 1 THEN <<")", "/\\", "(">>
                                                    ELSE << >>
                                      ELSE eseq[(i + 1) \div 2]])
           \o <<")">>

MakeUnion(eseq) ==
  (*************************************************************************)
  (* If eseq is a non-empty sequence of expressions, then this is their    *)
  (* union.                                                                *)
  (*************************************************************************)
  CASE eseq = << >>  -> << "Error: empty union" >>
  []   Len(eseq) = 1 -> <<"(">> \o eseq[1] \o <<")">>
  []   OTHER -> 
         <<"(">> \o 
         SeqConcat([i \in 1..(2*Len(eseq)-1) |-> 
                      IF i % 2 = 0 THEN IF i > 1 THEN <<")", "\\union", "(">>
                                                 ELSE << >>
                                   ELSE eseq[(i + 1) \div 2]])
          \o <<")">>

MakeDisj(eseq) ==
  (*************************************************************************)
  (* If eseq is a sequence of expressions, then this is their disjunction. *)
  (* This is only used for making disjunctions of expressions each of      *)
  (* which consists of a single identifier (the name of an action).  It's  *)
  (* therefore not necessary to put parentheses around the disjuncts.  A   *)
  (* translation program would probably also just write the disjunction    *)
  (* using the binary \/ operator.  (However, it would have to use a bit   *)
  (* of cleverness in formatting a disjunction of a large number of        *)
  (* expressions.)                                                         *)
  (*************************************************************************)
  CASE eseq = << >>  -> << "FALSE" >>
  []   Len(eseq) = 1 -> eseq[1]
  []   OTHER -> 
        SeqConcat([i \in 1..(2*Len(eseq)-1) |-> 
                     IF i % 2 = 0 THEN <<"\\/">>
                                  ELSE eseq[(i + 1) \div 2]])

MakeBigDisj(eseq) ==
  (*************************************************************************)
  (* Like MakeDisj, except with eseq a sequence of arbitrary expressions,  *)
  (* so it puts parentheses around each disjunct.                          *)
  (*************************************************************************)
  CASE eseq = << >>  -> << "FALSE" >>
  []   Len(eseq) = 1 -> eseq[1]
  []   OTHER -> 
        <<"(">> \o
        SeqConcat([i \in 1..(2*Len(eseq)-1) |-> 
                     IF i % 2 = 0 THEN <<")", "\\/", "(">>
                                  ELSE eseq[(i + 1) \div 2]])
          \o <<")">>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                 THE DEFINITION OF XlateLabeledStmtSeq                   *)
(*                                                                         *)
(* The next step in the translation is to define the operator              *)
(* XlateLabeledStmtSeq that maps a sequence of statements in LabeledStmt   *)
(* into a single TLA+ action that represents that sequence.  But first, we *)
(* define the operator XlateStmtSeq that translates a sequence of          *)
(* statements in SimpleStmts into a single action                          *)
(***************************************************************************)

XlateStmtSeq(stmts, allVarSeq, localVars, localSub) ==
  (*************************************************************************)
  (* If                                                                    *)
  (*    - stmts is a sequence of statements in SimpleStmt,                 *)
  (*                                                                       *)
  (*    - allVarSeq is the sequence of all algorithm variables,            *)
  (*                                                                       *)
  (*    - localVarSeq is the set of all processor-local variables          *)
  (*      (which is empty only for a uniprocess algorithm)                 *)
  (*                                                                       *)
  (*    - localSub: For a multiprocess algorithm, this expression is the   *)
  (*      subscript added to all local variables.  It equals << "self" >>  *)
  (*      if the statements appear in a procedure or a process set.        *)
  (*                                                                       *)
  (* then this is the TLA+ action that is the translation of the sequence  *)
  (* stmts.                                                                *)
  (*************************************************************************)
  LET allVars == SeqToSet(allVarSeq)
        (*******************************************************************)
        (* The set of all variables.                                       *)
        (*******************************************************************)

      Group(s) ==
        (*******************************************************************)
        (* If element s is the ass field of an assignment, then Group(s)   *)
        (* equals the sequence of records                                  *)
        (* `.                                                              *)
        (*      [var  : Variable,                                          *)
        (*       comp : Seq([sub: Expr, rhs : Expr])]                      *)
        (*                                                             .'  *)
        (* obtained by grouping the assignments in s that set the same     *)
        (* variable.                                                       *)
        (*******************************************************************)
        LET AddOne(ss, elt) ==
              IF \E j \in 1..Len(ss) : ss[j].var = elt.lhs.var
                THEN LET i == CHOOSE j \in 1..Len(ss) : 
                                       ss[j].var = elt.lhs.var
                     IN  [ss EXCEPT ![i].comp = Append(@,
                                                       [sub |-> elt.lhs.sub,
                                                        rhs |-> elt.rhs])]
                ELSE Append(ss,
                            [var  |-> elt.lhs.var,
                             comp |-> <<[sub |-> elt.lhs.sub, 
                                         rhs |-> elt.rhs]>>])
                                                 
           UpTo[i \in 0..Len(s)] ==
              IF i = 0 THEN << >>
                       ELSE AddOne(UpTo[i-1], s[i])
        IN  UpTo[Len(s)]

      PV(vars, expr) == ProcessVars(vars, <<"'">>, expr) 

      XlateAss(assgn, vars) ==
        (*******************************************************************)
        (* If assgn is an assignment statement and vars is a sequence of   *)
        (* variables that have already been assigned values, then this has *)
        (* the two components                                              *)
        (*                                                                 *)
        (*   conj : The action conjuncts describing assgn                  *)
        (*                                                                 *)
        (*   vars : vars \o the sequence of variables assigned values      *)
        (*          by assgn.                                              *)
        (*******************************************************************)
        LET gped  == Group(assgn.ass)
            pvars == SeqToSet(vars)
        IN  [conj |-> 
              [i \in 1..Len(gped) |->
                CASE gped[i].var \in pvars ->
                      <<"Error", ":", "multiple assignment to variable",
                         gped[i].var>>

                []   gped[i].var \notin allVars ->
                      <<"Error", ":", "assignment to undeclared variable",
                         gped[i].var>>
 
                []   OTHER ->
                       <<gped[i].var, "'", "=" >>   
                          \o
                       (IF /\ Len(gped[i].comp) = 1
                           /\ gped[i].comp[1].sub = << >>
                          THEN PV(pvars, gped[i].comp[1].rhs)
                          ELSE <<"[", gped[i].var, "EXCEPT">>
                                 \o
                               CommaConcatSeq([j \in 1..Len(gped[i].comp) |->
                                           <<"!">> \o  
                                            PV(pvars, gped[i].comp[j].sub)
                                             \o
                                           <<"=">>
                                             \o
                                            PV(pvars, gped[i].comp[j].rhs)
                                         ])
                                  \o
                                <<"]">>
                        ) 
               ],
             vars  |-> vars \o [i \in 1..Len(gped) |-> gped[i].var]]

      MakeUnchanged(varSeq) == 
        (*******************************************************************)
        (* If varSeq is a sequence of variables, then this equals a        *)
        (* sequence that is empty if varSeq is empty or else contains a    *)
        (* single element: an Expr that is the UNCHANGED clause for these  *)
        (* variables.                                                      *)
        (*******************************************************************)
        IF varSeq = << >> 
          THEN << >>        
          ELSE << <<"UNCHANGED">> \o
                  (IF Len(varSeq) = 1
                     THEN <<varSeq[1]>>
                     ELSE << "<<" >> \o CommaSeq(varSeq) \o << ">>" >>)
               >>

      \* TLCAlgorithms: Should be 
      \*    XSS[ss \in Seq(SimpleStmt(1)), vars \in Seq(Variable)] 
      XSS[ss \in Object, vars \in Seq(Variable)] ==
        (*******************************************************************)
        (* The record with two fields:                                     *)
        (*                                                                 *)
        (*   conj : the sequence of conjuncts obtained by translating      *)
        (*          the sequence ss, assuming the variables in the         *)
        (*          sequence vars should be primed.                        *)
        (*                                                                 *)
        (*   vars : the concatenation of vars with the sequence of         *)
        (*          variables whose values were set by the statements      *)
        (*          in ss.                                                 *)
        (*******************************************************************)
       IF \A i \in 1..Len(ss) : IsSimpleStmt(ss[i]) THEN
        IF ss = << >>
         THEN  [conj |-> << >>, vars |-> vars]
         ELSE  CASE Head(ss).type = "assignment" ->
                      LET XHd == XlateAss(Head(ss), vars)
                          XTl == XSS[Tail(ss), XHd.vars]
                      IN  [conj |-> XHd.conj \o XTl.conj,
                           vars |-> XTl.vars]
               []   Head(ss).type = "when"  ->
                      LET XTl == XSS[Tail(ss), vars]
                      IN  [conj |-> << PV(SeqToSet(vars), Head(ss).exp)>>
                                      \o XTl.conj,
                           vars |-> XTl.vars]
               []   Head(ss).type = "print"  ->
                      LET XTl == XSS[Tail(ss), vars]
                      IN  [conj |->  << <<"PrintT", "(">> 
                                      \o PV(SeqToSet(vars), Head(ss).exp)
                                      \o <<")">> >>
                                     \o XTl.conj,
                           vars |-> XTl.vars]
               []   Head(ss).type = "assert"  ->
                      LET XTl == XSS[Tail(ss), vars]
                      IN  [conj |->  << <<"Assert", "(">> 
                                      \o PV(SeqToSet(vars), Head(ss).exp)
                                      \o << "," >> \o
      Quote("Failure of assertion at line _, column _.") \o <<")">> >>
          (*****************************************************************)
          (* An implementation should insert the actual line and column    *)
          (* number.                                                       *)
          (*****************************************************************)
                                     \o XTl.conj,
                           vars |-> XTl.vars]
               []   Head(ss).type = "skip"  ->
                      LET XTl == XSS[Tail(ss), vars]
                      IN  [conj |-> XTl.conj,
                           vars |-> XTl.vars]
               []   Head(ss).type = "with" ->
                      LET XLDo == XSS[Head(ss).do, vars]
                          XTl  == XSS[Tail(ss), XLDo.vars]
                      IN [conj |-> 
                           << (IF Head(ss).eqOrIn = "="
                                 THEN <<"LET", Head(ss).var, "==">> \o
                                      PV(SeqToSet(vars), Head(ss).exp) 
                                          \o <<"IN">>
                                 ELSE <<"\\E", Head(ss).var, "\\in">> \o
                                      PV(SeqToSet(vars), Head(ss).exp) 
                                          \o  <<":">>)
                                \o
                              MakeConj(XLDo.conj)
                            >>
                              \o
                            XTl.conj ,
                          vars |-> XTl.vars]

                 [] Head(ss).type = "if" ->
                      LET XLthen   == XSS[Head(ss).then, vars]
                          XLelse   == XSS[Head(ss).else, vars]
                          thenConj == XLthen.conj \o 
                                       MakeUnchanged(SeqMinus(XLelse.vars,
                                                              XLthen.vars))
                          elseConj == XLelse.conj \o 
                                       MakeUnchanged(SeqMinus(XLthen.vars,
                                                              XLelse.vars))
                          tevars   == XLthen.vars \o SeqMinus(XLelse.vars,
                                                              XLthen.vars)
                          XTl == XSS[Tail(ss), tevars]
                          
                      IN  [conj |->
                            << <<"IF">> \o
                                 PV(SeqToSet(vars), Head(ss).test) \o
                                <<"THEN">> \o
                                 MakeConj(thenConj) \o
                                <<"ELSE">> \o
                                 MakeConj(elseConj)
                            >> \o XTl.conj,
                           vars |-> XTl.vars]

                 [] Head(ss).type = "either" ->
                      LET ors == Head(ss).ors
                          XLors[i \in 1..Len(ors)] == XSS[ors[i], vars]

                          (*************************************************)
                          (* Define AllChanged to be the seq of all        *)
                          (* variables in vars together with all           *)
                          (* additional variables changed by any disjunct. *)
                          (*************************************************)
                          CS[i \in 1..Len(ors)] ==
                             IF i = 1 
                               THEN XLors[i].vars
                               ELSE CS[i-1] \o SeqMinus(XLors[i].vars, CS[i-1])
                          AllChanged == CS[Len(ors)]

                          OrConj[i \in 1..Len(ors)] == 
                            XLors[i].conj \o 
                              MakeUnchanged(SeqMinus(AllChanged, 
                                                     XLors[i].vars))
                                                     
                          Xtl == XSS[Tail(ss), AllChanged]
                      IN  [conj |->
                            << MakeBigDisj([i \in 1..Len(ors) |-> MakeConj(OrConj[i])])
                            >> \o Xtl.conj,
                           vars |-> Xtl.vars]

            ELSE ErrorVal

      XSSofStmts == XSS[AddSubscript(localVars, 
                                     <<"[">> \o localSub \o <<"]">>, 
                                     stmts), 
                        << >>]
  IN  MakeConj(XSSofStmts.conj 
                \o 
               MakeUnchanged(SeqMinus(allVarSeq, XSSofStmts.vars)))

XlateLabeledStmtSeq(lstmts, pseq, next, allVarSeq, localVars, localSub) ==
  (*************************************************************************)
  (* If                                                                    *)
  (*    - lstmts is a sequence of statements in LabeledStmt,               *)
  (*                                                                       *)
  (*    - pseq is the sequence of procedures they can call.                *)
  (*                                                                       *)
  (*    - next is the label following the sequence of statements.          *)
  (*                                                                       *)
  (*    - allVarSeq is the sequence of all algorithm variables,            *)
  (*                                                                       *)
  (*    - localVars is the set of all processor-local variables            *)
  (*      (which is empty only for a uniprocess algorithm)                 *)
  (*                                                                       *)
  (*    - localSub: For a multiprocess algorithm, this expression is the   *)
  (*      subscript added to all local variables.  It equals << "self" >>  *)
  (*      if the statements appear in a procedure or a process set.        *)
  (*      In that case, each statement labeled `foo' creates a definition  *)
  (*      `foo(self) == ...'.  Otherwise, a statement labeled `foo'        *)
  (*      creates a definition `foo == ...'.  This argument is ignored     *)
  (*      for a uniprocess algorithm.                                      *)
  (*                                                                       *)
  (* then this is the TLA+ action that describes the sequence of           *)
  (* statements.                                                           *)
  (*************************************************************************)
  LET XlateLabStmt(stmt) ==
        (*******************************************************************)
        (* The translation of a simple labeled statement stmt.             *) 
        (*******************************************************************)
        << stmt.label >> \o
        (IF (localVars # {}) /\ (localSub = <<"self">>)
            THEN <<"(", "self", ")">>
            ELSE << >>)   \o 
         <<"==">> \o          
        XlateStmtSeq(stmt.stmts, allVarSeq, localVars, localSub)

      exploded == FullyExplodeSeq(lstmts, pseq, next)

  IN  SeqConcat([i \in 1..Len(exploded) |-> XlateLabStmt(exploded[i])])
-----------------------------------------------------------------------------
(***************************************************************************)
(*                        FINDING THE VARIABLES                            *)
(*                                                                         *)
(* We now define some operators that collect all the variables declared    *)
(* (explicitly or implicitly) by an algorithm.                             *)
(***************************************************************************)
ProcedureVarSeq(prcd) == [j \in 1..Len(prcd.decls) |-> prcd.decls[j].var]
  (*************************************************************************)
  (* The sequence of declared local variables of procedure prcd.           *)
  (*************************************************************************)

ProcedureParSeq(prcd) == [j \in 1..Len(prcd.params) |-> prcd.params[j].var]
  (*************************************************************************)
  (* The sequence of declared parameters of procedure prcd.                *)
  (*************************************************************************)

ProcessVarSeq(proc) == [j \in 1..Len(proc.decls) |-> proc.decls[j].var]
  (*************************************************************************)
  (* The sequence of local variables of process proc.                      *)
  (*************************************************************************)
       
LocalVars(alg) ==
  (*************************************************************************)
  (* The set of local variables of algorithm alg--that is, the ones that   *)
  (* become array variables.                                               *)
  (*************************************************************************)
  IF alg.type = "uniprocess"
    THEN {}
    ELSE (******************************************************************)
         (* The set of local procedure variables.                          *)
         (******************************************************************)
         SeqToSet(SeqConcat([i \in 1..Len(alg.prcds) |-> 
                               ProcedureVarSeq(alg.prcds[i])]))
           \cup
         (******************************************************************)
         (* The set of procedure parameters.                               *)
         (******************************************************************)
         SeqToSet(SeqConcat([i \in 1..Len(alg.prcds) |-> 
                               ProcedureParSeq(alg.prcds[i])]))
           \cup
         (******************************************************************)
         (* The set of variables declared in process sets, where a process *)
         (* set is defined by a statement of the form                      *)
         (*                                                                *)
         (*    process Foo \in S ...                                       *)
         (******************************************************************)
         SeqToSet(SeqConcat([i \in 1..Len(alg.procs) |-> 
                              IF alg.procs[i].eqOrIn = "\\in"
                                THEN ProcessVarSeq(alg.procs[i])
                                ELSE << >>]))
           \cup {"@pc@"}
           \cup (IF alg.prcds # << >> THEN {"@stack@"} ELSE {})

GlobalVarsSeq(alg) ==
  (*************************************************************************)
  (* The sequence of all global variables of algorithm alg.                *)
  (*************************************************************************)
  [i \in 1..Len(alg.decls) |-> alg.decls[i].var]

NonGlobalVarsSeq(alg) ==
  (*************************************************************************)
  (* The sequence of all variables of algorithm alg except the global ones. *)
  (*************************************************************************)
  SeqConcat([i \in 1..Len(alg.prcds) |-> 
               ProcedureVarSeq(alg.prcds[i]) \o ProcedureParSeq(alg.prcds[i])])
    \o
  (IF alg.type = "multiprocess"
     THEN SeqConcat([i \in 1..Len(alg.procs) |-> ProcessVarSeq(alg.procs[i])])
     ELSE << >>)
    \o
  <<"@pc@">>
    \o
  (IF alg.prcds # << >> THEN <<"@stack@">> ELSE << >>)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                          FINDING THE LABELS                             *)
(*                                                                         *)
(* We define LabelsOf(sseq) to be a sequence consisting of all the labels  *)
(* in the sequence sseq of elements of LabeledStmt.                        *)
(***************************************************************************)
LabelsOf(sseq) ==
  (*************************************************************************)
  (* Correction of 27 June 2005                                            *)
  (*                                                                       *)
  (* This definition was completely rewritten.                             *)
  (*                                                                       *)
  (* The original definition was wrong because it did not obtain the       *)
  (* labels from a <LabelIf> node inside the unlabDo field of a <While> or *)
  (* inside the unlabThen or unlabElse field of a <LatelIf> node.          *)
  (*************************************************************************)
  LET LSSeq[lss \in Object] ==
        (*******************************************************************)
        (* The sequence of labels in a sequence lss of <LabeledStmt>s.     *)
        (*******************************************************************)
        LET LS[ls \in Object] ==
              (*************************************************************)
              (* The sequence of labels inside a <LabSeq> ls.              *)
              (*************************************************************)
              IF ls = << >>
                THEN << >>
                ELSE LET last == ls[Len(ls)]
                     IN  IF last.type \in {"labelIf", "labelEither"}
                           THEN IF last.type = "labelIf"
                                 THEN LS[last.unlabThen] \o 
                                      LSSeq[last.labThen]  \o 
                                      LS[last.unlabElse] \o 
                                      LSSeq[last.labElse]  
                                 ELSE \* last.type = "labelEither"
                                      SeqConcat(
                                       [i \in 1..Len(last.clauses) |->
                                         LS[last.clauses[i].unlabOr] \o
                                         LSSeq[last.clauses[i].labOr] ] )
                           ELSE << >>
        IN  IF lss = << >>
              THEN << >>
              ELSE <<lss[1].label>> \o
                     ( IF lss[1].stmts[1].type = "while"
                         THEN LS[lss[1].stmts[1].unlabDo] \o
                              LSSeq[lss[1].stmts[1].labDo] \o
                              LS[Tail(lss[1].stmts)]
                         ELSE LS[lss[1].stmts]  )  
                      \o
                     LSSeq[Tail(lss)]
  IN  LSSeq[sseq]

-----------------------------------------------------------------------------
(***************************************************************************)
(*                      TRANSLATING A PROCEDURE                            *)
(*                                                                         *)
(* We now define the operators that construct the next-state action and    *)
(* the initial predicate of a procedure.                                   *)
(***************************************************************************)
PrcdNext(prcd, pseq, allVarSeq, localVars) ==
  (*************************************************************************)
  (* The Expr containing the TLA+ definition of procedure prcd's           *)
  (* next-state action, preceded by all action definitions of its body,    *)
  (* where                                                                 *)
  (*                                                                       *)
  (*   - pseq is the sequence of all procedures.                           *)
  (*                                                                       *)
  (*   - allVarSeq is the sequence of all algorithm variables,             *)
  (*                                                                       *)
  (*   - localVars is the set of all processor-local variables             *)
  (*     (which is empty only for a uniprocess algorithm)                  *)
  (*                                                                       *)
  (* If this is a multiprocess algorithm, then the next-state action       *)
  (* has the form                                                          *)
  (*                                                                       *)
  (*    name == \E self \in ProcSet : ...                                  *)
  (*************************************************************************)
  XlateLabeledStmtSeq(prcd.body, pseq, "Error", allVarSeq, localVars, 
                           <<"self">>)
       \o
  <<prcd.name>> 
       \o 
  (IF localVars = {} THEN << >>
                     ELSE <<"(", "self", ")">>)
     \o
  <<"==">> 
      \o
  (LET labels == LabelsOf(prcd.body) 
   IN  MakeDisj([i \in 1..Len(labels) |->
              IF localVars = {} 
                THEN <<labels[i]>>
                ELSE <<labels[i], "(", "self", ")">>]))

PrcdInit(prcd, Multiprocess) ==
  (*************************************************************************)
  (* The TLA+ expression that is the initial predicate for procedure prcd, *)
  (* where Multiprocess is a BOOLEAN that is true iff this is a            *)
  (* multiprocess algorithm.  Note that for a multiprocess algorithm,      *)
  (* ProcSet is the set of all process identifiers.  The expression        *)
  (* includes a comment identifying its source, because we don't bother    *)
  (* defining a separate initial predicate for each procedure or process.  *)
  (*                                                                       *)
  (* Note: Because the parameters and local variables are set when the     *)
  (* procedure is called, these variables are initialized to the arbitrary *)
  (* value `{}'.                                                           *)
  (*************************************************************************)
  LET pdecls == prcd.params \o prcd.decls
      pvars  == {pdecls[i].var : i \in 1..Len(pdecls)}
      varval(i) == ProcessVars(pvars, <<"[", "self", "]">>, pdecls[i].val)
  IN  << "(*", "Procedure", prcd.name, "*)">> \o
      MakeConj([i \in 1..Len(pdecls) |-> 
                 <<pdecls[i].var, "=">> \o
                 (IF Multiprocess 
                    THEN <<"[", "self", "\\in", "ProcSet", 
                              "|->">> \o  varval(i) \o << "]">>
                    ELSE pdecls[i].val  )])
-----------------------------------------------------------------------------
(***************************************************************************)
(*                      TRANSLATING A PROCESS                              *)
(*                                                                         *)
(* We now define the operators that construct the next-state action and    *)
(* the initial predicate of a process.                                     *)
(***************************************************************************)
ProcNext(proc, pseq, allVarSeq, localVars) ==
  (*************************************************************************)
  (* The Expr containing the TLA+ definition of process proc's next-state  *)
  (* action, preceded by all action definitions of its body, where         *)
  (*                                                                       *)
  (*   - pseq is the sequence of all procedures.                           *)
  (*                                                                       *)
  (*   - allVarSeq is the sequence of all algorithm variables,             *)
  (*                                                                       *)
  (*   - localVars is the set of all processor-local variables             *)
  (*                                                                       *)
  (* If proc is a process set, then the next-state action has the form     *)
  (* name(self) ==  ...                                                    *)
  (*************************************************************************)
  XlateLabeledStmtSeq(proc.body, pseq, "Done", allVarSeq, localVars,
     IF proc.eqOrIn = "=" THEN proc.id ELSE <<"self">> )
     \o
    
  (IF proc.eqOrIn = "=" THEN <<proc.name, "==">> 
                        ELSE <<proc.name, "(", "self", ")" , "==">> )
     \o
  (LET labels == LabelsOf(proc.body) 
   IN  MakeDisj([i \in 1..Len(labels) |->
              IF proc.eqOrIn = "=" 
                THEN <<labels[i]>>
                ELSE <<labels[i], "(", "self", ")">>]))


ProcInit(proc) ==
  (*************************************************************************)
  (* The TLA+ expression that is the initial predicate for process proc.   *)
  (* The expression includes a comment identifying its source, because we  *)
  (* don't bother defining a separate initial predicate for each procedure *)
  (* or process.                                                           *)
  (*************************************************************************)
  LET procvars  == {proc.decls[i].var : i \in 1..Len(proc.decls)}
      varval(i) == ProcessVars(procvars, <<"[", "self", "]">>, 
                                proc.decls[i].val)
  IN  << "(*", "Process", proc.name, "*)">> \o
       MakeConj([i \in 1..Len(proc.decls) |-> 
                  <<proc.decls[i].var, proc.decls[i].eqOrIn>> 
                   \o
                  (IF proc.eqOrIn = "="
                     THEN proc.decls[i].val
                     ELSE IF proc.decls[i].eqOrIn = "="
                            THEN <<"[", "self", "\\in">> \o proc.id \o
                                 <<"|->">> \o varval(i)  \o <<"]">>
                            ELSE <<"[">> \o proc.id \o <<"->">> \o
                                 varval(i) \o <<"]">>)])

-----------------------------------------------------------------------------
(***************************************************************************)
(*              THE DEFINITION OF `Translation'                            *)
(*                                                                         *)
(* We now put all the pieces together to define                            *)
(* Translation(alg, fairnessOption) for an algorithm alg and a fairness    *)
(* option fairnessOption that is either "", "wf", or "sf".                 *)
(***************************************************************************)
Translation(alg, fairnessOption) ==
  LET localVars  == LocalVars(alg)
      allVarsSeq == GlobalVarsSeq(alg) \o NonGlobalVarsSeq(alg)

      GlobalVarDecl == 
        (*******************************************************************)
        (* The global VARIABLES declaration.  We add "@pc@" and "@stack@" to   *)
        (* the global variable declarations so they can be mentioned in a  *)
        (* "defines" definition.                                           *)
        (*******************************************************************)
        <<"VARIABLES">> \o 
           CommaSeq(GlobalVarsSeq(alg) \o <<"@pc@">> \o
                      IF alg.prcds # << >> THEN <<"@stack@">>
                                           ELSE << >>)

      NonGlobalVarDecl == 
        (*******************************************************************)
        (* The non-global VARIABLES declaration.  We remove "@pc@" and       *)
        (* "@stack@" from it.                                                *)
        (*******************************************************************)
        LET NoPCorStack(a) == a \notin {"@pc@", "@stack@"}
            ngvseq == SelectSeq(NonGlobalVarsSeq(alg), NoPCorStack)
        IN  IF ngvseq = << >> THEN << >>
                              ELSE <<"VARIABLES">> \o CommaSeq(ngvseq)

      AllVarDecl == <<"VARIABLES">> \o CommaSeq(allVarsSeq)
        (*******************************************************************)
        (* A declaration of all variables, to be used if there's no        *)
        (* `define' statement.  This declaration is never empty because it *)
        (* contains pc.                                                    *)
        (*******************************************************************)

      varsDef ==
        (*******************************************************************)
        (* The definition of the tuple vars of all variables.              *)
        (*******************************************************************)
        << "vars", "==", "<<" >> \o CommaSeq(allVarsSeq) \o << ">>" >> 

      GlobalVarsInit ==
        (*******************************************************************)
        (* The initial predicate for the global variables.                 *)
        (*******************************************************************)
        << "(*", "Global Variables", "*)" >> \o 
        MakeConj([i \in 1..Len(alg.decls) |-> 
                    <<alg.decls[i].var, alg.decls[i].eqOrIn>> \o
                       alg.decls[i].val])
                 
      PrcdsInit == 
        (*******************************************************************)
        (* The sequence of initial predicates for procedures.              *)
        (*******************************************************************)
        [i \in 1..Len(alg.prcds) |-> PrcdInit(alg.prcds[i],
                                              alg.type = "multiprocess")]

      ProcsInit ==
        (*******************************************************************)
        (* The sequence of initial predicates for processes, if this is a  *)
        (* multiprocess algorithm.                                         *)
        (*******************************************************************)
        [i \in 1..Len(alg.procs) |-> ProcInit(alg.procs[i])]

      StackInit ==
        (*******************************************************************)
        (* The initial predicate for the stack variable, if that variable  *)
        (* occurs.                                                         *)
        (*******************************************************************)
        IF alg.type = "multiprocess" 
          THEN <<"@stack@", "=", "[", "self", "\\in", "ProcSet", "|->",
                   "<<", ">>", "]" >>
          ELSE <<"@stack@", "=", "<<", ">>">>

      pcInit ==
        (*******************************************************************)
        (* The initial predicate for the variable pc.                      *)
        (*******************************************************************)
        IF alg.type = "multiprocess" 
          THEN <<"@pc@", "=", "[", "self", "\\in", "ProcSet", "|->", "CASE">> 
                   \o
               SeqConcat([i \in 1..Len(alg.procs) |->
                           (IF i > 1 THEN << "[]" >> ELSE << >>) \o
                           <<"self", alg.procs[i].eqOrIn>> \o
                            alg.procs[i].id \o <<"->">> \o
                            Quote(alg.procs[i].body[1].label)])               
                   \o
               << "]" >>
               

          ELSE <<"@pc@", "=">> \o Quote(alg.body[1].label)
        
      InitDef ==
        (*******************************************************************)
        (* The definition of the initial predicate Init.                   *)
        (*******************************************************************)
        << "Init", "==">> \o
        MakeConj(
          (IF alg.decls # << >> THEN <<GlobalVarsInit>> ELSE << >>) \o
          PrcdsInit \o
          (IF alg.type = "multiprocess" THEN ProcsInit ELSE << >>) \o
          (IF alg.prcds # << >> THEN <<StackInit>> ELSE << >>) \o
          <<pcInit>>
         )

      ProcSetDef ==
        (*******************************************************************)
        (* If this is a multiprocess algorithm, then this is the definition  *)
        (* of ProcSet.                                                     *)
        (*******************************************************************)
        LET procIds ==
              (*************************************************************)
              (* The sequence of single process ids.                       *)
              (*************************************************************)
              SeqConcat([i \in 1..Len(alg.procs) |->
                          IF alg.procs[i].eqOrIn = "="
                            THEN <<alg.procs[i].id>>
                            ELSE << >>] )            

            procSets ==
              (*************************************************************)
              (* The sequence of process set id sets.                      *)
              (*************************************************************)
              SeqConcat([i \in 1..Len(alg.procs) |->
                          IF alg.procs[i].eqOrIn = "\\in"
                            THEN <<alg.procs[i].id>>
                            ELSE << >>] )  
       IN <<"ProcSet", "==">> \o
          (IF procIds # << >>
             THEN <<"{">> \o CommaConcatSeq(procIds) \o <<"}">>
             ELSE << >>) \o
          (IF (procIds # << >>) /\ (procSets # << >>) 
             THEN <<"\\union">>
             ELSE << >> ) \o
          (IF procSets # << >>
             THEN MakeUnion(procSets) 
             ELSE << >>) 

      PrcdsNextDef ==
        (*******************************************************************)
        (* The definitions of the next-state actions of all procedures.    *)
        (*******************************************************************)
        SeqConcat([i \in 1..Len(alg.prcds) |-> 
                    PrcdNext(alg.prcds[i], alg.prcds, allVarsSeq, localVars)])

      ProcsNextDef ==
        (*******************************************************************)
        (* For a multiprocess algorithm, the definitions of the next-state *)
        (* actions of all processes.                                       *)
        (*******************************************************************)
        SeqConcat([i \in 1..Len(alg.procs) |-> 
                    ProcNext(alg.procs[i], alg.prcds, allVarsSeq, localVars)
                  ] )
      MainNextDef ==
        (*******************************************************************)
        (* For a uniprocess algorithm, the definitions of the actions of   *)
        (* the main body of the algorithm.                                 *)
        (*******************************************************************)
        XlateLabeledStmtSeq(alg.body, alg.prcds, "Done", allVarsSeq, 
                              localVars, << >>)

      NextDef ==
        (*******************************************************************)
        (* The definition of the next-state action.                        *)
        (*******************************************************************)
        << "Next", "==" >> 
          \o
        MakeDisj(
          [i \in 1..Len(alg.prcds) |-> 
             IF alg.type = "multiprocess"
               THEN <<"(", "\\E", "self", "\\in", "ProcSet", ":" ,
                          alg.prcds[i].name, "(", "self", ")", ")">>
               ELSE <<alg.prcds[i].name>>] 
             \o
          (IF alg.type = "multiprocess"
            THEN [i \in 1..Len(alg.procs) |-> 
                    IF alg.procs[i].eqOrIn = "="
                      THEN <<alg.procs[i].name>>
                      ELSE <<"(", "\\E", "self", "\\in">> \o
                           alg.procs[i].id \o 
                          <<":", alg.procs[i].name, "(", "self", ")", ")" >> ]
            ELSE [i \in 1.. Len(LabelsOf(alg.body)) |->
                           <<LabelsOf(alg.body)[i]>>]          )
             \o
          << << "(*", "Disjunct to prevent deadlock on termination", "*)" >>
                \o
              <<"(">> 
                \o
              MakeConj(<< (IF alg.type = "multiprocess" 
                             THEN << "\\E", "self", "\\in", "ProcSet", ":",
                                     "@pc@", "[", "self", "]", "=">>
                             ELSE <<"@pc@", "=">>) 
                             \o 
                           Quote("Done"),
                           << "UNCHANGED", "vars" >>
                       >>) 
                 \o 
              <<")">> 
           >>)

      Fairness(wsf) ==
        (*******************************************************************)
        (* The fairness condition for the algorithm, where wsf is either   *)
        (* "WF_vars" or "SF_vars"                                          *)
        (*******************************************************************)
        IF alg.type = "uniprocess"
          THEN << wsf, "(", "Next", ")" >>
          ELSE MakeConj( [i \in 1..Len(alg.procs) |->
                           IF alg.procs[i].eqOrIn = "="
                             THEN << wsf, "(", alg.procs[i].name , ")" >>
                             ELSE << "\\A", "self", "\\in">> 
                                    \o alg.procs[i].id 
                                    \o << ":",
                                      wsf, "(", alg.procs[i].name , 
                                                "(", "self", ")", ")" >>
                         ] \o
                         [i \in 1..Len(alg.prcds) |->  
                               <<"\\A", "self", "\\in", "ProcSet", ":", 
                                    wsf, "(", alg.prcds[i].name, 
                                         "(", "self", ")", ")" >>
                              
                         ] ) 

    FixPCandStack(seq) ==
      [i \in 1..Len(seq) |-> IF seq[i] = "@pc@" 
                               THEN "pc"
                               ELSE IF seq[i] = "@stack@" 
                                      THEN "stack"
                                      ELSE seq[i] ]
 IN  FixPCandStack(
     (IF alg.defs = << >>
       THEN AllVarDecl
       ELSE GlobalVarDecl  \o alg.defs \o NonGlobalVarDecl)
        \o
      varsDef 
        \o
      (IF alg.type = "multiprocess" THEN ProcSetDef ELSE << >>) 
        \o
      InitDef 
         \o
      PrcdsNextDef 
         \o
      (IF alg.type = "multiprocess" THEN ProcsNextDef ELSE MainNextDef) 
         \o
      NextDef 
         \o 
      << "Spec", "==", "Init", "/\\", "[]", "[", "Next", "]_", "vars" >>
         \o
       ( CASE fairnessOption = ""      -> << >>
          [] fairnessOption = "wf"     -> <<"/\\">> \o Fairness("WF_vars")
          [] fairnessOption = "sf"     -> <<"/\\">> \o Fairness("SF_vars")
          [] fairnessOption = "wfNext" -> 
                    << "/\\", "WF_vars", "(", "Next", ")" >>
       )
          \o
      << "Termination", "==", "<>", "(" >> \o 
        (IF alg.type = "uniprocess"  
          THEN <<"@pc@", "=" >> 
          ELSE <<"\\A", "self" , "\\in" , "ProcSet", ":", 
                     "@pc@", "[", "self", "]", "=" >> )
         \o Quote("Done") \o <<")">> 
      )

PrintSeq(s) ==
\A i \in 0..(Len(s) \div 25) :
     IF 25*(i + 1) > Len(s)
          THEN PrintT(SubSeq(s, 25*i+1, Len(s)))
          ELSE PrintT(SubSeq(s, 25*i + 1, 25*(i + 1)))

MCIsRecord(r, D) == 
 (DOMAIN r = D) /\ (r = [x \in D |-> r[x]])

ASSUME 
 /\ IF IsAlgorithm(ast)
      THEN PrintSeq(Translation(ast, fairness))
      ELSE Print("<<Error", TRUE)
 /\ PrintT("@@END@@")
=============================================================================
As of 28 June 2005
Total number of non-comment lines: 938
Number of those lines through definition of IsAlgorithm: 159
 