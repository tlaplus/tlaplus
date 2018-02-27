package org.lamport.tla.toolbox.editor.basic.pcal;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IPCalReservedWords {
	public final static String ALGORITHM = "--algorithm";

	public final static String ASSERT = "assert";
	public final static String AWAIT = "await";
	public final static String BEGIN = "begin";
	public final static String CALL = "call";
	public final static String DEFINE = "define";
	public final static String DO = "do";
	public final static String EITHER = "either";
	public final static String ELSE = "else";
	public final static String ELSEIF = "elseif";
	public final static String END = "end";
	public final static String GOTO = "goto";
	public final static String IF = "if";
	public final static String MACRO = "macro";
	public final static String OR = "or";
	public final static String PRINT = "print";
	public final static String PROCEDURE = "procedure";
	public final static String PROCESS = "process";
	public final static String FAIR = "fair";
	public final static String RETURN = "return";
	public final static String SKIP = "skip";
	public final static String THEN = "then";
	public final static String VARIABLE = "variable";
	public final static String VARIABLES = "variables";
	public final static String WHILE = "while";
	public final static String WITH = "with";
	// public final static String WHEN = "";

	public final static String[] ALL_WORDS_ARRAY = new String[] { ASSERT, BEGIN, CALL, DO, EITHER, ELSE, ELSEIF, END,
			GOTO, IF, MACRO, OR, PRINT, PROCEDURE, PROCESS, FAIR, RETURN, SKIP, THEN, VARIABLE, VARIABLES, WHILE,
			WITH };

	// Just the complete PlusCal BNF
	public static final String ALGORITHM_HELP = "<Algorithm> ::= [--algorithm | --fair algorithm] <name>\r\n"
			+ "		{<VarDecls>{0,1}\r\n" + "		<Definitions>{0,1}\r\n" + "		<Macro>*\r\n"
			+ "		<Procedure>*\r\n" + "		[<CompoundStmt> | [fair [+]{0,1}]{0,1}<Process>+] }\r\n" + "\r\n"
			+ "<Definitions> ::= define { <Defs> } [;]{0,1}\r\n" + "\r\n"
			+ "<Macro> ::= macro<Name> ( [ <Variable>[, <Variable>]* ]{0,1} )\r\n" + "		<CompoundStmt> [;]{0,1}\r\n"
			+ "\r\n" + "<Procedure> ::= procedure<Name> ( [<PVarDecl> [,<PVarDecl>]*]{0,1} )\r\n"
			+ "		<PVarDecls>{0,1}\r\n" + "		<CompoundStmt> [;]{0,1}\r\n" + "\r\n"
			+ "<Process> ::= [fair [+]{0,1}]{0,1} process (<Name> [=|\\in] <Expr> )\r\n" + "		<VarDecls>{0,1}\r\n"
			+ "		<CompoundStmt> [;]{0,1}\r\n" + "\r\n" + "<VarDecls> ::= [variable | variables] <VarDecl>+\r\n"
			+ "<VarDecl> ::=<Variable> [[=|\\in] <Expr>]{0,1} [;|,]\r\n" + "\r\n"
			+ "<PVarDecls> ::= [variable | variables] [hPVarDecl> [;|,]]+\r\n"
			+ "<PVarDecl> ::=<Variable> [=<Expr>]{0,1}\r\n" + "\r\n"
			+ "<CompoundStmt> ::= {<Stmt> [;<Stmt>]* [;]{0,1} }\r\n"
			+ "<Stmt> ::= [<Label> : [+|-]{0,1}]{0,1} [<UnlabeledStmt> |<CompoundStmt>]\r\n"
			+ "<UnlabeledStmt> ::=<Assign> |<If> |<While> |<Either> |<With> | <Await> |<Print> |<Assert> |<Skip> |<Return> | <Goto> |<Call> |<MacroCall>\r\n"
			+ "\r\n" + "<Assign> ::=<LHS> := <Expr> [||<LHS> :=<Expr>]*\r\n"
			+ "<LHS> ::=<Variable> [[<Expr> [,<Expr>]*] | .<Field>]*\r\n" + "\r\n"
			+ "<If> ::=>f (<Expr> )<Stmt> [else<Stmt>]{0,1}\r\n" + "\r\n" + "<While> ::= while (<Expr>)<Stmt>\r\n"
			+ "\r\n" + "<Either> ::= either<Stmt> [or<Stmt>]+\r\n" + "<With> ::= with (<Variable> [=|\\in] <Expr>\r\n"
			+ "			[[; | ,]<Variable> [=|\\in] <Expr>]* [; | ,]{0,1}\r\n" + "		)<Stmt>\r\n" + "\r\n"
			+ "<Await> ::= [await | when]<Expr>\r\n" + "\r\n" + "<Print> ::= print<Expr>\r\n" + "\r\n"
			+ "<Assert> ::= assert<Expr>\r\n" + "\r\n" + "<Skip> ::= skip\r\n" + "\r\n" + "<Return> ::= return\r\n"
			+ "\r\n" + "<Goto> ::= goto<Label>\r\n" + "\r\n" + "<Call> ::= call<MacroCall>\r\n" + "\r\n"
			+ "<MacroCall> ::=<Name> ( [<Expr> [,<Expr>]*]{0,1} )\r\n" + "\r\n"
			+ "<Variable> ::= A TLA+ identifier that is not a PlusCal reserved word and\r\n"
			+ "is not pc, stack, or self.\r\n" + "\r\n" + "<Field> ::= A TLA+ record-component label.\r\n" + "\r\n"
			+ "<Name> ::= A TLA+ identifier that is not a PlusCal reserved word.\r\n" + "\r\n"
			+ "<Label>  ::= A TLA+ identifier that is not a PlusCal reserved word and\r\n" + "is not Done or Error.\r\n"
			+ "\r\n" + "<Expr> ::= A TLA+ expression not containing a PlusCal reserved word\r\n" + "or symbol.\r\n"
			+ "\r\n" + "<Defs> ::= A sequence of TLA+ definitions not containing a PlusCal\r\n"
			+ "reserved word or symbol.";

	public static final String ASSIGN_HELP = "<Assign> ::= <LHS> := <Expr> [ || <LHS> := <Expr>]*\r\n"
			+ "\t<LHS> ::= <Variable> [[ <Expr> [, <Expr>]* ] | . <Field>]*\n\n"
			+ "An assignment is either an assignment to a variable such as\r\n" + "\ty := A + B\r\n"
			+ "or else an assignment to a component, such as\r\n" + "\tx.foo[i+1] := y+3\r\n"
			+ "If the current value of x is a record with a foo component that is a function\r\n"
			+ "(array), then this assignment sets the component x.foo[i+1] to the current\r\n"
			+ "value of y+3. The value of this assignment is undefined if the value of x is not\r\n"
			+ "a record with a foo component, or if x.foo is not a function. Therefore, if\r\n"
			+ "such an assignment appears in the code, then x will usually be initialized to\r\n"
			+ "an element of the correct “type”, or to be a member of some set of elements\r\n"
			+ "of the correct type. For example, the declaration\r\n" + "\tvariable x \\in [bar : BOOLEAN,\r\n"
			+ "\t\tfoo : [1..N |-> {\"on\", \"off\"}] ] ;\r\n"
			+ "asserts that initially x is a record with a bar component that is a Boolean\r\n"
			+ "(equal to TRUE or FALSE) and a foo component that is a function with\r\n"
			+ "domain 1.. N such that x.foo[i] equals either “on” or “off” for each i in\r\n" + "1.. N.\r\n"
			+ "An assignment statement consists of one or more assignments, separated\r\n"
			+ "by “||” tokens, ending with a semicolon. An assignment statement contain-\r\n"
			+ "ing more than one assignment is called a multiple assignment. A multiple\r\n"
			+ "assignment is executed by first evaluating the right-hand sides of all its as-\r\n"
			+ "signments, and then performing those assignments from left to right. For\r\n"
			+ "example, if i = j = 3, then executing\r\n" + "\tx[i] := 1 || x[j] := 2\r\n" + "sets x[3] to 2.\r\n"
			+ "Assignments to the same variable cannot be made in two different as-\r\n"
			+ "signment statements within the same step. In other words, in any control\r\n"
			+ "path, a label must come between two statements that assign to the same\r\n"
			+ "variable. However, assignments to components of the same variable may\r\n"
			+ "appear in a single multiple assignment, as in\r\n" + "\tx.foo[7] := 13 || y := 27 || x.bar := x.foo";
	public static final String MULTI_ASSIGN_HELP = "A multiple\r\n"
			+ "assignment is executed by first evaluating the right-hand sides of all its as-\r\n"
			+ "signments, and then performing those assignments from left to right. For\r\n"
			+ "example, if i = j = 3, then executing\r\n" + "\tx[i] := 1 || x[j] := 2\r\n" + "sets x[3] to 2.\r\n"
			+ "Assignments to the same variable cannot be made in two different as-\r\n"
			+ "signment statements within the same step. In other words, in any control\r\n"
			+ "path, a label must come between two statements that assign to the same\r\n"
			+ "variable. However, assignments to components of the same variable may\r\n"
			+ "appear in a single multiple assignment, as in\r\n" + "\tx.foo[7] := 13 || y := 27 || x.bar := x.foo";
	public static final String DEFINE_HELP = "<Definitions> ::= define { <Defs> }[;]{0,1}\n\n"
			+ "An algorithm’s expressions can use any operators defined in the TLA + mod-\r\n"
			+ "ule before the “BEGIN TRANSLATION” line. Since the TLA + declaration of\r\n"
			+ "the algorithm’s variables follows that line, the definitions of those opera-\r\n"
			+ "tors can’t mention any algorithm variables. The PlusCal define statement\r\n"
			+ "allows you to write TLA + definitions of operators that depend on the algo-\r\n"
			+ "rithm’s global variables. For example, suppose the algorithm begins:\r\n" + "\t--algorithm Test {\r\n"
			+ "\tvariables x \\in 1..N ; y ;\r\n" + "\tdefine { zy == y*(x+y)\r\n" + "\t\tzx(a) == x*(y-a) }\r\n"
			+ "\t...\r\n" + "The operators zy and zx can then be\r\n"
			+ "used in expressions anywhere in the remainder of the algorithm. Observe\r\n"
			+ "that there is no semicolon or other separator between the two definitions.\r\n"
			+ "Section 5.11 on page 55 describes how to write TLA + definitions.\r\n"
			+ "The variables that may appear within the define statement are the ones\r\n"
			+ "declared in the variable statement that immediately precedes it and that\r\n"
			+ "follows the algorithm name, as well as the variable pc and, if there is a pro-\r\n"
			+ "cedure, the variable stack . Local process and procedure variables may not\r\n"
			+ "appear in the define statement. The define statement’s definitions need\r\n"
			+ "not mention the algorithm’s variables. You might prefer to put definitions\r\n"
			+ "in the define statement even when they don’t have to go there. However,\r\n"
			+ "remember that the define statement cannot mention any symbols defined\r\n"
			+ "or declared after the “END TRANSLATION” line; and the symbols it defines\r\n"
			+ "cannot be used before the “BEGIN TRANSLATION” line.\r\n"
			+ "Definitions, including ones in a define statement, are not expanded\r\n"
			+ "in the PlusCal to TLA + translation. All defined symbols appear in the\r\n"
			+ "translation exactly as they appear in the PlusCal code.";
	public static final String MACRO_HELP = "<Macro> ::= macro <Name> ( [<Variable>[, <Variable>]∗]{0,1})\n"
			+ "\t<CompoundStmt>[;]{0,1}\n\n"
			+ "A macro is like a procedure, except that a call of a macro is expanded at\r\n"
			+ "translation time. You can think of a macro as a procedure that is executed\r\n"
			+ "within the step from which it is called.\r\n"
			+ "A macro definition looks much like a procedure declaration - for example:\r\n"
			+ "\tmacro P(s, i) { await s ≥ i ;\r\n" + "\t\ts := s - i }\r\n"
			+ "The difference is that the body of the macro may contain no labels, no\r\n"
			+ "while, call, return, or goto statement. It may contain a call of a previously\r\n"
			+ "defined macro. Macro definitions come right after any global variable\r\n"
			+ "declarations and define section.\r\n"
			+ "A macro call is like a procedure call, except with the call omitted—for\r\n" + "example:\r\n"
			+ "\tP(sem, y + 17) ;\r\n"
			+ "The translation replaces the macro call with the sequence of statements ob-\r\n"
			+ "tained from the body of the macro definition by substituting the arguments\r\n"
			+ "of the call for the definition’s parameters. Thus, this call of the P macro\r\n" + "expands to:\r\n"
			+ "\tawait sem ≥ (y + 17) ;\r\n" + "\tsem := sem - (y + 17) ;\n"
			+ "When translating a macro call, substitution is syntactic in the sense that\r\n"
			+ "the meaning of any symbol in the macro definition other than a parameter\r\n"
			+ "is the meaning it has in the context of the call. For example, if the body of\r\n"
			+ "the macro definition contains a symbol q and the macro is called within a\r\n"
			+ "\"with ( q \\in ... )\" statement, then the q in the macro expansion is the q\r\n"
			+ "introduced by the with statement.\r\n"
			+ "When replacing a macro by its definition, the translation replaces every\r\n"
			+ "instance of a macro parameter id in an expression within the macro body\r\n"
			+ "by the corresponding expression. Every instance includes any uses of id as\r\n"
			+ "a bound variable, as in the expression\r\n" + "\t[id \\id 1..N |-> false]\r\n"
			+ "The substitution of an expression like y + 17 for id here will cause a mys-\r\n"
			+ "terious error when the translation is parsed. When using PlusCal, obey the\r\n"
			+ "TLA+ convention of never assigning a new meaning to any identifier that\r\n" + "already has a meaning.";
	public static final String GOTO_HELP = "<Goto> ::= goto <Label>\n\nExecuting the statement\r\n" + "\tgoto lab ;\r\n"
			+ "ends the execution of the current step and causes control to go to the state-\r\n"
			+ "ment labeled lab. In any control path, a goto must be immediately followed\r\n"
			+ "by a label. (Remember that the control path by definition ignores the mean-\r\n"
			+ "ing of the goto and continues to what is syntactically the next statement.)\r\n"
			+ "It is legal for a goto to jump into the middle of a while or if statement,\r\n"
			+ "but this sort of trickery should be avoided.";
	public static final String SKIP_HELP = "<Skip> ::= skip\n\nThe statement skip; does nothing.";
	public static final String ASSERT_HELP = "<Assert> ::= assert <Expr>\n\n" + "The statement" + "\tassert expr;"
			+ "is equivalent to skip if expression expr equals true. If expr equals false,\r\n"
			+ "executing the statement causes TLC to produce an error message saying\r\n"
			+ "that the assertion failed and giving the location of the assert statement.\r\n"
			+ "TLC may report a failed assertion even if the step containing the assert\r\n"
			+ "statement is not executed because of an await statement that appears later\r\n" + "in the step.\r\n"
			+ "An algorithm containing an assert statement must be in a module that\r\n" + "extends the TLC module.";
	public static final String PRINT_HELP = "<Print> ::= print <Expr>\n\n" + "Execution of the statement\r\n"
			+ "\tprint expr;\r\n"
			+ "is equivalent to skip, except it causes TLC to print the current value of expr.\r\n"
			+ "TLC may print the value even if the step containing the print statement is\r\n"
			+ "not executed because of an await statement that appears later in the step.\r\n"
			+ "An algorithm containing a print statement must be in a module that\r\n" + "extends the TLC module.";
	public static final String RETURN_HELP = "<Return> ::= return\n\nSee procedure!";
	public static final String AWAIT_HELP = "<Await> ::= [ await | when ] <Expr>\n\nA step containing the statement await expr can be executed only when the\r\n"
			+ "value of the Boolean expression expr is TRUE. Although it usually appears\r\n"
			+ "at the beginning of a step, an await statement can appear anywhere within\r\n" + "the step.\r\n"
			+ "\ta : x := y + 1 ;\r\n" + "\tb: ...\r\n"
			+ "The step from a to b can be executed only when the current value of y+1\r\n"
			+ "is positive. (Remember that an entire step must be executed; part of a step\r\n"
			+ "cannot be executed by itself.) The keyword when can be used instead of\r\n" + "await.";
	public static final String WITH_HELP = "<With> ::= with ( <Variable> [=|\\in] <Expr>\r\n"
			+ "\t[ [;|,] <Variable> [=|\\\\in] <Expr> ]* [;|,]{0,1}\r\n" + "\t) <Stmt>\n\n" + "The statement\r\n"
			+ "\twith ( id \\in S ) body\r\n"
			+ "is executed by executing the (possibly compound) statement body with identifier\r\n"
			+ " id equal to a nondeterministically chosen element of S.\r\n" + "Execution is impossible if S is empty.";
	public static final String EITHEROR_HELP = "<Either> ::= either <Stmt> [or <Stmt> ]+\n\n"
			+ "The either statement has the form:\r\n" + "\teither clause 1\r\n" + "\tor clause 2\r\n" + "\t.\r\n"
			+ "\t.\r\n" + "\tor clause n\r\n"
			+ "where each clause i is a (possibly compound) statement. It is executed by\r\n"
			+ "nondeterministically choosing any clause i that is executable and executing\r\n"
			+ "it. The either statement can be executed iff at least one of those clauses can\r\n"
			+ "be executed. If any clause i contains a call, return, or goto statement or a\r\n"
			+ "label, then the either statement must be followed by a labeled statement.\r\n" + "The statement\r\n"
			+ "\tif (test) t clause else e clause\r\n" + "is equivalent to the following statement.\r\n"
			+ "\teither { await test ; t clause }\r\n" + "\tor { await ¬test ; e clause }";
	public static final String IFTHENELSE_HELP = "<If> ::= if ( <Expr> ) <Stmt> [else <Stmt>]{0,1}\n\n"
			+ "The if statement has its usual meaning. The statement\r\n" + "\tif ( test ) t clause else e clause\r\n"
			+ "is executed by evaluating the expression test and then executing the (pos-\r\n"
			+ "sibly compound) statement t clause or e clause depending on whether test\r\n"
			+ "equals true or false. The else clause is optional. An if statement must\r\n"
			+ "have a non-empty then clause. An if statement that contains a call,\r\n"
			+ "return, or goto statement or a label within it must be followed by a\r\n"
			+ "labeled statement. (A label on the if statement itself is not considered to be\r\n"
			+ "within the statement.)";
	public static final String VARIABLE_HELP = "<VarDecls> ::= [variable|variables] <VarDecl>+\r\n"
			+ "\t<VarDecl> ::= <Variable> [ [= |\\in] <Expr> ]{0,1} [;|,]\n\n";
	public static final String WHILE_HELP = "<While> ::= while ( <Expr> ) <Stmt>\n\n"
			+ "The while statement has its usual meaning. The statement\r\n" + "\tlb : while ( test ) body\r\n"
			+ "where body is a (possibly compound) statement, is executed like the following\r\n" + "if statement.\r\n"
			+ "\tlb : if ( test ) { body ; goto lb }\r\n"
			+ "A while statement must be labeled. However, the statement following a\r\n"
			+ "while statement need not be labeled, even if there is a label in body.";
	public static final String PROCESS_HELP = "<Process> ::= [ fair [+]{0,1} ]{0,1} process ( <Name> [=|\\in] <Expr> )\r\n"
			+ "\t<VarDecls>{0,1}\r\n" + "\t<CompoundStmt> [;]{0,1}\n\n"
			+ "A multiprocess algorithm contains one or more processes. A process begins\r\n"
			+ "in one of two ways:\r\n" + "\tprocess ( ProcName \\in IdSet )\r\n" + "\tprocess ( ProcName = Id )\r\n"
			+ "The first form begins a process set, the second an individual process. The\r\n"
			+ "identifier ProcName is the process or process set’s name. The elements of\r\n"
			+ "the set IdSet and the element Id are called process identifiers. The process\r\n"
			+ "identifiers of different processes in the same algorithm must all be different.\r\n"
			+ "This means that the semantics of TLA + must imply that they are different,\r\n"
			+ "which intuitively usually means that they must be of the same “type”. (For\r\n"
			+ "example, the semantics of TLA + does not specify whether or not a string\r\n"
			+ "may equal a number.) For execution by TLC, this means that all process\r\n"
			+ "identifiers must be comparable values, as defined in Specifying\r\n" + "Systems.\r\n"
			+ "The name ProcName has no significance; changing it does not change\r\n"
			+ "the meaning of the process statement in any way. The name appears\r\n"
			+ "in the TLA + translation, and it should be different for different process\r\n" + "statements\r\n"
			+ "As explained above in Section 2.6 on page 11, the process statement is\r\n"
			+ "optionally followed by declarations of local variables. The process body is a\r\n"
			+ "sequence of statements enclosed by braces ({ }). Its first statement must be\r\n"
			+ "labeled. Within the body of a process set, self equals the current process’s\r\n" + "identifier.\r\n"
			+ "A multiprocess algorithm is executed by repeatedly choosing an arbitrary\r\n"
			+ "process and executing one step of that process, if that step’s execution is\r\n"
			+ "possible. Execution of the process’s next step is impossible if the process has\r\n"
			+ "terminated, if its next step contains an await statement whose expression\r\n"
			+ "equals false, or if that step contains a statement of the form “await x ∈ S ”\r\n"
			+ "and S equals the empty set. Fairness conditions may be specified on the choice\r\n"
			+ "of which processes’ steps are to be executed.";
	public static final String CALL_HELP = "<Call> ::= call <MacroCall>\r\n"
			+ "\t<MacroCall> ::= <Name> ( [ <Expr>[, <Expr>]* ]{0,1} )\n\nSee procedure!";
	public static final String PROCEDURE_HELP = "<Procedure> ::= procedure <Name> ( [<PVarDecl> [, <PVarDecl>]* ]{0,1} )\r\n"
			+ "\t<PVarDecls>{0,1}\r\n" + "\t<CompoundStmt> [;]{0,1}\n\n"
			+ "An algorithm may have one or more procedures. If it does, the algorithm\r\n"
			+ "must be in a TLA + module that extends the Sequences module.\r\n"
			+ "The algorithm’s procedures follow its global variable declarations and\r\n"
			+ "define section (if any) and precede the “{” that begins the body of a\r\n"
			+ "uniprocess algorithm or the first process of a multiprocess algorithm. A\r\n"
			+ "procedure named PName begins\r\n" + "\tprocedure PName ( param 1 , . . . , param n )\r\n"
			+ "where the identifiers param i are the formal parameters of the procedure.\r\n"
			+ "These parameters are treated as variables and may be assigned to. As ex-\r\n"
			+ "plained in Section 4.5 on page 37, there may also be initial-value assignments\r\n"
			+ "of the parameters.\r\n" + "The procedure statement is optionally followed by declarations of vari-\r\n"
			+ "ables local to the procedure. These have the same form as the declara-\r\n"
			+ "tions of global variables, except that initializations may only have the form\r\n"
			+ "“variable = expression”. The procedure’s local variables are initialized on\r\n"
			+ "each entry to the procedure.\r\n"
			+ "Any variable declarations are followed by the procedure’s body, which\r\n"
			+ "is a sequence of statements enclosed by braces ({ }). The body must begin\r\n"
			+ "with a labeled statement. There is an implicit label Error immediately\r\n"
			+ "after the body. If control ever reaches that point, then execution of either\r\n"
			+ "the process (multiprocess algorithm) or the complete algorithm (uniprocess\r\n" + "algorithm) halts.\r\n"
			+ "A procedure PName can be called by the statement\r\n" + "\tcall PName ( expr 1 , . . . , expr n )\r\n"
			+ "Executing this call assigns the current values of the expressions expr i to the\r\n"
			+ "corresponding parameters param i , initializes the procedure’s local variables,\r\n"
			+ "and puts control at the beginning of the procedure body.\r\n"
			+ "A return statement assigns to the parameters and local procedure vari-\r\n"
			+ "ables their previous values—that is, the values they had before the procedure\r\n"
			+ "was last called—and returns control to the point immediately following the\r\n" + "call statement.\r\n"
			+ "The call and return statements are considered to be assignments to the\r\n"
			+ "procedure’s parameters and local variables. In particular, they are included\r\n"
			+ "in the rule that a variable can be assigned a value by at most one assignment\r\n"
			+ "statement in a step. For example, if x is a local variable of procedure P ,\r\n"
			+ "then a step within the body of P that (recursively) calls P cannot also assign\r\n" + "a value to x.\r\n"
			+ "For a multiprocess algorithm, the identifier self in the body of a proce-\r\n"
			+ "dure equals the process identifier of the process within which the procedure\r\n" + "is executing.\r\n"
			+ "The return statement has no argument. A PlusCal procedure does not\r\n"
			+ "explicitly return a value. A value can be returned by having the procedure\r\n"
			+ "set a global variable and having the code immediately following the call\r\n"
			+ "read that variable. For example, in a multiprocess algorithm, procedure P\r\n"
			+ "might use a global variable rVal to return a value by executing\r\n" + "\trVal[self] := ... ;\r\n"
			+ "\treturn ;\r\n" + "From within a process in a process set, the code that calls P might look like\r\n"
			+ "this:\r\n" + "call P(17) ;\r\n" + "lab: x := ... rVal[self] ... ;\r\n"
			+ "For a call from within a single process, the code would contain the process’s\r\n"
			+ "identifier instead of self.\r\n"
			+ "In any control path, a return statement must be immediately followed\r\n"
			+ "by a label. A call statement must either be followed in the control path by\r\n"
			+ "a label or else it must appear immediately before a return statement in a\r\n"
			+ "statement sequence.\r\n" + "When a call P statement is followed immediately by a return, the\r\n"
			+ "return from procedure P and the return performed by the return statement\r\n"
			+ "are both executed as part of a single execution step. When these statements\r\n"
			+ "are in the (recursive) procedure P , this combining of the two returns is\r\n"
			+ "essentially the standard optimization of replacing tail recursion by a loop.";
}
