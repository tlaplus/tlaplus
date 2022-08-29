package pcal;

import pcal.AST.SingleAssign;
import pcal.AST.VarDecl;
import pcal.MappingObject.LeftParen;
import pcal.MappingObject.RightParen;
import pcal.exception.PcalTLAGenException;
import pcal.exception.TLAExprException;
import util.TLAConstants;

import java.util.ArrayList;
import java.util.List;

/****************************************************************************
 * Given an exploded and disambiguated AST, generate the equivalent TLA+.
 * <br>
 * {@link PcalTLAGen#generate(AST, PcalSymTab)} returns a vector of Strings, one entry per line of generated TLA+.
 *
 * @version $Id$
 * @author Leslie Lamport (modified on Thu  6 March 2008 at 10:16:22 PST)
 *                        (minor change on 9 December 2009)            
 * @author keith (modified on Mon  3 Oct 2005 at 21:43:09 UT)                  
 *
 ****************************************************************************/

// Relies heavily on untyped generics. Ignored after typing what could be typed.
@SuppressWarnings({"rawtypes", "unchecked"})
public class PcalTLAGen {
    // Constants that control formatting
    public static final boolean boxUnderCASE = true; /* else [] at end of line  */


    // I think that this is used as follows:
    //    when translating an assignment statement (or multiassignment?)
    //    to  var' = [var EXCEPT ...],  it begins the ... on a new line
    //    iff  the ... would begin in a column > pcalParams.ssWrapColumn.
    // For the time being, it is set to wrapColumn - 33.  We may want
    // to do something cleverer or else make it a user option.

    // Private class variables
    /**
     * The tlacode field accumulates the translation as it is constructed.  It
     * should be a vector of separate lines.  Keiths original implementation put
     * multiple lines in a single element of tlacode in:
     * <p>
     * GenVarsAndDefs
     * GenVarDecl
     */
    private final ArrayList<String> tlacode = new ArrayList<>(); /* of lines */
    private final ArrayList<String> vars = new ArrayList<>(); /* list of all disambiguated vars */
    private final ArrayList<String> pcV = new ArrayList<>(); /* sublist of vars of variables representing
                                          procedure parameters and procedure variables */
    private final ArrayList<String> psV = new ArrayList<>(); /* sublist of vars local to a process set */
    private final ArrayList<String> nextStep = new ArrayList<>(); /* unparam actions */ // For multiprocess alg, these are the individual (=) processes
    private final ArrayList<String> nextStepSelf = new ArrayList<>(); /* param actions */ // These are process sets (\in processes) and procedures
    private final ParseAlgorithm parseAlgorithm;
    private final PcalParams pcalParams;
    /**
     * The tlacodeNextLine field accumulates characters for the next
     * line of tlacode.  It is always a string.  It is assumed that
     * when it equals "", then a new line can be started without
     * adding the current string in tlacodeNextLine as a new line.
     */
    private String tlacodeNextLine = "";
    /**
     * mappingVector is a local pointer to {@link TLAtoPCalMapping#mappingVector},
     * which is used to accumulate the TLA+ to PlusCal mapping.  It approximately
     * reflects the TLA+ that has been inserted in the {@link PcalTLAGen#tlacode}
     * vector.  It is set in the {@link TLAtoPCalMapping#generate} method.
     */

    private ArrayList mappingVector;
    /**
     * mappingVectorNextLine contains the sequence of MappingObject objects
     * that correspond to the strings added to tlacodeNextLine.
     */
    private ArrayList<MappingObject> mappingVectorNextLine = new ArrayList<>();
    /**
     * The self field is set to "self" by GenProcess when called for a single process
     * (rather than a process set) and by GenProcedure for a multiprocess algorithm.
     * It is set to the process id by GenProcess when called for a single process.
     * selfIsSelf is set to true when self is set to "self", and to false when self is
     * set to a process id.  The self field never seems to be reset to null.
     */
    private TLAExpr self = null; // changed by LL on 22 jan 2011 from: private String self = null; /* for current process */
    private boolean selfIsSelf = false;
    private PcalSymTab st = null; /* symbol table */
    private boolean mp = false; /* true if multiprocess, else unip */
    // Following added to keep track of the length of the "lbl... == /\ "
    // that precedes all the statements in the definition of a label's action
    // because Keith screwed up and handled the assignment to the pc different
    // from that of all other variables, forgetting that the subscript exp
    // in pc[exp] := ... can be multi-line.
    private int kludgeToFixPCHandlingBug;
    /**
     * The public method: generate TLA+ as a vector of strings.
     */

    /*
     * The  string currentProcName is the name of the current process (for a multiprocess algorithm)
     * or "Next" for a uniprocess algorithm.  When ParseAlgorithm.omitPC is true, this is used
     * instead of the label when generating the process's or the entire algorithm's next-state
     * action.  Thus, with a single label lbl, this generates
     *    Next == Xlation
     * instead of
     *    lbl == Xlation
     *    Next == lbl
     */
    private String currentProcName;

    public PcalTLAGen(ParseAlgorithm parseAlgorithm) {
        this.parseAlgorithm = parseAlgorithm;
        this.pcalParams = parseAlgorithm.pcalParams;
    }

    /****************************************************************/
    private static boolean InVector(final String var, final ArrayList<String> v) {
        for (String s : v)
            if (var.equals(s))
                return true;
        return false;
    }

    /****************************************************************/
    /* Returns whether the string is present in a vector of string. */

    /**********************************************/
    private static String NSpaces(final int n) {
        final StringBuilder sb = new StringBuilder();
        AddSpaces(sb, n);
        return sb.toString();
    }

    /******************************************************/
    /* True if var is in the list of procedure variables. */

    /*********************************************/
    private static void AddSpaces(final StringBuilder sb, final int num) {
        sb.append(" ".repeat(Math.max(0, num)));
    }

    /****************************************************/
    /* True if var is in the list of process variables. */

    /****************************************/
    private static boolean EmptyExpr(final TLAExpr expr) {
        if (expr == null)
            return true;
        return expr.tokens == null || expr.tokens.size() == 0;
    }

    /**********************************************/
    /* Returns a string of length n of all spaces */

    /***********************************************************************
     * Given an expression, makes it into a subscript expr.  It is called   *
     * only with argument Self(context), which means that it is called      *
     * only for a single subscript.                                         *
     *                                                                      *
     * If string is null, then returns null.                                *
     *                                                                      *
     * Since this is used only to add "[self]", there is no need to add     *
     * any REPLACEMENT tokens to the expression.  Moreover, the added       *
     * subscript's tokens have a null source field because they don't come  *
     * from any PCal code.  The new expression is given the same origin as  *
     * the original one.                                                    *
     ***********************************************************************/
    private static TLAExpr SubExpr(final TLAExpr sub) {
        if (sub != null) {
            final TLAExpr expr = sub.cloneAndNormalize();
            // This preserves the origin of the expression
            for (int i = 0; i < expr.tokens.size(); i++) {
                final ArrayList<TLAToken> tokenVec = expr.tokens.get(i);
                for (final TLAToken tok : tokenVec) {
                    tok.column = tok.column + 1;
                }
                if (i == 0) {
                    /*
                     * Set isAppended field of the "[" and "]" to true iff the first
                     * token of sub has isAppended field true, which should be the
                     * case iff it is the "self" token.
                     */
                    tokenVec.add(0,
                            new TLAToken("[", 0, TLAToken.BUILTIN, sub.firstToken().isAppended())
                    );
                }
            }
            expr.addTokenOffset(
                    new TLAToken("]", 0, TLAToken.BUILTIN, sub.firstToken().isAppended()), 0);
            return expr;
        } else {
            return null;
        }
    }

    /*********************************************/
    /* Appends n spaces to the string buffer sb. */

    private static TLAExpr selfAsExpr() {
        /*
         * This is a token that does not correspond to anything in the
         * PCal code, so it should have a null source field.
         * It has a true isAppended field because it is always appended
         * as a subscript to a variable.
         */
        final TLAToken selfToken = new TLAToken("self", 0, TLAToken.IDENT, true);
        final ArrayList<TLAToken> tokenVec = new ArrayList<>();
        tokenVec.add(selfToken);
        final ArrayList<ArrayList<TLAToken>> tokens = new ArrayList<>();
        tokens.add(tokenVec);
        final TLAExpr expr = new TLAExpr(tokens);
        expr.normalize();
        return expr;
    }

    /****************************************/
    /* True if expr is an empty expression. */

    /***********************************************************/
    private static ArrayList<SingleAssign> SortSass(final ArrayList<AST.SingleAssign> vec) {
        final ArrayList<AST.SingleAssign> v = (ArrayList<SingleAssign>) vec.clone();
        final ArrayList<SingleAssign> r = new ArrayList<>(); // The sorted version of v.
        while (v.size() > 0) { // Good old n^2 insertion sort.
            AST.SingleAssign candidate = v.get(0);
            int indexC = 0;
            for (int i = 1; i < v.size(); i++) {
                final AST.SingleAssign sass = v.get(i);
                if (candidate.lhs.var.compareTo(sass.lhs.var) > 0) {
                    indexC = i;
                    candidate = sass;
                }
            }
            r.add(candidate);
            v.remove(indexC);
        }
        return r;
    }

    /*****************************************************************/
    /* Top level routines. Context is "", "procedure", or "process". */

    /**
     * As part of adding the TLA to PCal translation code, LL removedseparated
     * the code that decides if parentheses are needed from the Parenthesize
     * method and put it into this method.  The Parenthesize method itself
     * will not be needed.
     */
    public static boolean NeedsParentheses(final ArrayList<String> vec) {
        if (vec.size() == 0) {
            return false;
        }
        /*******************************************************************
         * vec shouldn't be empty, but let's not worry about what to do if  *
         * it is.                                                           *
         *******************************************************************/
        int curCharNum = 0;
        int curLineNum = 0;
        int parenDepth = 0;
        boolean inString = false;
        boolean needParen = false;
        while ((curLineNum < vec.size()) && (!needParen)) {
            final String curLine = vec.get(0);
            while ((curCharNum < curLine.length()) && (!needParen)) {
                final char curChar = curLine.charAt(curCharNum);

                if (inString) {
                    switch (curChar) {
                        case '\"' -> inString = false;
                        case '\\' -> curCharNum++;
                    }
                    // end switch
                } // end if (inString)
                else {
                    boolean leftParen = false;
                    boolean rightParen = false;
                    boolean mayNeedParen = false;
                    /***************************************************************
                     * Set nextChar to the next character on the line, or ' ' if    *
                     * there is none.                                               *
                     ***************************************************************/
                    char nextChar = ' ';
                    if (curCharNum < curLine.length() - 1) {
                        nextChar = curLine.charAt(curCharNum + 1);
                    }
                    switch (curChar) {
                        case '\"':
                            inString = true;
                            break;
                        case '=':
                        case '#':
                            mayNeedParen = true;
                            break;
                        case '<':
                            if (nextChar == '<') {
                                curCharNum++;
                                leftParen = true;
                            } else {
                                mayNeedParen = true;
                            }
                            break;
                        case '>':
                            if (nextChar == '>') {
                                curCharNum++;
                                rightParen = true;
                            } else {
                                mayNeedParen = true;
                            }
                            break;
                        case '|':
                            if ((nextChar == '-') || ((curCharNum > 0) && (curLine.charAt(curCharNum - 1) == '-'))) {
                                mayNeedParen = true;
                            }
                            break;
                        case '\\':
                            if (!((nextChar == ' ') || (nextChar == 'o') || (nextChar == 'X'))) {
                                mayNeedParen = true;
                            }
                            break;
                        case '/':
                            if (nextChar == '\\') {
                                mayNeedParen = true;
                            }
                            break;
                        case '(':
                        case '[':
                        case '{':
                            leftParen = true;
                            break;
                        case ')':
                        case ']':
                        case '}':
                            rightParen = true;
                            break;
                    }
                    if (mayNeedParen && (parenDepth == 0)) {
                        needParen = true;
                    }
                    if (leftParen) {
                        parenDepth++;
                    }
                    if (rightParen) {
                        if (parenDepth == 0) {
                            needParen = true;
                        }
                        parenDepth--;
                    }
                }
                // end else ! inString
                curCharNum++;
            }
            // end while (curCharNum < curLine.length())

            if (inString) {
                needParen = true;
            }
            /*****************************************************************
             * If there is an unmatched quote, we might as well stop here.    *
             *****************************************************************/
            curLineNum++;
            curCharNum = 0;
        } // end while (curLineNum < vec.size())

        return needParen;
    }

    /**
     * Generates the translation.
     *
     * @param ast    The AST produced by parsing and exploding.
     * @param symtab The symbol table.
     * @param report A vector of strings, containing the reports of renaming.
     * @return A vector of strings.
     */
    public ArrayList<String> generate(final AST ast, final PcalSymTab symtab, final ArrayList<String> report) throws PcalTLAGenException {
        final TLAtoPCalMapping map = pcalParams.tlaPcalMapping;
        mappingVector = new ArrayList<String>(50);
        /*
         * Add the reports of renaming to the output.
         */
        for (String s : report) {
            addOneLineOfTLA(s);
        }

        st = symtab;
        GenSym(ast, "");

        /*
         * We put at the beginning and end of mappingVector a LeftParen
         * and RightParen with location (0, 0), so that location will
         * be found by the TLA+ to PCal translation algorithm if the
         * user selects the entire algorithm, in which case it will
         * return the null region to GotoPCalSourceHandler.execute.
         */
        final PCalLocation ZeroLocation = new PCalLocation(0, 0);
        ((ArrayList<LeftParen>) mappingVector.get(0)).
                add(0, new MappingObject.LeftParen(ZeroLocation));
        final ArrayList<RightParen> lastLine = (ArrayList<RightParen>) mappingVector.get(mappingVector.size() - 1);
        lastLine.add(lastLine.size(), new MappingObject.RightParen(ZeroLocation));

        /*
         * For testing, throw a null pointer exception if the parentheses are not
         * properly matching in mappingVector.
         */
        //int[] depths = new int[10000];

        int parenDepth = 0;
        for (Object value : mappingVector) {
            final ArrayList line = (ArrayList) value;
            for (Object o : line) {
                final MappingObject obj = (MappingObject) o;
                if (obj.getType() == MappingObject.LEFT_PAREN) {
                    parenDepth++;
                } else if (obj.getType() == MappingObject.RIGHT_PAREN) {
                    parenDepth--;
                    if (parenDepth < 0) {
                        throw new NullPointerException("paren depth < 0");
                    }
                }
            }
            // depths[i] = parenDepth;
        }
        if (parenDepth != 0) {
            throw new NullPointerException("Unmatched Left Paren");
        }
        /*   ------------------ end testing --------------------------*/
        final ArrayList nonredundantMappingVector =
                TLAtoPCalMapping.RemoveRedundantParens(mappingVector);
        map.makeMapping(nonredundantMappingVector);

//System.out.println("Original mappingvector:");
//MappingObject.printMappingVector(mappingVector);
//System.out.println("RemoveRedundantParens(mappingVector)");
//MappingObject.printMappingVector(TLAtoPCalMapping.RemoveRedundantParens(mappingVector));
//System.out.println("Should be original mappingvector:");
//MappingObject.printMappingVector(mappingVector);
// Debugging

        return tlacode;
    }

    /******************************************************/
    private boolean IsProcedureVar(final String var) {
        return InVector(var, pcV);
    }

    /****************************************************/
    private boolean IsProcessSetVar(final String var) {
        return InVector(var, psV);
    }

    /**
     *
     ****************************************************************/
    private void GenSym(final AST ast, final String context) throws PcalTLAGenException {
        if (ast instanceof AST.Uniprocess obj)
            GenUniprocess(obj, context);
        else if (ast instanceof AST.Multiprocess obj)
            GenMultiprocess(obj, context);
        else if (ast instanceof AST.Procedure obj)
            GenProcedure(obj, context);
        else if (ast instanceof AST.Process obj)
            GenProcess(obj, context);
        else if (ast instanceof AST.LabeledStmt obj)
            GenLabeledStmt(obj, context);
    }

    /*****************************************************/
    /* Generates an action with name equal to the label. */

    private void GenUniprocess(final AST.Uniprocess ast, final String context) throws PcalTLAGenException {
        mp = false;
        currentProcName = "Next";
        GenVarsAndDefs(ast.decls, ast.prcds, null, ast.defs);
        GenInit(ast.decls, ast.prcds, null);
        for (int i = 0; i < ast.prcds.size(); i++)
            GenProcedure(ast.prcds.get(i), "");
        for (int i = 0; i < ast.body.size(); i++) {
            final AST.LabeledStmt ls = (AST.LabeledStmt) ast.body.get(i);
            /* Add this step to the disjunct of steps */
            nextStep.add(ls.label);
            GenLabeledStmt(ls, "");
        }
        GenNext();
        GenSpec();
        GenTermination();
    }

    private void GenMultiprocess(final AST.Multiprocess ast, final String context) throws PcalTLAGenException {
        mp = true;
        GenVarsAndDefs(ast.decls, ast.prcds, ast.procs, ast.defs);
        GenProcSet();
        GenInit(ast.decls, ast.prcds, ast.procs);
        for (int i = 0; i < ast.prcds.size(); i++)
            GenProcedure(ast.prcds.get(i), "");
        for (int i = 0; i < ast.procs.size(); i++)
            GenProcess(ast.procs.get(i), "");
        GenNext();
        GenSpec();
        GenTermination();
    }

    /***************************************************************************
     * LL Comment added 27 Jan 2006:                                            *
     *                                                                          *
     * There is a basic flaw in the way GenStmt works.  It now generates the    *
     * output on the fly.  This means that                                      *
     *                                                                          *
     * - There is no way to avoid the prefix /\ on a one-element conjunct       *
     *   because GenStmt has no way of knowing if there's another conjunct      *
     *   coming.                                                                *
     *                                                                          *
     * - The handling of the UNCHANGEDs of the THEN and ELSE clauses of         *
     *   an IF is a kludge, because the UNCHANGED of the THEN clause is         *
     *   output before it can be known.                                         *
     *                                                                          *
     * The correct way of doing things is to define GenStmt so it returns a     *
     * sequence (vector) of string vectors, each string vector being a          *
     * conjunction expression (without a leading /\ or any leading spaces) and  *
     * the new Changed object (which it can do as it now does by modifying its  *
     * Changed object argument).  It would also be useful to define a           *
     * GenStmtSeq that simply calls GenStmt iteratively on a sequence of        *
     * simple statements.  The method that calls GenStmtSeq would then add the  *
     * Unchanged conjunct and call a method that returns a sequence of          *
     * conjuncts and a prefix into a string vector containing the prefix and    *
     * the necessary /\s.                                                       *
     ***************************************************************************/

    /*****************************************************************/
    /* General entry for generating the TLA+ for a simple statement. */
    /* Prefix is the prefix of the first line. Col is where to start */
    /* subsequent lines (I think we could replace it with the length */
    /* of prefix).                                                   */
    /*                                                               */
    /* And what on earth are `c' and `context'? LL                   */

    private void GenProcedure(final AST.Procedure ast, final String context) throws PcalTLAGenException {
        /*
         * First, generate the body's actions.  Must set self and selfIsSelf (?) for
         * use by GenLabeledStmt.
         */
        if (mp) {

            self = selfAsExpr(); // subscript for variables is "self"
            selfIsSelf = true;
//            /* Add this step to the disjunct of steps with (self) */
            nextStepSelf.add(ast.name + "(self)");
        } else {
            /* Add this step to the disjunct of steps */
            nextStep.add(ast.name);
        }
        for (int i = 0; i < ast.body.size(); i++) {
            final AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.get(i);
            GenLabeledStmt(stmt, "procedure");
        }

        /*
         * Next add the definition of the procedure--e.g.,
         *
         *    procedureName(self) == label_1(self) \/ ... \/ label_k(self)
         *
         * We put Left/RightParens for the entire procedure around the entire
         * definition, and Left/RightParens around each disjunction for
         * the labeled statement.
         */
        addLeftParen(ast.getOrigin());
        final String argument = (mp) ? "(self)" : "";
        final StringBuilder buf = new StringBuilder(ast.name + argument + " == ");
        addOneTokenToTLA(buf.toString());
        final String indentSpaces = NSpaces(buf.length() + 2);
        for (int i = 0; i < ast.body.size(); i++) {
            final AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.get(i);
            final String disjunct = stmt.label + argument;
            if (i != 0
                    && tlacodeNextLine.length() + 7 /* the 7 was obtained empirically */
                    + disjunct.length() > pcalParams.wrapColumn) {
                endCurrentLineOfTLA();
            }
            if (i != 0) {
                addOneTokenToTLA(((tlacodeNextLine.length() == 0) ? indentSpaces : "") + " \\/ ");
            }
            addLeftParen(stmt.getOrigin());
            addOneTokenToTLA(disjunct);
            addRightParen(stmt.getOrigin());
        }
        addRightParen(ast.getOrigin());
        addOneLineOfTLA("");

// The previous version was very convoluted just to avoid having to go through the
// list of labeled statements twice.  It seemed easier to just reimplement from
    }

    /*****************************************************************/
    /* Generates a sequence of single assigns. Since all of them are */
    /* executed "at the same time", we accumulate the changes in a   */
    /* separate Changed cThis, and use c to determine which vars in  */
    /* the right hand side are primed.                               */
    /**
     * ***************************************************************/

    private void GenProcess(final AST.Process ast, final String context) throws PcalTLAGenException {
        currentProcName = ast.name;

        /*
         * Generate the body's actions.   Must set self and selfIsSelf (?) for
         * use by GenLabeledStmt.
         */
        boolean isSet = true;
        /************************************************************/
        /* Decide if it is a process set or not. If so, set self to */
        /* the string "self"; otherwise set self to the process id. */
        /************************************************************/
        if (ast.isEq) {
            self = ast.id;
            selfIsSelf = false;
            isSet = false;
        } else {
            self = selfAsExpr();
            selfIsSelf = true;
        }

        if (isSet) {
            nextStepSelf.add(ast.name + "(self)");
        } else
            nextStep.add(ast.name);

        for (int i = 0; i < ast.body.size(); i++) {
            final AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.get(i);
            GenLabeledStmt(stmt, "process");
        }

        /*
         * Next add the definition of the process--e.g.,
         *
         *    processName(self) == label_1(self) \/ ... \/ label_k(self)
         *
         * We put Left/RightParens for the entire procedure around the entire
         * definition, and Left/RightParens around each disjunction for
         * the labeled statement.
         *
         * However, we don't add this definition if we are omitting the pc,
         * because we have already defined the process name to equal the
         * only label action.
         */

        if (!parseAlgorithm.omitPC) {
            addLeftParen(ast.getOrigin());
            final String argument = (isSet) ? "(self)" : "";
            final StringBuilder buf = new StringBuilder(ast.name + argument + " == ");
            addOneTokenToTLA(buf.toString());
            final String indentSpaces = NSpaces(buf.length() + 2);
            for (int i = 0; i < ast.body.size(); i++) {
                final AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.get(i);
                final String disjunct = stmt.label + argument;
                if (i != 0
                        && tlacodeNextLine.length() + 7 /* the 7 was obtained empirically */
                        + disjunct.length() > pcalParams.wrapColumn) {
                    endCurrentLineOfTLA();
                }
                if (i != 0) {
                    addOneTokenToTLA(((tlacodeNextLine.length() == 0) ? indentSpaces : "") + " \\/ ");
                }
                addLeftParen(stmt.getOrigin());
                addOneTokenToTLA(disjunct);
                addRightParen(stmt.getOrigin());
            }
            addRightParen(ast.getOrigin());
            addOneLineOfTLA("");
        }


// As with GenProcedure, the original implementation was quite convoluted, so
// it was rewritten.  The code above was copied with modifications from
// the rewritten GenProcedure code.
    }

    /**
     *
     ****************************************************/
    private void GenLabeledStmt(final AST.LabeledStmt ast, final String context) throws PcalTLAGenException {
        // Set actionName to the name of the action being defined.
        // This is the label, except when we are omitting the PC,
        // in which case it is "Next" for a uniprocess algorithm
        // and the process name for a multiprocess algorithm.
        String actionName = ast.label;
        if (parseAlgorithm.omitPC) {
            actionName = currentProcName;
        }
        StringBuilder sb = new StringBuilder(actionName);
        /* c is used to determine which vars are in UNCHANGED. */
        final Changed c = new Changed(vars);
        if (mp && (context.equals("procedure") || selfIsSelf)) { // self.equals("self")))
            sb.append("(self)");
        }
        sb.append(" == ");
        final int col = sb.length();
        kludgeToFixPCHandlingBug = col;
        // There's a problem here.  If ast.stmts.size() = 1, then we don't preface
        // the statement's translation with "/\".  However, that means that if we
        // then add an UNCHANGED conjunct, we wind up with
        //   A
        //    /\ UNCHANGED ...
        // where A is the statement's translation.  This looks bad and could wind up
        // putting the UNCHANGED inside prefix operator--e.g.,
        //   x' = CHOOSE t : ...
        //     /\ UNCHANGED ...
        // This is seems to be a problem only when omitPC = true, since otherwise the
        // testing and setting of pc ensures that there is more than one element in ast.stmts.
        // What we do is always add the "/\ ", but remove it afterwards if there's only
        // a single statement in ast.stmts and there is no UNCHANGED clause.
        // The code for doing this is based on the observation that the contents of
        // StringBuilder sb begin the next line added to tlacode.
        //
        /* if (ast.stmts.size() > 1) {  */
        sb.append("/\\ ");
        kludgeToFixPCHandlingBug = kludgeToFixPCHandlingBug + 3;
        /* } */

        // We set defStartLine to the index of the next line added to tlacode and
        // colAfterAnd to the column position in that line immediately following
        // the added "/\ ".  This gives us the information needed to remove the
        // "/\ " later from tlacode.
        final int defStartLine = tlacode.size();
        final int colAfterAnd = sb.length();

        /*
         * Note: it would make sense for this method to insert sb into the tlacode
         * output, but it seems safer to maintain the current structure in which
         * each GenX for each statement type X does that.
         */

        /*
         * We set macroBeginLeft to the macroOriginBegin field of the first statement
         * in ast.stmts with a non-null origin, and macroEndRight to the macroOriginEnd
         * field of the last statement in ast.stmts with a non-null origin.
         */
        PCalLocation macroBeginLeft = null;
        PCalLocation macroEndRight = null;
        boolean nonNullNotFound = true;
        for (int i = 0; i < ast.stmts.size(); i++) {
            final AST stmt = ast.stmts.get(i);
            if (stmt.getOrigin() != null) {
                if (nonNullNotFound) {
                    nonNullNotFound = false;
                    macroBeginLeft = stmt.macroOriginBegin;
                }
                macroEndRight = stmt.macroOriginEnd;
            }
        }

        /*
         * addLeftParenV used instead of addLeftParen because if the first statement
         * that came from PlusCal code arose from a macro call, then we want the
         * location of the macro call rather than that of the macro's code.
         */
        addLeftParenV(ast, macroBeginLeft);
        for (int i = 0; i < ast.stmts.size(); i++) {
            GenStmt(ast.stmts.get(i), c, context, sb.toString(), sb.length());
            sb = new StringBuilder(NSpaces(col));
            sb.append("/\\ ");
        }

        /*
         * Since the UNCHANGED conjunct just consists of TLATokens, with no
         * SourceTokens, we can just use the old code, simply replacing each
         * tlacode.add call with a call of addOneLineOfTLA--except that
         * the last one is replaced with a call of addOneTokenToTLA so we can
         * put the RightParen object in mappingVector.
         */
        final List<String> unc = c.Unchanged(pcalParams.wrapColumn - col - "/\\ UNCHANGED << ".length());
        if (c.NumUnchanged() > 1) {
            sb = new StringBuilder(NSpaces(col));
            sb.append("/\\ UNCHANGED << ");
            final int here = sb.length();
            sb.append(unc.get(0));
            for (int i = 1; i < unc.size(); i++) {
//                tlacode.add(sb.toString());
                addOneLineOfTLA(sb.toString());
                sb = new StringBuilder(NSpaces(here));
                sb.append(unc.get(i));
            }
            sb.append(" >>");
//            tlacode.add(sb.toString());
            addOneTokenToTLA(sb.toString());
        } else if (c.NumUnchanged() == 1) {
            // Change made by LL on 16 Mar 2011 so that, if there is a single
            // unchanged variable v, it produces v' = v if v is a short variable,
            // otherwise it produces UNCHANGED v
            if (c.Unchanged().length() > 5) {
//              tlacode.add(NSpaces(col) + "/\\ UNCHANGED " + c.Unchanged());
                addOneTokenToTLA(NSpaces(col) + "/\\ UNCHANGED " + c.Unchanged());
            } else {
                addOneTokenToTLA(NSpaces(col) + "/\\ " + c.Unchanged() + "' = "
                        + c.Unchanged());
            }
        } else {
            // No unchanged.  If there was only one conjunction, remove it.
            // To do that, we must remove the "/\ " and then remove three spaces
            // from all other lines that were added.  We must also modify the
            // TLAToken objects appropriately in the corresponding lines of
            // mappingVector
            if (ast.stmts.size() == 1) {
                for (int i = defStartLine; i < tlacode.size(); i++) {
                    final String line = tlacode.get(i);
                    if (i == defStartLine) {
                        // remove the "/\ " added
                        tlacode.set(i, line.substring(0, colAfterAnd - 3) +
                                line.substring(colAfterAnd));
                        shiftMappingVectorTokensLeft(i, colAfterAnd, 3);

                    } else {
                        // Remove three blanks from any following lines.  We test the length
                        // of the line just in case one or more short (hopefully blank) lines
                        // have been added.
                        if (line.length() > 3) {
                            tlacode.set(i, line.substring(3));
                            shiftMappingVectorTokensLeft(i, colAfterAnd, 3);
                        }
                    }
                }
            }
        }
        /*
         * We call addRightParenV rather than addRightParen because it the last statement
         * that came from the PCal code arose from the expansion of a macro call, then we
         * want the RightParen's location to be the end of the call, not the end of the
         * macro's code.
         */
        addRightParenV(ast, macroEndRight);
        addOneLineOfTLA("");
//        tlacode.add("");
    }

    /**
     * Adjusts the objects in line lineNum of mappingVector so all column
     * numbers starting with startCol are decreased by `shift'.  If any Begin/EndTLAToken
     * pairs are changed to have a non-positive width, a bug is reported.
     * <p>
     * Note: It is assumed that there is no aliasing of MappingTokens in mappingVector.
     * That is, other than in transient local variables, the only pointer to a
     * MappingToken in mappingVector is the single one in its line of mappingVector.
     * I can't see how any aliasing of MappingTokens could arise.
     * <p>
     * This method is called only by GenLabeledStmts.
     */
    private void shiftMappingVectorTokensLeft(final int lineNum, final int startCol, final int shift) {
        boolean lastWasBeginTLAToken = false;
        int lastBeginTLATokCol = -777; // to keep the compiler happy.
        final ArrayList line = (ArrayList) mappingVector.get(lineNum);
        for (Object o : line) {
            final MappingObject obj = (MappingObject) o;
            if (obj.getType() == MappingObject.BEGIN_TLATOKEN) {
                final MappingObject.BeginTLAToken tobj = (MappingObject.BeginTLAToken) obj;
                final int col = tobj.getColumn();
                if (col >= startCol) {
                    tobj.setColumn(col - shift);
                }
                lastWasBeginTLAToken = true;
                lastBeginTLATokCol = tobj.getColumn();
            } else {
                if (obj.getType() == MappingObject.END_TLATOKEN) {
                    final MappingObject.EndTLAToken tobj = (MappingObject.EndTLAToken) obj;
                    final int col = tobj.getColumn();
                    if (col >= startCol) {
                        tobj.setColumn(col - shift);
                    }
                    if (lastWasBeginTLAToken && tobj.getColumn() <= lastBeginTLATokCol) {
                        PcalDebug.ReportBug(
                                "PcalTLAGen.shiftMappingVectorTokensLeft created a null TLA Token");
                    }
                } else if (obj.getType() == MappingObject.SOURCE_TOKEN) {
                    final MappingObject.SourceToken tobj = (MappingObject.SourceToken) obj;
                    int col = tobj.getBeginColumn();
                    if (col >= startCol) {
                        tobj.setBeginColumn(col - shift);
                    }
                    col = tobj.getEndColumn();
                    if (col >= startCol) {
                        tobj.setEndColumn(col - shift);
                    }

                    lastWasBeginTLAToken = false;
                }
            }
        }


    }

    /**
     *
     ****************************************************************/
    private void GenStmt(final AST ast, final Changed c, final String context, final String prefix, final int col) throws PcalTLAGenException {
        if (ast instanceof AST.Assign obj)
            GenAssign(obj, c, context, prefix, col);
        else if (ast instanceof AST.If obj)
            GenIf(obj, c, context, prefix, col);
            // Either case added by LL on 27 Jan 2006
        else if (ast instanceof AST.Either obj)
            GenEither(obj, c, context, prefix, col);
        else if (ast instanceof AST.With obj)
            GenWith(obj, c, context, prefix, col);
        else if (ast instanceof AST.When obj)
            GenWhen(obj, c, context, prefix, col);
        else if (ast instanceof AST.PrintS obj)
            GenPrintS(obj, c, context, prefix, col);
        else if (ast instanceof AST.Assert obj)
            GenAssert(obj, c, context, prefix, col);
        else if (ast instanceof AST.Skip obj)
            GenSkip(obj, c, context, prefix, col);
        else
            PcalDebug.ReportBug("Unexpected AST type " + ast);
    }

    /**
     *
     */
    private void GenAssign(final AST.Assign ast, final Changed c, final String context, final String prefix, final int col)
            throws PcalTLAGenException {
        final Changed cThis = new Changed(c);
        StringBuilder sb = new StringBuilder();
//        ArrayList vlines = new ArrayList();
        /*
         * Sort the vector ast.ass so that assignments to the same variable
         * follow one another.
         */
        ast.ass = SortSass(ast.ass);

        addOneTokenToTLA(prefix);
        addLeftParen(ast.getOrigin());

        int i = 0;
        int numAssigns = 0;
        /*
         * hasMultipleVars set true iff the assignment assigns values to
         * more than one variable, and hence the statement's translation
         * has multiple conjuncts.
         */
        boolean hasMultipleVars = false;
        while (i < ast.ass.size()) {
            final AST.SingleAssign sF = ast.ass.get(i);

            /*
             * Added by LL and MK on 16 May 2018:
             * Report an error if the variable being assigned is not a
             * variable declared in the algorithm (either not declared
             * at all or is a constant, bound identifier, ...).
             */
            if (!this.vars.contains(sF.lhs.var)) {
                throw new PcalTLAGenException("Assignment to undeclared variable " + sF.lhs.var, sF);
            }

            int iFirst = i;
            int iLast = i;
            boolean hasAssignmentWithNoSubscript = false;
            boolean lastAssignmentHasNoSubscript = EmptyExpr(sF.lhs.sub);
            AST.SingleAssign sL = ast.ass.get(i);
            while (iLast < ast.ass.size() && sF.lhs.var.equals(sL.lhs.var)) {
                if (lastAssignmentHasNoSubscript) {
                    hasAssignmentWithNoSubscript = true;
                }
                iLast = iLast + 1;
                if (iLast < ast.ass.size()) {
                    sL = ast.ass.get(iLast);
                    if (EmptyExpr(sL.lhs.sub)) {
                        lastAssignmentHasNoSubscript = true;
                    }
                }
            }

            /*
             * If there are assignments to multiple variables, then this sets
             * hasMultiplevars true on the first execution of the outer while loop.
             */
            if (iLast != ast.ass.size()) {
                hasMultipleVars = true;
            }

            iLast = iLast - 1;
            // All statements from iFirst to iLast are to the same variable

            /*
             * Throws an error if there are multiple assignments to the variable
             * in different statements, or if there are multiple assignments to
             * the variable in this statement and at least one of them has no
             * subscript.
             */
            if (cThis.Set(sF.lhs.var) > 1 ||
                    (iLast - iFirst > 0 && hasAssignmentWithNoSubscript)) {
                /***********************************************************
                 * The following was changed by LL on 3 Mar 06 to use       *
                 * AST.location to properly report the location of an       *
                 * error in a line created by expanding a macro.            *
                 * However, it doesn't work very well otherwise.  This      *
                 * should be fixed.                                         *
                 ***********************************************************/
                throw new PcalTLAGenException("Multiple assignment to " + sF.lhs.var, ast /* sF */);
            }
            numAssigns = numAssigns + 1;
            if (hasMultipleVars) {
                sb.append("/\\ ");
            }
            if (iFirst == iLast) {
                /*
                 * This is a single assignment to the variable.
                 */
                final AST.SingleAssign sass = sF;

                addLeftParen(sass.getOrigin());
                final TLAExpr sub = AddSubscriptsToExpr(sass.lhs.sub, SubExpr(Self(context)), c);
                final TLAExpr rhs = AddSubscriptsToExpr(sass.rhs, SubExpr(Self(context)), c);
                if (mp
                        && (sass.lhs.var.equals("pc") || IsProcedureVar(sass.lhs.var) || IsProcessSetVar(sass.lhs.var) || sass.lhs.var
                        .equals("stack"))) {
                    /* Generate single assignment to variable with self subscript */
                    sb.append(sass.lhs.var);
                    sb.append("' = [");
                    final int wrapCol = sb.length() + 2;
                    sb.append(sass.lhs.var);
                    sb.append(" EXCEPT ");

                    final ArrayList<String> selfAsSV = self.toStringVector();

                    // The test for selfAsSV size added by LL on 22 Jan 2011
                    // because wrapping screws up the kludgeToFixPCHandlingBug
                    // hack.
                    if ((sb.length() + prefix.length() > pcalParams.ssWrapColumn)
                            && (selfAsSV.size() == 0)) {
//                        lines.add(sb.toString());
                        addOneLineOfTLA(sb.toString());
                        sb = new StringBuilder(NSpaces(wrapCol));
                    }
                    sb.append("![");
                    addOneTokenToTLA(sb.toString());
                    addLeftParen(self.getOrigin());
                    addExprToTLA(self);
                    addRightParen(self.getOrigin());

                    addOneTokenToTLA("]");
                    final ArrayList<String> sv = sub.toStringVector();
                    /*****************************************************
                     * Was                                                *
                     *                                                    *
                     *       ArrayList sv = sass.lhs.sub.toStringVector();   *
                     *                                                    *
                     * Changed by Chi Ho on 3 Aug 2006 to add             *
                     * subscript.  See bug_06_08_03.                      *
                     *****************************************************/
                    if (sv.size() > 0) {
                        addLeftParen(sub.getOrigin());
                        addExprToTLA(sub);
                        addRightParen(sub.getOrigin());

                    }
                    addOneTokenToTLA(" = ");
                    addLeftParen(rhs.getOrigin());
                    addExprToTLA(rhs);
                    addRightParen(rhs.getOrigin());
                    addOneTokenToTLA("]");
                    sb = new StringBuilder();
                } else if (!EmptyExpr(sass.lhs.sub)) {
                    /*
                     * Generate single assignment to variable with no [self] subscript
                     * but with an explicit subscript.
                     */
                    sb.append(sass.lhs.var);
                    sb.append("' = [");
                    sb.append(sass.lhs.var);
                    sb.append(" EXCEPT !");
                    addOneTokenToTLA(sb.toString());
                    addLeftParen(sub.getOrigin());
                    addExprToTLA(sub);
                    addRightParen(sub.getOrigin());
                    addOneTokenToTLA(" = ");
                    addLeftParen(rhs.getOrigin());
                    addExprToTLA(rhs);
                    addRightParen(rhs.getOrigin());
                    addOneTokenToTLA("]");
                    sb = new StringBuilder();
                } else {
                    /*
                     * Generate assignment to a variable with no subscript at all.
                     */
                    sb.append(sass.lhs.var);
                    sb.append("' = ");
//                    int here = sb.length();
                    final boolean needsParens = NeedsParentheses(rhs.toStringVector());
                    if (needsParens) {
                        sb.append("(");
                    }
                    addOneTokenToTLA(sb.toString());
                    addLeftParen(rhs.getOrigin());
                    addExprToTLA(rhs);
                    addRightParen(rhs.getOrigin());
                    if (needsParens) {
                        addOneTokenToTLA(")");
                    }

//                    ArrayList sv = Parenthesize(rhs.toStringVector());
//                    /*******************************************************
//                    * Call of Parenthesize added by LL on 27 Feb 2008.     *
//                    * See bug_08-02-18.                                    *
//                    *******************************************************/
//                    for (int v = 0; v < sv.size(); v++)
//                    {
//                        sb.append((String) sv.get(v));
//                        lines.add(sb.toString());
//                        sb = new StringBuilder(NSpaces(here));
//                    }
// Debugging

                    sb = new StringBuilder();
                }
                addRightParen(sass.getOrigin());
            } else {
                /*
                 * Multiple assignments to the same variable, which must therefore
                 * each have a user-specified subscript.
                 */
                AST.SingleAssign sass = sF;
                sb.append(sass.lhs.var);
                sb.append("' = [");
                sb.append(sass.lhs.var);
                sb.append(" EXCEPT ");
                int cc = sb.length();
                /*
                 * If this  the first variable, so i = 0, then sb does not contain
                 * any spaces to compensate for the missing prefix; otherwise it
                 * does.
                 */
                if (i == 0) {
                    cc = cc + prefix.length();
                }
                final boolean subscript = (mp && (IsProcedureVar(sass.lhs.var) || IsProcessSetVar(sass.lhs.var)));
                while (iFirst <= iLast) {
                    sass = ast.ass.get(iFirst);
                    final TLAExpr sub = AddSubscriptsToExpr(sass.lhs.sub, SubExpr(Self(context)), c);
                    final TLAExpr rhs = AddSubscriptsToExpr(sass.rhs, SubExpr(Self(context)), c);
                    addLeftParen(sass.getOrigin());
                    sb.append("!");

                    // On 21 Jan 2011, LL moved the following statement to below the if
                    // to correct part 3 of bug_11_01_13.
                    //
//                    int here = sb.length();
                    if (subscript) {
                        /*
                         * This variable has a "self" subscript in addition to its user-specified
                         * subscript.
                         */
                        sb.append("[");
                        addOneTokenToTLA(sb.toString());
                        final TLAExpr self = Self(context);
                        addLeftParen(self.getOrigin());
                        addExprToTLA(self);
                        addOneTokenToTLA("]");

                    } else {
                        addOneTokenToTLA(sb.toString());
                    }

                    addLeftParen(sub.getOrigin());
                    addExprToTLA(sub);
                    addRightParen(sub.getOrigin());
                    addOneTokenToTLA(" = ");
                    addLeftParen(rhs.getOrigin());
                    addExprToTLA(rhs);
                    addRightParen(rhs.getOrigin());
                    addRightParen(sass.getOrigin());
                    addOneTokenToTLA((iFirst == iLast) ? "]" : ",");
                    sb = new StringBuilder();
                    if (iFirst < iLast) {
                        endCurrentLineOfTLA();
                        AddSpaces(sb, cc);
                    }
                    iFirst = iFirst + 1;
                }
            }

//            vlines.add(lines);
            i = iLast + 1;
            if (i < ast.ass.size()) {
                endCurrentLineOfTLA();
                AddSpaces(sb, prefix.length());
            }
        }
        addRightParen(ast.getOrigin());
        endCurrentLineOfTLA();

        c.Merge(cThis);
        // Append generated code to tlacode
    }

    /**
     * Generate TLA+ for if statement. Each branch has its own
     * UNCHANGED that lists variables that were changed in the
     * other branch. This is a little difficult since we don't
     * know the UNCHANGED for the Then branch until the code
     * for the Else branch is generated. So, we fix the
     * line in the Then branch after the Else branch is done.
     * The corresponding mappingVector line also has to be changed,
     * but that's not a problem because the UNCHANGED is a TLA+
     * token with no corresponding source.
     */
    private void GenIf(final AST.If ast, final Changed c, final String context, final String prefix, final int col) throws PcalTLAGenException {
        final Changed cThen = new Changed(c);
        final Changed cElse = new Changed(c);
        int lineUncThen;
        StringBuilder sb = new StringBuilder(prefix);
        TLAExpr test;
        test = AddSubscriptsToExpr(ast.test, SubExpr(Self(context)), c);
//        ArrayList sv = test.toStringVector();
        sb.append("IF ");
        int here = sb.length();
        /*************************************************************
         * LL removed a bogus "- 1" here on 31 Jan 2006.              *
         *************************************************************/
        addLeftParen(ast.getOrigin());
        addOneTokenToTLA(sb.toString());
        addExprToTLA(test);
        endCurrentLineOfTLA();

        sb = new StringBuilder(NSpaces(here));
        sb.append("THEN ");
        here = sb.length();

        sb.append("/\\ ");
        for (int i = 0; i < ast.Then.size(); i++) {
            GenStmt(ast.Then.get(i), cThen, context, sb.toString(),
                    /*******************************************************************
                     * LL added the +3 on 18 Feb 2006 to take account of the            *
                     * indentation of the "IF ".                                        *
                     *******************************************************************/
                    here + 3);
            sb = new StringBuilder(NSpaces(here) + "/\\ ");
        }
        lineUncThen = tlacode.size();
//        tlacode.add(sb.toString());
        addOneLineOfTLA(sb.toString());
        sb = new StringBuilder(NSpaces(here - "THEN ".length()) + "ELSE ");
        here = sb.length();
        if (ast.Else.size() == 0) {
            sb.append("/\\ TRUE");
//            tlacode.add(sb.toString());
            addOneLineOfTLA(sb.toString());

            sb = new StringBuilder(NSpaces(here) + "/\\ ");
        } else {
            sb.append("/\\ ");
            for (int i = 0; i < ast.Else.size(); i++) {
                GenStmt(ast.Else.get(i), cElse, context, sb.toString(),
                        /*******************************************************************
                         * LL added the +3 on 18 Feb 2006 to take account of the            *
                         * indentation of the "IF ".                                        *
                         *******************************************************************/
                        here + 3);
                sb = new StringBuilder(NSpaces(here) + "/\\ ");
            }
        }
        // Generate UNCHANGED for the ELSE branch
        if (cElse.NumUnchanged(cThen) > 1) {
            final List<String> uncElse = cElse.Unchanged(cThen, pcalParams.wrapColumn - sb.length() - "UNCHANGED << ".length());
            sb.append("UNCHANGED << ");
            final int cc = sb.length();
            sb.append(uncElse.get(0));
            for (int i = 1; i < uncElse.size(); i++) {
//                tlacode.add(sb.toString());
                addOneLineOfTLA(sb.toString());
                sb = new StringBuilder(NSpaces(cc));
                sb.append(uncElse.get(i));
            }
            sb.append(" >>");
//            tlacode.add(sb.toString());
            addOneTokenToTLA(sb.toString());
            addRightParen(ast.getOrigin());
            endCurrentLineOfTLA();
        } else if (cElse.NumUnchanged(cThen) == 1) {   // Change made by LL on 16 Mar 2011 so that, if there is a single
            // unchanged variable v, it produces v' = v if v is a short variable,
            // otherwise it produces UNCHANGED v
            //
            // sb.append("UNCHANGED " + cElse.Unchanged(cThen));
            final String uc = cElse.Unchanged(cThen);
            if (uc.length() > 5) {
                sb.append("UNCHANGED ").append(uc);
            } else {
                sb.append(uc).append("' = ").append(uc);
            }
//            tlacode.add(sb.toString());
            addOneTokenToTLA(sb.toString());
            addRightParen(ast.getOrigin());
            endCurrentLineOfTLA();
        } else {
            /*
             * There is no UNCHANGED after the ELSE, so we have to put
             * the RightParen for the whole if statement at the end of
             * the last line already generated
             */
            ((List<RightParen>) mappingVector.get(mappingVector.size() - 1))
                    .add(new MappingObject.RightParen(ast.getOrigin().getEnd()));
        }

        // Patch up the UNCHANGED for the THEN branch
        sb = new StringBuilder(tlacode.get(lineUncThen));
        tlacode.remove(lineUncThen);
        mappingVector.remove(lineUncThen);
        if (cThen.NumUnchanged(cElse) > 1) {
            final List<String> uncThen = cThen.Unchanged(cElse, pcalParams.wrapColumn - sb.length() - "UNCHANGED << ".length());
            sb.append("UNCHANGED << ");
            final int cc = sb.length();
            sb.append(uncThen.get(0));
            for (int i = 1; i < uncThen.size(); i++) {
                tlacode.add(lineUncThen, sb.toString());

                //set the mappingVector entry
                mappingVector.add(lineUncThen, stringToTLATokens(sb.toString()));

                lineUncThen = lineUncThen + 1;
                sb = new StringBuilder(NSpaces(cc));
                sb.append(uncThen.get(i));
            }
            sb.append(" >>");
            tlacode.add(lineUncThen, sb.toString());
            final List<MappingObject> vec = stringToTLATokens(sb.toString());

            // The following is bogus because the RightParen for the
            // entire procedure is inserted after (or instead of) the
            // ELSE's UNCHANGED
            // vec.add(new MappingObject.RightParen(ast.getOrigin().getEnd()));

            mappingVector.add(lineUncThen, vec);

        } else if (cThen.NumUnchanged(cElse) == 1) {   // Change made by LL on 16 Mar 2011 so that, if there is a single
            // unchanged variable v, it produces v' = v if v is a short variable,
            // otherwise it produces UNCHANGED v
            final String uc = cThen.Unchanged(cElse);
            if (uc.length() > 5) {
                sb.append("UNCHANGED ").append(uc);
            } else {
                sb.append(uc).append("' = ").append(uc);
            }
            tlacode.add(lineUncThen, sb.toString());
            final ArrayList<MappingObject> vec = stringToTLATokens(sb.toString());
            // The following is bogus because the RightParen for the
            // entire procedure is inserted after (or instead of) the
            // ELSE's UNCHANGED
            // vec.add(new MappingObject.RightParen(ast.getOrigin().getEnd()));
            mappingVector.add(lineUncThen, vec);
        }

        // Merge the change lists together
        c.Merge(cThen);
        c.Merge(cElse);
    }

    /**
     * Returns the vector of MappingObjects containing the BeginTLAToken and
     * EndTLAToken that are put in the mappingVector by a call of addOneLineOfTLA.
     * The code was essentially copied from addOneTokenToTLA.
     */
    private ArrayList<MappingObject> stringToTLATokens(final String token) {
        final ArrayList<MappingObject> result = new ArrayList<>(3);

        String trimmedToken = token.trim();

        int numberOfLeftTrimmedTokens =
                (trimmedToken.length() == 0) ? -1 :
                        token.indexOf(trimmedToken.charAt(0));

        /**
         * Handle a token of only space characters.
         */
        if (numberOfLeftTrimmedTokens == -1) {
            numberOfLeftTrimmedTokens = 0;
            trimmedToken = token;
        }

        final int objBegin = numberOfLeftTrimmedTokens;
        result.add(new MappingObject.BeginTLAToken(objBegin));
        result.add(new MappingObject.EndTLAToken(objBegin + trimmedToken.length()));
        return result;
    }

    /********************************************************/
    /* Assert(ast.expr, "Failure of assertion at... ")      */

    /***********************************************************************
     * Added by LL on 30 Jan 2006.                                          *
     *                                                                      *
     * Generate TLA+ for the `either' statement.  This performs the same    *
     * sort of hackery as for the `if' statement, necessitated by the       *
     * design flaw commented on above.
     **
     ***********************************************************************/
    private void GenEither(final AST.Either ast, final Changed c, final String context, final String prefix, final int col)
            throws PcalTLAGenException {
        final Changed allC = new Changed(c);
        /*******************************************************************
         * Accumulates the variable changes of all the clauses.             *
         *******************************************************************/
        final Changed[] cOrs = new Changed[ast.ors.size()];
        /*******************************************************************
         * cOrs[i] is the Changed vector for the i-th `or' clause.          *
         *******************************************************************/
        final int[] ucLocs = new int[ast.ors.size()]; // location of unchangeds.
        /******************************************************************
         * tlaout.get(ucLocs[i]) is the UNCHANGED clause for the     *
         * i-th `or' clause.                                               *
         ******************************************************************/
        StringBuilder sb = new StringBuilder(prefix);
        final int prefixIndent = sb.length();
        sb.append("\\/ ");
        final int here = sb.length();
        /*******************************************************************
         * The number of columns to the left of the code generated for      *
         * each `or' clause.                                                *
         *******************************************************************/

        /*
         * Add the left paren for the statement.
         */
        addLeftParen(ast.getOrigin());
        /*********************************************************************
         * Produce the output for the clauses, but with a dummy line in       *
         * place of the UNCHANGED clause, and compute allC, cOrs, and         *
         * ucLocs.                                                            *
         *********************************************************************/
        for (int i = 0; i < ast.ors.size(); i++) {
            if (i != 0) {
                sb = new StringBuilder(NSpaces(prefixIndent) + "\\/ ");
            }
            sb.append("/\\ ");
            final ArrayList orClause = (ArrayList) ast.ors.get(i);
            final Changed cC = new Changed(c);
            /***********************************************************
             * On 6 Jun 2010, LL added the "+3" in the following call   *
             * of GenStmt.  This seems to fix a bug which caused        *
             *                                                          *
             *    either when \/ A                                      *
             *                \/ B                                      *
             *        or ...                                            *
             *                                                          *
             * to produce                                               *
             *    \/ /\ \/ A                                            *
             *       \/ B                                               *
             *    \/ ...                                                *
             ***********************************************************/
            for (Object o : orClause) {
                /***********************************************************
                 * On 6 Jun 2010, LL added the "+3" in the following call   *
                 * of GenStmt.  This seems to fix a bug which caused        *
                 *                                                          *
                 *    either when \/ A                                      *
                 *                \/ B                                      *
                 *        or ...                                            *
                 *                                                          *
                 * to produce                                               *
                 *    \/ /\ \/ A                                            *
                 *       \/ B                                               *
                 *    \/ ...                                                *
                 ***********************************************************/
                GenStmt((AST) o, cC, context, sb.toString(), here + 3);
                sb = new StringBuilder(NSpaces(here) + "/\\ ");
            }
            cOrs[i] = cC;
            allC.Merge(cC);
            ucLocs[i] = tlacode.size();
//            tlacode.add("Replace by UNCHANGED"); //
            addOneLineOfTLA("Replace by UNCHANGED");
        }
        // End of for i

        /**********************************************************************
         * Insert real UNCHANGED clauses.  Note that we have to go through     *
         * loop backwards since we will remove a line of output for each `or'  *
         * clause that doesn't get an UNCHANGED.                               *
         **********************************************************************/
        int i = ast.ors.size();
        while (i > 0) {
            i = i - 1;
            tlacode.remove(ucLocs[i]);
            mappingVector.remove(ucLocs[i]);
            final int numUnchanged = cOrs[i].NumUnchanged(allC);
            final String NotChanged = cOrs[i].Unchanged(allC);
            if (numUnchanged > 1) {
                /*
                 * The line should be wrapped if it's too long.
                 */
                final String line = NSpaces(here) + "/\\ UNCHANGED <<" + NotChanged + ">>";
                tlacode.add(ucLocs[i], line);
                mappingVector.add(ucLocs[i], stringToTLATokens(line));
            } else if (numUnchanged == 1) {   // Change made by LL on 16 Mar 2011 so that, if there is a single
                // unchanged variable v, it produces v' = v if v is a short variable,
                // otherwise it produces UNCHANGED v
                //
                // tlacode.insertElementAt(NSpaces(here) + "/\\ UNCHANGED " + NotChanged, ucLocs[i]);
                if (NotChanged.length() > 5) {
                    final String line = NSpaces(here) + "/\\ UNCHANGED " + NotChanged;
                    tlacode.add(ucLocs[i], line);
                    mappingVector.add(ucLocs[i], stringToTLATokens(line));
//                    tlacode.insertElementAt(NSpaces(here) + "/\\ UNCHANGED " + NotChanged, ucLocs[i]);
                } else {
                    final String line = NSpaces(here) + "/\\ " + NotChanged + "' = " + NotChanged;
                    tlacode.add(ucLocs[i], line);
                    mappingVector.add(ucLocs[i], stringToTLATokens(line));
                }
            }
        }
        /*
         * Add the right paren for the entire statement.
         */
        ((ArrayList<RightParen>) mappingVector.get(mappingVector.size() - 1))
                .add(new MappingObject.RightParen(ast.getOrigin().getEnd()));
        /**********************************************************************
         * Add the statement's unchangeds to c.                                *
         **********************************************************************/
        c.Merge(allC);
    }

    /********************************************************/
    /* I generate a TRUE conjunct, which is useless, but so */
    /* is a skip statement.                                 */

    private void GenWith(final AST.With ast, final Changed c, final String context, final String prefix, final int col) throws PcalTLAGenException {
        addLeftParen(ast.getOrigin());
        StringBuilder sb = new StringBuilder(prefix);
        final TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
//        ArrayList sv = exp.toStringVector();
        if (ast.isEq) {
            /* generate LET statement */
            sb.append("LET ");
            sb.append(ast.var);
            sb.append(" == ");
            addOneTokenToTLA(sb.toString());
            addLeftParen(exp.getOrigin());
            addExprToTLA(exp);
            addRightParen(exp.getOrigin());
            addOneTokenToTLA(" IN");
            /*************************************************************
             * LL changed "col + 4" to "col + 2" here to correct an       *
             * alignment problem on 31 Jan 2006.                          *
             *************************************************************/
        } else {
            /* generate \E statement */
            sb.append("\\E ");
            sb.append(ast.var);
            sb.append(" \\in ");
            addOneTokenToTLA(sb.toString());
            addLeftParen(exp.getOrigin());
            addExprToTLA(exp);
            addRightParen(exp.getOrigin());
//            int here = sb.le
            addOneTokenToTLA(":");
        }
        endCurrentLineOfTLA();
        sb = new StringBuilder(NSpaces(col + 2));
        if (ast.Do.size() > 1)
            sb.append("/\\ ");
        for (int i = 0; i < ast.Do.size(); i++) {
            GenStmt(ast.Do.get(i), c, context, sb.toString(), sb.length());
            sb = new StringBuilder(NSpaces(col + 2) + "/\\ ");
        }
        // tlacode.add(NSpaces(col) + ")");

        /*
         * Add the right paren for the entire statement.
         */
        ((ArrayList<RightParen>) mappingVector.get(mappingVector.size() - 1))
                .add(new MappingObject.RightParen(ast.getOrigin().getEnd()));
    }

    private void GenWhen(final AST.When ast, final Changed c, final String context, final String prefix, final int col) throws PcalTLAGenException {
        addOneTokenToTLA(prefix);

//        StringBuilder sb = new StringBuilder(prefix);
        final TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
        addLeftParen(exp.getOrigin());
        addExprToTLA(exp);
        addRightParen(exp.getOrigin());
        endCurrentLineOfTLA();
    }

    private void GenPrintS(final AST.PrintS ast, final Changed c, final String context, final String prefix, final int col)
            throws PcalTLAGenException {
        final TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
        addLeftParen(ast.getOrigin());
        addOneTokenToTLA(prefix + "PrintT(");
        addExprToTLA(exp);
        addOneTokenToTLA(")");
        addRightParen(ast.getOrigin());
        endCurrentLineOfTLA();

    }

    /**
     *
     *******************************************************/
    private void GenAssert(final AST.Assert ast, final Changed c, final String context, final String prefix, final int col)
            throws PcalTLAGenException {
        addLeftParen(ast.getOrigin());
        StringBuilder sb = new StringBuilder(prefix);
        final StringBuilder sc = new StringBuilder();
        final TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
//        ArrayList sv = exp.toStringVector();
        sb.append("Assert(");
        addOneTokenToTLA(sb.toString());
        addLeftParen(exp.getOrigin());
        addExprToTLA(exp);
        addRightParen(exp.getOrigin());
        final int here = sb.length();
        sb = new StringBuilder(", ");
        sc.append("\"Failure of assertion at ");
        sc.append(ast.location());
        // modified on 23 Mar 2006 by LL to use location() instead of
        // ast.line and ast.col
        sc.append(".\")");
        if (tlacodeNextLine.length() + sb.length() + sc.length() < pcalParams.wrapColumn) {
            addOneTokenToTLA(sb.toString() + sc);
        } else {
            addOneTokenToTLA(sb.toString());
            endCurrentLineOfTLA();
            addOneTokenToTLA(NSpaces(here) + sc);
        }
        addRightParen(ast.getOrigin());
        endCurrentLineOfTLA();
    }

    /***********************************/
    /* Generate the Init == statement. */

    /********************************************************/
    private void GenSkip(final AST.Skip ast, final Changed c, final String context, final String prefix, final int col) {
//        tlacode.add(prefix + "TRUE");
        addOneTokenToTLA(prefix);
        addLeftParen(ast.getOrigin());
        addOneTokenToTLA("TRUE");
        addRightParen(ast.getOrigin());
        endCurrentLineOfTLA();
    }

    /************************************/
    /* Generate the Next == definition. */

    /***********************************************************************
     * Generate the VARIABLES declaration(s), output the TLA+ "code" from   *
     * a `define' statement, if any, and generate the definition of         *
     * `vars'.                                                              *
     *                                                                      *
     * Method renamed from GenVars and given the defs argument by LL on     *
     * 25 Jan 2006 to handle the `define' statement.                        *
     ***********************************************************************/
    private void GenVarsAndDefs(final ArrayList<AST.VarDecl> globals, final ArrayList<AST.Procedure> procs, final ArrayList<AST.Process> processes, final TLAExpr defs)
            throws PcalTLAGenException {
        /*******************************************************************
         * lVars and gVars are vectors of strings, each element being a     *
         * variable name.  They hold the local and global variables,        *
         * respectively.                                                    *
         *******************************************************************/
        final ArrayList<String> lVars = new ArrayList<>();
        final ArrayList<String> gVars = new ArrayList<>();

        /**
         * lVarsSource and gVarsSource are vectors of AST.VarDecl objects that
         * generated the elements of lVars and gVars, where PVarDecl objects
         * are converted to VarDecl objects.
         */
        final ArrayList<VarDecl> lVarsSource = new ArrayList<>();
        final ArrayList<VarDecl> gVarsSource = new ArrayList<>();

        /*******************************************************************
         * Set gVars to the global variables, including pc and `stack' if   *
         * there are procedures, and add these variables to vars.           *
         *******************************************************************/
        if (globals != null)
            for (final VarDecl decl : globals) {
                gVars.add(decl.var);
                gVarsSource.add(decl);
                vars.add(decl.var);
            }
        if (!parseAlgorithm.omitPC) {
            gVars.add("pc");
            /**
             * For added variables, create a VarDecl with null origin.
             */
            final AST.VarDecl pcVarDecl = new AST.VarDecl(pcalParams);
            pcVarDecl.var = "pc";
            gVarsSource.add(pcVarDecl);
            vars.add("pc");
        }
        if (procs != null && procs.size() > 0) {
            gVars.add("stack");
            /**
             * For added variables, create a VarDecl with null origin.
             */
            final AST.VarDecl pcVarDecl = new AST.VarDecl(pcalParams);
            pcVarDecl.var = "stack";
            gVarsSource.add(pcVarDecl);
            vars.add("stack");
        }
        /*******************************************************************
         * Add local procedure variables to lVars, vars, and pcV.           *
         *******************************************************************/
        if (procs != null)
            for (final AST.Procedure proc : procs) {
                if (proc.params != null)
                    for (int p = 0; p < proc.params.size(); p++) {
                        final AST.PVarDecl decl = proc.params.get(p);
                        lVars.add(decl.var);
                        lVarsSource.add(decl.toVarDecl());
                        vars.add(decl.var);
                        pcV.add(decl.var);
                    }
                if (proc.decls != null)
                    for (int p = 0; p < proc.decls.size(); p++) {
                        final AST.PVarDecl decl = proc.decls.get(p);
                        lVars.add(decl.var);
                        lVarsSource.add(decl.toVarDecl());
                        vars.add(decl.var);
                        pcV.add(decl.var);
                    }
            }

        /*******************************************************************
         * Add local process variables to lVars, vars, and psV for          *
         * variables local to process sets.                                 *
         *******************************************************************/
        if (processes != null)
            for (final AST.Process proc : processes) {
                if (proc.decls != null)
                    for (int p = 0; p < proc.decls.size(); p++) {
                        final VarDecl decl = proc.decls.get(p);
                        lVars.add(decl.var);
                        lVarsSource.add(decl);
                        vars.add(decl.var);
                        if (!proc.isEq)
                            psV.add(decl.var);
                    }
            }

        /********************************************************************
         * Add a declaration of the constant defaultInitValue if it is       *
         * used.  (Added by LL on 22 Aug 2007.)                              *
         ********************************************************************/
        if (parseAlgorithm.hasDefaultInitialization) {
            addOneLineOfTLA("CONSTANT defaultInitValue");
        }

        if (EmptyExpr(defs)) {
            /******************************************************************
             * There is no `define' statement.  In this case, generate a       *
             * single VARIABLES statement and set gVars to vector of all       *
             * variables.                                                      *
             ******************************************************************/
            gVars.addAll(lVars);
            gVarsSource.addAll(lVarsSource);
            GenVarDecl(gVars, gVarsSource);
        } else {
            /******************************************************************
             * There is a `define' statement.  In this case, must declare      *
             * global and local variables separately.  Also, set gVars to      *
             * vector of all variables.                                        *
             ******************************************************************/
            GenVarDecl(gVars, gVarsSource);
            addOneLineOfTLA("");
            addOneLineOfTLA("(* define statement *)");
            addExprToTLA(defs);
            addOneLineOfTLA("");
            GenVarDecl(lVars, lVarsSource); // to be fixed
            gVars.addAll(lVars);
            gVarsSource.addAll(lVarsSource);
        }
        addOneLineOfTLA("");

        /*
         * We check for the unlikely case in which there are no variables.
         * Without this check, the Init is not generated but appears in
         * the definition of Spec.
         */
        if (gVars.size() == 0) {
            throw new PcalTLAGenException("The algorithm has no variables.");
        }
        /*******************************************************************
         * Generate definition of var.                                     *
         *******************************************************************/
        addOneTokenToTLA("vars == << ");
        final int indent = tlacodeNextLine.length();
        for (int i = 0; i < gVars.size(); i++) {
            if (i > 0) {
                addOneTokenToTLA(", ");
            }
            final String vbl = gVars.get(i);
            final AST.VarDecl vblDecl = gVarsSource.get(i);
            final Region vblOrigin = vblDecl.getOrigin();
//            if (curLine.length() + vbl.length() + 1 > pcalParams.wrapColumn)
            if (tlacodeNextLine.length() + vbl.length() + 1 > pcalParams.wrapColumn) {
                endCurrentLineOfTLA();
                tlacodeNextLine = NSpaces(indent);
            }
            addOneSourceTokenToTLA(vbl, vblOrigin);
        }
//        if (curLine.length() + " >>".length() + 1 > pcalParams.wrapColumn)
        if (tlacodeNextLine.length() + " >>".length() + 1 > pcalParams.wrapColumn) {
//            var.append("\n" + NSpaces("vars ==".length()));
            endCurrentLineOfTLA();
            tlacodeNextLine = NSpaces("vars ==".length());
        }
        addOneTokenToTLA(" >>");
//        tlacode.add(var.toString());
        addOneLineOfTLA("");
    }

    /****************************************/
    /* Generate the Spec == ... definition. */
    /****************************************/

    /**
     * Generate a VARIABLE(S) declarations.  The varVec argument is a vector of
     * strings that are the variables to be declared.  It does nothing if
     * the vector has length 0.  The varVecSource argument is a vector
     * of the same size as varVec that contains the AST.VarDecl objects.
     * <p>
     * Method added by LL on 25 Jan 2006.
     * <p>
     * Modified 16 Dec 2011 to add varVecSource argument and generate TLA to
     * PCal mapping.
     *
     * @param varVec       A vector of strings.
     * @param varVecSource A vector of AST.VarDecl objects.
     */
    public void GenVarDecl(final ArrayList<String> varVec, final ArrayList<VarDecl> varVecSource) {
//        StringBuilder res = new StringBuilder();
//        StringBuilder curLine = new StringBuilder("VARIABLES ");
        // for measuring length
        if (varVec.size() == 0) {
            return;
        }
        if (varVec.size() > 1) {
//            res.append("VARIABLES ");
            addOneTokenToTLA("VARIABLES ");
        } else {
//            res.append("VARIABLE ");
            addOneTokenToTLA(TLAConstants.KeyWords.VARIABLE + " ");
        }
        for (int i = 0; i < varVec.size(); i++) {
            if (i > 0) {
                addOneTokenToTLA(", ");
            }
            final String vbl = varVec.get(i);
            final AST vblsource = varVecSource.get(i);
//            if (curLine.length() + vbl.length() + 1 > pcalParams.wrapColumn)
            if (tlacodeNextLine.length() + vbl.length() + 1 > pcalParams.wrapColumn) {
//                curLine = new String
                endCurrentLineOfTLA();
                if (varVec.size() > 1) {
//                    res.append(NSpaces("VARIABLES ".length()));
                    tlacodeNextLine = tlacodeNextLine + NSpaces("VARIABLES ".length());
                } else {
//                    res.append(NSpaces("VARIABLE ".length()));
                    tlacodeNextLine = tlacodeNextLine + NSpaces("VARIABLE ".length());
                }
            }
            addOneSourceTokenToTLA(vbl, vblsource.getOrigin());
        }
        //        tlacode.add(res.toString());
        endCurrentLineOfTLA();
    }

    /************************************/
    /* Generate the Termination ==      */

    /**
     * Generates the "ProcSet == ..." output.  It is just a union of all the
     * process sets, all on one line (except if a process set is a multi-line
     * expression).  It wouldn't be too hard to break long lines, but that
     * should be done later, if desired, after the TLA to PCal translation
     * is finished.
     */
    public void GenProcSet() {
        if (st.processes.size() == 0)
            return;
//        ps.append("ProcSet == ");
        addOneTokenToTLA("ProcSet == ");
        for (int i = 0; i < st.processes.size(); i++) {
            final PcalSymTab.ProcessEntry proc = st.processes.get(i);
//            ArrayList sv = proc.id.toStringVector();
            if (i > 0) {
//                ps.append(" \\cup ");
                addOneTokenToTLA(" \\cup ");
            }
            addLeftParen(proc.id.getOrigin());
            if (proc.isEq) {
//                ps.append("{");
                addOneTokenToTLA("{");
            } else {
//                ps.append("(");
                addOneTokenToTLA("(");
            }
            addExprToTLA(proc.id);
            if (proc.isEq) {
//                ps.append("}");
                addOneTokenToTLA("}");
            } else {
//                ps.append(")");
                addOneTokenToTLA(")");
            }
            addRightParen(proc.id.getOrigin());
        }
        endCurrentLineOfTLA();
        addOneLineOfTLA("");
    }

    /**********************************************************/
    /* For variables that need subscripts, add the subscript. */
    /* These are pc, stack, procedure variables, procedure    */
    /* parameters, and variables defined in process sets.     */
    /* Then, add primes to variables that have been changed   */
    /* according to c.                                        */
    /*   exprn : the original expression.                     */
    /*   sub : the subscript to be added (null if none)       */
    /*   c : the variables that have been changed (so need to */
    /*       be primed.                                       */

    /**
     *
     **********************************/
    private void GenInit(final ArrayList<AST.VarDecl> globals, final ArrayList<AST.Procedure> procs, final ArrayList<AST.Process> processes) throws PcalTLAGenException {
        final int col = "Init == ".length();
        StringBuilder is = new StringBuilder();
        is.append("Init == ");

        /* Global variables */
        if (globals != null && globals.size() > 0) {
            is.append("(* Global variables *)");
//            tlacode.add(is.toString());
            addOneLineOfTLA(is.toString());
            is = new StringBuilder(NSpaces(col));
            for (final VarDecl decl : globals) {
                addVarDeclToTLA(decl, is);
                is = new StringBuilder(NSpaces(col));
            }
        }
        if (procs != null && procs.size() > 0) {
            /* Procedure variables and parameters */
            /*******************************************************
             * Modified on 31 Jan 2006 by LL to add subscripts to   *
             * initialization expression if needed.  Also replaced  *
             * test for "\\in" with assertion that it can't occur,  *
             * since it's forbidden by the grammar.                 *
             *******************************************************/
            /*******************************************************
             * Modified on 31 Jan 2006 by LL to add subscripts to   *
             * initialization expression if needed.  Also replaced  *
             * test for "\\in" with assertion that it can't occur,  *
             * since it's forbidden by the grammar.                 *
             *******************************************************/
            for (final AST.Procedure proc : procs) {
                if (proc.params.size() == 0 && proc.decls.size() == 0)
                    // No parameters or procedure variables in this procedure
                    continue;
                is.append("(* Procedure ");
                is.append(proc.name);
                is.append(" *)");
//                tlacode.add(is.toString());
                addOneLineOfTLA(is.toString());
                is = new StringBuilder(NSpaces(col));
                for (int p = 0; p < proc.params.size(); p++) {
                    final AST.PVarDecl decl = proc.params.get(p);
                    if (!mp) {
                        addVarDeclToTLA(decl.toVarDecl(), is);
                    } else {
                        is.append("/\\ ");
                        addOneTokenToTLA(is.toString());
                        addLeftParen(decl.getOrigin());
//                    is.append(decl.var);
                        is = new StringBuilder(decl.var);
                        /*******************************************************
                         * Modified on 31 Jan 2006 by LL to add subscripts to   *
                         * initialization expression if needed.  Also replaced  *
                         * test for "\\in" with assertion that it can't occur,  *
                         * since it's forbidden by the grammar.                 *
                         *******************************************************/
                        PcalDebug.Assert(decl.isEq);
                        is.append(" = ");

//                    ArrayList sv;
//                    if (mp)
//                    {
//                        sv = AddSubscriptsToExpr(decl.val,
//                              SubExpr(Self("procedure")), new Changed(new ArrayList()))
//                                .toStringVector();
//                    } else
//                    {
//                        sv = Parenthesize(decl.val.toStringVector());
//                        /*************************************************
//                        * Call to Parenthesize added by LL on 27 Feb 2008. *
//                        * See bug_08-02-18.                              *
//                        *************************************************/
//                    }
//                    ;
//                    if (mp)
//                    {
                        is.append("[ self \\in ProcSet |-> ");
//                    }
                        addOneTokenToTLA(is.toString());
                        addLeftParen(decl.val.getOrigin());
                        addExprToTLA(
                                AddSubscriptsToExpr(decl.val,
                                        SubExpr(Self("procedure")),
                                        new Changed(new ArrayList<>())));
                        addRightParen(decl.val.getOrigin());
                        addOneTokenToTLA("]");
                        addRightParen(decl.getOrigin());
                        endCurrentLineOfTLA();

                    }
                    is = new StringBuilder(NSpaces(col));
                }
                for (int p = 0; p < proc.decls.size(); p++) {
                    /*
                     * Note: the following code is identical to the for loop
                     * code above for procedure variables.  (Well done, Keith!)
                     * I realized this too late to feel like procedurizing it.
                     */
                    final AST.PVarDecl decl = proc.decls.get(p);
                    if (!mp) {
                        addVarDeclToTLA(decl.toVarDecl(), is);
                    } else {
                        is.append("/\\ ");
                        addOneTokenToTLA(is.toString());
                        addLeftParen(decl.getOrigin());
//                    is.append(decl.var);
                        is = new StringBuilder(decl.var);

                        /*******************************************************
                         * Modified on 31 Jan 2006 by LL to add subscripts to   *
                         * initialization expression if needed.  Also replaced  *
                         * test for "\\in" with assertion that it can't occur,  *
                         * since it's forbidden by the grammar.                 *
                         *******************************************************/
                        PcalDebug.Assert(decl.isEq);
                        is.append(" = ");
//                    ArrayList sv;
//                    if (mp)
//                    {
//                        sv = AddSubscriptsToExpr(decl.val, SubExpr(Self("procedure")), new Changed(new ArrayList()))
//                                .toStringVector();
//                    } else
//                    {
//                        sv = Parenthesize(decl.val.toStringVector());
//                        /*************************************************
//                        * Call to Parenthesize added by LL on            *
//                        * 27 Feb 2008.  See bug_08-02-18.                *
//                        *************************************************/
//                    }
//                    ;
//                    if (mp)
//                    {
                        is.append("[ self \\in ProcSet |-> ");
//                    }
                        addOneTokenToTLA(is.toString());
                        addLeftParen(decl.val.getOrigin());
                        addExprToTLA(AddSubscriptsToExpr(
                                decl.val,
                                SubExpr(Self("procedure")),
                                new Changed(new ArrayList<>())));
                        addRightParen(decl.val.getOrigin());
                        addOneTokenToTLA("]");
                        addRightParen(decl.getOrigin());
                        endCurrentLineOfTLA();

                    }
                    is = new StringBuilder(NSpaces(col));
                }
            }
        }
        if (processes != null && processes.size() > 0) {
            /* Process variables */
            for (final AST.Process proc : processes) {
                if (proc.decls.size() == 0) // No variables in this procedure
                    continue;
                is.append("(* Process ");
                is.append(proc.name);
                is.append(" *)");
//                tlacode.add(is.toString());
                addOneLineOfTLA(is.toString());
                is = new StringBuilder(NSpaces(col));
                for (int p = 0; p < proc.decls.size(); p++) {
                    /*
                     * In the comments below, (( and )) represent
                     * MappingObject.LeftParen and MappingObject.RightParen
                     * objects.
                     */
                    final VarDecl decl = proc.decls.get(p);
                    is.append("/\\ ");
                    /*
                     * The following adds  /\ ((  to the TLA+ output.
                     */
                    addOneTokenToTLA(is.toString());
                    addLeftParen(decl.getOrigin());


                    if (proc.isEq) {
                        /*
                         * The source is
                         *
                         *     process (P = S) variables ... v  @@  Val
                         *
                         * where @@ is either "=" or "\in".  The TLA+ output is
                         *
                         *    /\ (( v @@ (( Val )) ))
                         */
                        is = new StringBuilder(decl.var);
                        if (decl.isEq) {
                            is.append(" = ");
                        } else {
                            is.append(" \\in ");
                        }
                        addOneTokenToTLA(is.toString());
                        addLeftParen(decl.val.getOrigin());
                        addExprToTLA(decl.val);
                        addRightParen(decl.val.getOrigin());
                    } else {
                        if (decl.isEq) {
                            /*
                             * The source is
                             *
                             *     process (P \in S) variables ... v = Val
                             *
                             * The TLA+ output is
                             *
                             *    /\ (( v = [self \in (( S )) |-> (( ValBar )) ] ))
                             *
                             * where ValBar obtained from Val by replacing each
                             * variable w of the process with w[self].
                             */
                            is = new StringBuilder(decl.var);
                            is.append(" = [self \\in ");
                            addOneTokenToTLA(is.toString());
                            addLeftParen(proc.id.getOrigin());
                            addExprToTLA(proc.id);
                            addRightParen(proc.id.getOrigin());
                            addOneTokenToTLA(TLAConstants.RECORD_ARROW);
                            addLeftParen(decl.val.getOrigin());
                            addExprToTLA(AddSubscriptsToExpr(
                                    decl.val,
                                    SubExpr(Self("procedure")),
                                    new Changed(new ArrayList<>())));

                        } else {
                            /*
                             * The source is
                             *
                             *    process (P \in S) variables ... v \in Val
                             *
                             * The TLA+ output is
                             *
                             *    /\ (( v \in [ (( S )) -> (( ValBar )) ] ))
                             *
                             * where ValBar is obtained from Val by replacing each
                             * variable w of the process with
                             *
                             *    w[CHOOSE self \in S : TRUE]
                             *
                             * We first set expr to the TLAExpr "CHOOSE self \in S : TRUE".
                             * (This is Keith's original code.)
                             */
                            final TLAExpr subexpr = proc.id.cloneAndNormalize();
                            TLAExpr expr = new TLAExpr();
                            expr.addLine();
                            expr.addToken(new TLAToken("[", 0, TLAToken.BUILTIN));
                            expr.addToken(new TLAToken("CHOOSE", 1, TLAToken.BUILTIN));
                            expr.addToken(new TLAToken("self", 8, TLAToken.IDENT));
                            expr.addToken(new TLAToken("\\in ", 13, TLAToken.BUILTIN));
                            expr.normalize();
                            expr.setOrigin(subexpr.getOrigin()); // see what this does.
                            try {
                                subexpr.prepend(expr, 1);
                                expr = new TLAExpr();
                                expr.addLine();
                                expr.addToken(new TLAToken(":", 0, TLAToken.BUILTIN));
                                expr.addToken(new TLAToken("TRUE", 2, TLAToken.BUILTIN));
                                expr.addToken(new TLAToken("]", 6, TLAToken.BUILTIN));
                                expr.prepend(subexpr, 1);
                            } catch (final TLAExprException e) {
                                throw new PcalTLAGenException(e.getMessage());
                            }

                            /*
                             * Now we output the TLA+ code.
                             */
                            is = new StringBuilder(decl.var);
                            is.append(" \\in [");
                            addOneTokenToTLA(is.toString());
                            addLeftParen(proc.id.getOrigin());
                            addExprToTLA(proc.id);
                            addRightParen(proc.id.getOrigin());
                            addOneTokenToTLA(" -> ");
                            addLeftParen(decl.val.getOrigin());
                            addExprToTLA(AddSubscriptsToExpr(
                                    decl.val, expr, new Changed(new ArrayList<>())));
                        }
                        addRightParen(decl.val.getOrigin());
                        addOneTokenToTLA("]");
                    }
                    /*
                     * This adds the final )) .
                     */
                    addRightParen(decl.getOrigin());
                    endCurrentLineOfTLA();
                    is = new StringBuilder(NSpaces(col));

// everything from here down to the end of the for p loop should be commented out
//                    is.append(decl.var);
//                    is = new StringBuilder(decl.var);
//                    if (decl.isEq)
//                        is.append(" = ");
//                    else
//                        is.append(" \\in ");
//                    /*******************************************************
//                    * Modified on 31 Jan 2006 by LL to add subscripts to   *
//                    * initialization expression for process set.  Note     *
//                    * tricky subscript that is added in expr for           *
//                    * declaration of form "v \in expr".                    *
//                    *                                                      *
//                    * Also modified the whole method of producing the      *
//                    * variable declaration because the original destroyed  *
//                    * the formatting of the expression proc.id, leading    *
//                    * to bad or incorrect formatting if the process id     *
//                    * set expression was not trivial.                      *
//                    *******************************************************/
//                    ArrayList sv;
//                    TLAExpr sve;
//                    if (proc.isEq)
//                    {
//                        /***************************************************
//                        * No substitution unless it's a process set.       *
//                        ***************************************************/
//                        sve = decl.val; // .toStringVector();
//                    } else
//                    {
//                        if (decl.isEq)
//                        {
//                            /***********************************************
//                            * For declaration "v = ...", add subscript     *
//                            * "[self]".                                    *
//                            ***********************************************/
//                            sve = AddSubscriptsToExpr(decl.val, SubExpr(Self("procedure")), new Changed(new ArrayList()));
//                        } else
//                        {
//                            /************************************************
//                            * For declaration "v \in ...", add subscript    *
//                            * "[CHOOSE self \in Process Id Set : TRUE]".    *
//                            *                                               *
//                            * This weird subscript is needed in the         *
//                            * following weird case:                         *
//                            *                                               *
//                            *    process (P \in S)                          *
//                            *    variable v \in T, w \in R(v)               *
//                            *                                               *
//                            * This produces the following conjunct in       *
//                            * the initial predicate for w:                  *
//                            *                                               *
//                            *   w \in [S -> R(v[CHOOSE self \in S : TRUE])] *
//                            ************************************************/
//                            TLAExpr subexpr = proc.id.cloneAndNormalize();
//
//                            TLAExpr expr = new TLAExpr();
//                            expr.addLine();
//                            expr.addToken(new TLAToken("[", 0, TLAToken.BUILTIN));
//                            expr.addToken(new TLAToken("CHOOSE", 1, TLAToken.BUILTIN));
//                            expr.addToken(new TLAToken("self", 8, TLAToken.IDENT));
//                            expr.addToken(new TLAToken("\\in ", 13, TLAToken.BUILTIN));
//                            expr.normalize();
//
//                            try
//                            {
//                                subexpr.prepend(expr, 1);
//                                expr = new TLAExpr();
//                                expr.addLine();
//                                expr.addToken(new TLAToken(":", 0, TLAToken.BUILTIN));
//                                expr.addToken(new TLAToken("TRUE", 2, TLAToken.BUILTIN));
//                                expr.addToken(new TLAToken("]", 6, TLAToken.BUILTIN));
//                                expr.prepend(subexpr, 1);
//                            } catch (TLAExprException e)
//                            {
//                                throw new PcalTLAGenException(e.getMessage());
//                            }
//
//                            sve = AddSubscriptsToExpr(decl.val, expr, new Changed(new ArrayList()));
//                        }
//                        ;
//                    }
//                    ;
//                    TLAExpr expr = new TLAExpr();
//                    expr.addLine();
//                    if (!proc.isEq)
//                    {
//                        expr.addToken(new TLAToken("[", 0, TLAToken.BUILTIN));
//                        if (decl.isEq)
//                        {
//                            expr.addToken(new TLAToken("self", 1, TLAToken.IDENT));
//                            expr.addToken(new TLAToken("\\in ", 6, TLAToken.BUILTIN));
//                        }
//                        ;
//                        expr.normalize();
//                        TLAExpr expr2 = proc.id.cloneAndNormalize();
//                        try
//                        {
//                            expr2.prepend(expr, 0);
//                            expr = new TLAExpr();
//                            expr.addLine();
//                            if (decl.isEq)
//                            {
//                                expr.addToken(new TLAToken("|->", 0, TLAToken.BUILTIN));
//                            } else
//                            {
//                                expr.addToken(new TLAToken("->", 0, TLAToken.BUILTIN));
//                            }
//                            ;
//                            expr.prepend(expr2, 1);
//                            sve.prepend(expr, 1);
//                        } catch (TLAExprException e)
//                        {
//                            throw new PcalTLAGenException(e.getMessage());
//                        }
//                    }
//                    ;
//                    sv = sve.toStringVector();
//                    if (proc.isEq)
//                    {
//                        sv = Parenthesize(sv);
//                    }
//                    ;
//                    /*****************************************************
//                    * Call to Parenthesize added by LL on 27 Feb 2008.   *
//                    * See bug_08-02-18.                                  *
//                    *****************************************************/
//                    int col2 = is.length();
//                    is.append((String) sv.get(0));
//                    for (int v = 1; v < sv.size(); v++)
//                    {
//                        tlacode.add(is.toString());
//                        is = new StringBuilder(NSpaces(col2));
//                        is.append((String) sv.get(v));
//                    }
//                    if (!proc.isEq)
//                        is.append("]");
//                    tlacode.add(is.toString());
//                    is = new StringBuilder(NSpaces(col));
// end of section to be commented out
                } // end of for p loop.
            }
        }

        /* stack initial value */
        if (procs != null && procs.size() > 0) {
            if (mp)
                is.append("/\\ stack = [self \\in ProcSet |-> << >>]");
            else
                is.append("/\\ stack = << >>");
//            tlacode.add(is.toString());
            addOneLineOfTLA(is.toString());
            is = new StringBuilder(NSpaces(col));
        }
        /* pc initial value */
        if (!parseAlgorithm.omitPC) {
            if (mp) {
                // On 4 May 2012, LL added useCase flag to inhibit adding of CASE for
                // a single process or process set.
                final boolean useCase = st.processes.size() != 1;
                if (useCase) {
                    is.append("/\\ pc = [self \\in ProcSet |-> CASE ");
                } else {
                    is.append("/\\ pc = [self \\in ProcSet |-> ");
                }
                int colPC = is.length();
                if (boxUnderCASE)
                    colPC = colPC - 3;
                for (int p = 0; p < st.processes.size(); p++) {
                    final PcalSymTab.ProcessEntry pe = st.processes.get(p);
                    if (useCase) {
                        is.append("self ");
                        if (pe.isEq) {
                            is.append("= ");
                            // int colExpr = is.length();

                        } else {
                            is.append("\\in ");

                        }
                        addOneTokenToTLA(is.toString());
                        addLeftParen(pe.id.getOrigin());
                        addExprToTLA(pe.id);
                        addRightParen(pe.id.getOrigin());
                        // is.append(" -> \"");
                        is = new StringBuilder(" -> \"");
                        is.append(pe.iPC);
                        if (p == st.processes.size() - 1)
                            is.append("\"]");
                        else if (!boxUnderCASE)
                            is.append("\" []");
                        else
                            is.append("\"");
                    } // end if (useCase)
                    else {
                        is.append("\"").append(pe.iPC).append("\"]");
                    }
//                  tlacode.add(is.toString());
                    addOneTokenToTLA(is.toString());
                    endCurrentLineOfTLA();
                    is = new StringBuilder(NSpaces(colPC));
                    if (boxUnderCASE && p < st.processes.size() - 1)
                        is.append("[] ");
                }
            } else {
                is.append("/\\ pc = \"").append(st.iPC).append("\"");
//              tlacode.add(is.toString());
                addOneLineOfTLA(is.toString());
            }
        }
//        tlacode.add("");
        addOneLineOfTLA("");
    }

    /************************************/
    private void GenNext() {
        // It we are omitting pc and this is a uniprocess
        // algorithm, then the definition of Next has
        // already been added.
        if (parseAlgorithm.omitPC && !mp) {
            return;
        }
        final ArrayList<String> nextS = new ArrayList<>();
        StringBuilder sb = new StringBuilder();
        int max, col;

        if (!(pcalParams.NoDoneDisjunct || parseAlgorithm.omitStutteringWhenDone)) {
//          tlacode.add(sb.toString());
            sb.append("(* Allow infinite stuttering to prevent deadlock on termination. *)");
            addOneLineOfTLA(sb.toString());

            sb = new StringBuilder("Terminating == ");
            if (mp) {
                /************************************************************
                 * Bug fix by LL on 6 Sep 2007.  Added parentheses to        *
                 * change                                                    *
                 *                                                           *
                 * (*)    \A self \in ProcSet: ... /\ UNCHANGED vars         *
                 *                                                           *
                 * to                                                        *
                 *                                                           *
                 * (**)   (\A self \in ProcSet: ...)  /\ UNCHANGED vars      *
                 *                                                           *
                 * thus moving the UNCHANGED vars outside the quantifier.    *
                 * Since self does not appear in UNCHANGED vars, the two     *
                 * expressions are equivalent except when ProcSet is the     *
                 * empty set, in which case (*) equals TRUE and (**) equals  *
                 * UNCHANGED vars.                                           *
                 ************************************************************/
                /************************************************************
                 * Changed by MK on 19 Jun 2019 into a conjunct list         *
                 * after modifying GenNext to generate an explicit           *
                 * Terminating action before Next instead of the old         *
                 * implicit disjunct-to-prevent-deadlock-on-termination.     *
                 * This change also entailed to copy this if-block from the  *
                 * end of GenNext here modifying the original one to         *
                 * generate a call to Terminating.                           *
                 *                                                           *
                 * The rational for this change results from the recently    *
                 * introduced TLC profiler. The profiler reports the number  *
                 * of distinct successor states per action.                  *
                 * A terminating PlusCal algorithm has the implicit          *
                 * disjunct-to-prevent-deadlock-on-termination sub-action of *
                 * the Next next-state action.  Since the sub-action has no  *
                 * identifier, the profiler has to report Next as generating *
                 * no successor states (which is bogus).  With this change,  *
                 * the profiler will report the Terminating sub-action to    *
                 * generate no (distinct) successor states instead, which    *
                 * is perfectly correct and easy to understand.              *
                 ************************************************************/
                sb.append("/\\ \\A self \\in ProcSet: pc[self] = \"Done\"");
                addOneLineOfTLA(sb.toString());
                sb = new StringBuilder(NSpaces("Terminating == ".length()));
                sb.append("/\\ UNCHANGED vars");
            } else {
                sb.append("pc = \"Done\" /\\ UNCHANGED vars");
//              tlacode.add(sb.toString());
            }
            addOneLineOfTLA(sb.toString());
            addOneLineOfTLA("");
        }
        sb = new StringBuilder();

        // Steps with no parameter
        max = pcalParams.wrapColumn - ("Next == \\/ ".length());
        for (final String a : nextStep) {
            if (a.length() + " \\/ ".length() + sb.length() > max) {
                nextS.add(sb.toString());
                sb = new StringBuilder();
            }
            if (sb.length() > 0)
                sb.append(" \\/ ");
            sb.append(a);
        }
        if (sb.length() > 0)
            nextS.add(sb.toString());

        // Steps with (self) from ProcSet
        // These are procedures in a multiprocess algorithm
        final ArrayList<String> nextSS = new ArrayList<>();
        final String nextSSstart = "(\\E self \\in ProcSet: ";
        sb = new StringBuilder();
        max = pcalParams.wrapColumn - ("Next == \\/ (\\E self \\in ProcSet: \\/ ".length());
        if (mp && st.procs.size() > 0) {
            for (int i = 0; i < st.procs.size(); i++) {
                final PcalSymTab.ProcedureEntry p = st.procs.get(i);
                if ((p.name.length() + "(self) \\/ ".length() + sb.length()) > max) {
                    nextSS.add(sb.toString());
                    sb = new StringBuilder();
                }
                if (sb.length() > 0)
                    sb.append(" \\/ ");
                sb.append(p.name);
                sb.append("(self)");
            }
            if (sb.length() > 0)
                nextSS.add(sb + ")");
        }

        // Steps with (self) from a set
        // These are process sets
        final ArrayList<ArrayList<String>> nextSSP = new ArrayList<>(); // of ArrayList
        if (mp && st.processes.size() > 0)
            for (int i = 0; i < st.processes.size(); i++) {
                final PcalSymTab.ProcessEntry p = st.processes.get(i);
                if (p.isEq)
                    continue;
                final ArrayList<String> vec = new ArrayList<>();
                sb = new StringBuilder();
                sb.append("(\\E self \\in ");
                final ArrayList<String> sv = p.id.toStringVector();
                col = sb.length();
                sb.append(sv.get(0));
                for (int j = 1; j < sv.size(); j++) {
                    vec.add(sb.toString());
                    sb = new StringBuilder(NSpaces(col));
                    sb.append(sv.get(j));
                }
                sb.append(": ");
                sb.append(p.name);
                sb.append("(self))");
                vec.add(sb.toString());
                nextSSP.add(vec);
            }

        // assemble the line from the pieces
        sb = new StringBuilder("Next == ");
        col = sb.length() + 2;
        for (String next : nextS) {
            sb.append(next);
            addOneLineOfTLA(sb.toString());
//            tlacode.add(sb.toString());
            sb = new StringBuilder(NSpaces(col) + " \\/ ");
        }
        if (nextSS.size() > 0) {
            sb.append(nextSSstart);
            final int col2 = sb.length();
            if (nextSS.size() > 1)
                sb.append(" \\/ ");
            for (String ss : nextSS) {
                sb.append(ss);
                addOneLineOfTLA(sb.toString());
//                tlacode.add(sb.toString());
                sb = new StringBuilder(NSpaces(col2) + " \\/ ");
            }
            sb = new StringBuilder(NSpaces(col) + " \\/ ");
        }
        if (nextSSP.size() > 0)
            for (int i = 0; i < nextSSP.size(); i++) {
                final ArrayList<String> v = nextSSP.get(i);
                for (final String line : v) {
                    sb.append(line);
                    addOneLineOfTLA(sb.toString());
//                    tlacode.add(sb.toString());

                    // The following if case was added by LL on 22 Jan 2011
                    // to correct part 1 of bug bug_11_01_13.  This  bug occurs
                    // when an "\in" process's set is multi-line and that
                    // process's next-state action comes immediately after
                    // the Next == ..., with no " \/ " preceding it.  To fix the
                    // problem, we must add 6 fewer spaces to all lines after
                    // the first in that process's set than in other such sets.
                    if ((nextS.size() == 0) && (nextSS.size() == 0) && (i == 0)) {
                        sb = new StringBuilder(NSpaces(col - 2));
                    } else {
                        sb = new StringBuilder(NSpaces(col + 4));
                    }
                }
                sb = new StringBuilder(NSpaces(col) + " \\/ ");
            }
        if (!(pcalParams.NoDoneDisjunct || parseAlgorithm.omitStutteringWhenDone)) {
            addOneLineOfTLA(sb.append("Terminating").toString());
        }
        addOneLineOfTLA("");
//        tlacode.add("");
    }

    /*********************************************************/
    /* Gives the string to use when subscripting a variable. */

    /***********************************************************************
     * The spec can contain the following conjuncts                         *
     *                                                                      *
     * 1. Init /\ [][Next]_vars                                             *
     *    Always present                                                    *
     *                                                                      *
     * 2. WF_var(Next)                                                      *
     *    present if (a) The wfNext option is specified, or                 *
     *               (b) It is a uniprocess algorithm and one of the        *
     *                   options -wf, -sf, -termination is specified.       *
     *                                                                      *
     * 3. A sequence of process fairness formulas, containing               *
     *    one for each process for which there is a fairness condition.     *
     *                                                                      *
     * A process has                                                        *
     *    (a) a WF fairness condition iff                                   *
     *         (i) it is preceded by the keyword "fair" and the -nof        *
     *             option is not specified, or                              *
     *        (ii) the -wf option is specified.                             *
     *    (b) an SF fairness condition iff it is not preceded               *
     *        by the keyword "fair" and the -sf option is specified.        *
     *                                                                      *
     * Let P be a process specified by either                               *
     *                                                                      *
     *     [fair] process (P = exp) ...                                     *
     *     [fair] process (P \in exp) ...                                   *
     *                                                                      *
     * In the first case we say that P is a single process, in the second   *
     * that it is a process set.  Let                                       *
     *                                                                      *
     *   - p_1, ... , p_Np  be the labels of P modified by "+"              *
     *                                                                      *
     *   - m_1, ... , m_Nm  be the set of labels of P modified by "-"       *
     *                                                                      *
     *   - pSelf = IF P is a single process THEN "pname"                    *
     *                                      ELSE "self"                     *
     *                                                                      *
     *   - qSelf = IF /\ P is a single process                              *
     *                /\ pSelf a multi-line formula                         *
     *               THEN "self"                                            *
     *               ELSE pSelf                                             *
     *                                                                      *
     *   - pName = IF P is a single process THEN "P"                        *
     *                                      ELSE  "P(self)"                 *
     *                                                                      *
     * A process fairness formula is described by the following:            *
     *                                                                      *
     *    XF:                                                               *
     *       either WF or SF depending on P's fairness condition            *
     *                                                                      *
     *    prefix:                                                           *
     *       IF P is a single process                                       *
     *         THEN IF pSelf a multi-line formula                           *
     *                THEN "LET self = pSelf IN"                            *
     *                ELSE ""                                               *
     *         ELSE "\A self \in exp"                                       *
     *                                                                      *
     *    wfFormula:                                                        *
     *       "XF( (pc[qSelf] \notin {"m_1", ... , "m_Np"}) /\ pName )"      *
     *                                                                      *
     *    sfFormula:                                                        *
     *       if XF = SF                                                     *
     *         then null                                                    *
     *         else if P a single process                                   *
     *                then "SF_vars(p_1) /\ ... /\ SF_vars(p_Np)"           *
     *                else "SF_vars(p_1(self)) /\ ...                       *
     *                         /\ SF_vars(p_Np(self))"                      *
     *                                                                      *
     *    prcdFormulas:                                                     *
     *       A sequence consisting of the following two formulas for each   *
     *       procedure D called within P.  Let                              *
     *                                                                      *
     *         - pd_1, ... , pd_Npd  be the labels of D modified by "+"     *
     *         - md_1, ... , md_Nmd  be the labels of D modified by "-"     *
     *                                                                      *
     *       in the formulas:                                               *
     *                                                                      *
     *         wfFormula:                                                   *
     *           "XF( (pc[qSelf] \notin {"md_1", ... , "md_Nmd"})           *
     *                    /\ D(qSelf) )"                                    *
     *                                                                      *
     *         sfFormula:                                                   *
     *            if XF = SF                                                *
     *              then null                                               *
     *              else "SF_vars(pd_1(qSelf)) /\ ...                       *
     *                            /\ SF_vars(pd_Npd(qSelf))"                *
     *                                                                      *
     * -------                                                              *
     *                                                                      *
     * If there is at least one fairness formula, the definition of Spec    *
     * will be formatted in one of two ways.  If there is either a          *
     * WF_vars(Next) condition or a process fairness formula, then it may   *
     * be formatted as:                                                     *
     *                                                                      *
     *   Spec == Init /\ [][Next]_vars                                      *
     *                                                                      *
     * otherwise, it will be formatted as                                   *
     *                                                                      *
     *   Spec == /\ Init /\ [][Next]_vars                                   *
     *          [/\ WF_vars(Next)]                                          *
     *           /\ F_1                                                     *
     *           ...                                                        *
     *           /\ F_n                                                     *
     *                                                                      *
     * where each F_i is a process fairness formulas.                       *
     ***********************************************************************/
    private void GenSpec() {
        final String safetyFormula = "Init /\\ [][Next]_vars";

        if (pcalParams.FairnessOption.equals("nof")
                || (!mp && pcalParams.FairnessOption.equals(""))) {
            addOneLineOfTLA("Spec == " + safetyFormula);
            addOneLineOfTLA("");
            return;
        }
//System.out.println("foo |-> " + st.UseThis(PcalSymTab.PROCEDURE, "foo", ""));
//int to = st.FindProc("foo");
//PcalSymTab.ProcedureEntry pe =
//    (PcalSymTab.ProcedureEntry) st.procs.get(to);
//AST.Procedure procAst = pe.ast;

        // wfNextConj is either null or  " /\ WF_(Next)"
        String wfNextConj = null;
        if (pcalParams.FairnessOption.equals("wfNext")
                || pcalParams.FairAlgorithm
                || (!mp && (pcalParams.FairnessOption.equals("wf")
                || pcalParams.FairnessOption.equals("sf")))) {
            // If uniprocess then wf and sf are the same as wfNext
            wfNextConj = " /\\ WF_vars(Next)";
        }

        // Now compute procFairnessFormulas to equal the processes' fairness
        // formulas, which is never null but may have zero length.
        final ArrayList<ProcessFairness> procFairnessFormulas = new ArrayList<>();
        if (mp) {
            for (int i = 0; i < st.processes.size(); i++) {
                final PcalSymTab.ProcessEntry p = st.processes.get(i);
                final AST.Process pAst = p.ast;
                final int fairness = pAst.fairness;
                if (fairness != AST.UNFAIR_PROC) {
                    final String xf = (fairness == AST.WF_PROC) ? "WF" : "SF";

                    final ArrayList<String> pSelf = p.id.toStringVector();

                    // makeLetIn is true iff prefix will be LET self == ... IN
                    boolean makeLetIn = false;

                    String qSelf = "self";
                    if (p.isEq) {
                        if (pSelf.size() > 1) {
                            makeLetIn = true;
                        } else {
                            qSelf = pSelf.get(0);
                        }
                    }

                    final ArrayList<String> prefix = new ArrayList<>();
                    if (makeLetIn || !p.isEq) {
                        final int prefixSize = pSelf.size();
                        final String prefixBegin;
                        final String prefixEnd;
                        if (p.isEq) {
                            prefixBegin = "LET self == ";
                            prefixEnd = "";
                        } else {
                            prefixBegin = "\\A self \\in ";
                            prefixEnd = " : ";
                        }
                        final String padding = NSpaces(prefixBegin.length());
                        for (int j = 0; j < prefixSize; j++) {
                            String line = pSelf.get(j);
                            if (j == 0) {
                                line = prefixBegin + line;
                            } else {
                                line = padding + line;
                            }
                            if (j == prefixSize - 1) {
                                line = line + prefixEnd;
                            }
                            prefix.add(line);
                        }
                        if (makeLetIn) {
                            prefix.add("IN ");
                        }
                    } // end if (makeLetIn || !p.isEq)

                    final StringBuilder wfSB = new StringBuilder(xf + "_vars(");
                    if (pAst.minusLabels != null && pAst.minusLabels.size() > 0) {
                        wfSB.append("(pc[");
                        wfSB.append(qSelf);
                        if (pAst.minusLabels.size() == 1) {
                            wfSB.append("] # \"");
                            wfSB.append(pAst.minusLabels.get(0));
                            wfSB.append("\"");
                        } else {
                            wfSB.append("] \\notin {\"");
                            for (int j = 0; j < pAst.minusLabels.size(); j++) {
                                wfSB.append(pAst.minusLabels.get(j));
                                if (j == pAst.minusLabels.size() - 1) {
                                    wfSB.append("\"}");
                                } else {
                                    wfSB.append("\", \"");
                                }
                            }
                        }
                        wfSB.append(") /\\ ");
                    }

                    String pName = p.name;
                    if (!p.isEq) {
                        pName = p.name + "(self)";
                    }
                    wfSB.append(pName);
                    wfSB.append(")");

                    StringBuilder sfSB = null;
                    if (xf.equals("WF")
                            && (pAst.plusLabels != null)
                            && (pAst.plusLabels.size() != 0)) {
                        sfSB = new StringBuilder();
                        for (int j = 0; j < pAst.plusLabels.size(); j++) {
                            if (j != 0) {
                                sfSB.append(" /\\ ");
                            }
                            sfSB.append("SF_vars(");
                            sfSB.append(pAst.plusLabels.get(j));
                            if (!p.isEq) {
                                sfSB.append("(self)");
                            }
                            sfSB.append(")");
                        }
                    }

                    final ArrayList<FormulaPair> prcdFormulas = new ArrayList<>();
                    final ArrayList<String> procedures = pAst.proceduresCalled;
                    for (final String originalName : procedures) {
                        final String name = st.UseThis(PcalSymTab.PROCEDURE, originalName, "");
                        final int procedureIndex = st.FindProc(name);
                        final PcalSymTab.ProcedureEntry pe =
                                st.procs.get(procedureIndex);
                        final AST.Procedure prcAst = pe.ast;

                        final StringBuilder wfPrcSB = new StringBuilder(xf + "_vars(");
                        if (prcAst.minusLabels != null && prcAst.minusLabels.size() > 0) {
                            wfPrcSB.append("(pc[");
                            wfPrcSB.append(qSelf);
                            if (prcAst.minusLabels.size() == 1) {
                                wfPrcSB.append("] # \"");
                                wfPrcSB.append(prcAst.minusLabels.get(0));
                                wfPrcSB.append("\"");
                            } else {
                                wfPrcSB.append("] \\notin {\"");
                                for (int j = 0; j < prcAst.minusLabels.size(); j++) {
                                    wfPrcSB.append(prcAst.minusLabels.get(j));
                                    if (j == prcAst.minusLabels.size() - 1) {
                                        wfPrcSB.append("\"}");
                                    } else {
                                        wfPrcSB.append("\", \"");
                                    }
                                }
                            }
                            wfPrcSB.append(") /\\ ");
                        }

                        final String prcName = pe.name + "(" + qSelf + ")";
                        wfPrcSB.append(prcName);
                        wfPrcSB.append(")");

                        StringBuilder sfPrcSB = null;
                        if (xf.equals("WF")
                                && (prcAst.plusLabels != null)
                                && (prcAst.plusLabels.size() != 0)) {
                            sfPrcSB = new StringBuilder();
                            for (int j = 0; j < prcAst.plusLabels.size(); j++) {
                                if (j != 0) {
                                    sfPrcSB.append(" /\\ ");
                                }
                                sfPrcSB.append("SF_vars(");
                                sfPrcSB.append(prcAst.plusLabels.get(j));
                                sfPrcSB.append("(").append(qSelf).append(")");
                                sfPrcSB.append(")");
                            }
                        }
                        prcdFormulas.add(
                                new FormulaPair(
                                        wfPrcSB.toString(),
                                        (sfPrcSB == null) ? null : sfPrcSB.toString())
                        );
                    } // end construction of prcdFormulas

                    procFairnessFormulas.add(
                            new ProcessFairness(
                                    xf,
                                    prefix,
                                    wfSB.toString(),
                                    (sfSB == null) ? null : sfSB.toString(),
                                    prcdFormulas,
                                    pcalParams)
                    );
                } // end if (fairness != AST.UNFAIR_PROC)
            }
        } // ends construction of procFairnessFormulas

        if (wfNextConj == null && procFairnessFormulas.size() == 0) {
            addOneLineOfTLA("Spec == " + safetyFormula);
            addOneLineOfTLA("");
            return;
        }
        addOneLineOfTLA("Spec == /\\ " + safetyFormula);
//        tlacode.add("Spec == /\\ " + safetyFormula) ;
        final int indent = "Spec == /\\ ".length();

        if (wfNextConj != null) {
            addOneLineOfTLA("        /\\ WF_vars(Next)");
//            tlacode.add("        /\\ WF_vars(Next)");
        }
        for (ProcessFairness procFairnessFormula : procFairnessFormulas) {
            /*
             * The original code called format on the fairness formula, which can
             * create a string with \n characters embedded.  I've just split the
             * string into its individual lines and added them to tlacode one at a time.
             * However, the current and original code can both produce very long lines
             * that could be wrapped.  So if this change does make a difference, then
             * it would be better to completely rewrite the format method (which is only
             * called here).
             */
            final String str =
                    "        /\\ " +
                            procFairnessFormula.format(indent).toString();
            final String[] splitStr = str.split("\n");
            for (final String s : splitStr) {
                addOneLineOfTLA(s);
            }

        }
        addOneLineOfTLA("");
//        tlacode.add("");
    }

    /************************************/
    private void GenTermination() {
        // if we're omitting the pc or omitting the stuttering-when-done
        // clause of the Next action, then we shouldn't
        // generate the Termination definition.
        // Check of omitStutteringWhenDone added by LL on 30 Mar 2012.
        if (parseAlgorithm.omitPC || parseAlgorithm.omitStutteringWhenDone) {
            return;
        }
        final StringBuilder sb = new StringBuilder();
        sb.append("Termination == <>(");
        if (mp)
            sb.append("\\A self \\in ProcSet: pc[self]");
        else
            sb.append("pc");
        sb.append(" = \"Done\")");
        addOneLineOfTLA(sb.toString());
        addOneLineOfTLA("");
    }


    /***********************************************************/
    /* v is a sequence of SingleAssign. Return a vector of the */
    /* same SingleAssign, but sorted in terms of the lhs.var.  */

    /**********************************************************/
    private TLAExpr AddSubscriptsToExpr(final TLAExpr exprn, final TLAExpr sub, final Changed c) throws PcalTLAGenException {
        /*
         * For testing, throw a null pointer exception if the begin/end substitution
         * mapping vectors are not properly matching in the returned expression
         */
//        int[] depths = new int[1000];

        int parenDepth = 0;
        for (int i = 0; i < exprn.tokens.size(); i++) {
            final ArrayList<TLAToken> line = exprn.tokens.get(i);
            for (final TLAToken tok : line) {
                parenDepth = parenDepth + tok.getBeginSubst().size() - tok.getEndSubst().size();
                if (parenDepth < 0) {
                    throw new NullPointerException("argument: begin/end Subst depth negative");
                }
            }
//            depths[i] = parenDepth;
        }
        if (parenDepth != 0) {
            throw new NullPointerException("argument: Unmatched begin Subst");
        }
        /*   ------------------ end testing --------------------------*/

        /*
         * We now set stringVec to the sequence of identifiers that occur in exprn
         * for which we need to add a subscript or a prime.
         */
        final ArrayList<TLAExpr> exprVec = new ArrayList<>(); // the substituting exprs
        final ArrayList<String> stringVec = new ArrayList<>(); // the substituted ids
        final TLAExpr expr = exprn.cloneAndNormalize();  // the expression to be returned

        for (int i = 0; i < expr.tokens.size(); i++) {
            final ArrayList<TLAToken> tv = expr.tokens.get(i);
            /*****************************************************
             * Modified by LL on 30 Aug 2007.  The following      *
             * call to addTokenOffset was originally a call to    *
             * addToken.  See the comments for                    *
             * TLAExpr.addTokenOffset().                          *
             *****************************************************/
            /**********************************************************
             * Modified by LL on 31 Jan 2006 to comment out the call   *
             * of MakeExprPretty, since it totally screwed up the      *
             * formatting when substituting any string containing      *
             * spaces or multiple lines for a variable.                *
             **********************************************************/
            for (final TLAToken tok : tv) {
                final boolean prime = ((tok.type == TLAToken.IDENT) && c.IsChanged(tok.string));
                final boolean subr = (sub != null && (tok.type == TLAToken.ADDED || (mp && (tok.type == TLAToken.IDENT) && (IsProcedureVar(tok.string) || IsProcessSetVar(tok.string)))));
                if ((subr || prime) && !InVector(tok.string, stringVec)) {
                    stringVec.add(tok.string);
                    TLAExpr exp = new TLAExpr();
                    exp.addLine();
                    /*
                     * 15 Dec 2011:  The following code added to replace the
                     *
                     *    exp.addToken(new TLAToken(tok.string, 0, TLAToken.IDENT));
                     *
                     * that is commented out.  Note that this change can add a token with
                     * type ADDED rather than IDENT.  I don't think this matters.
                     */
                    final TLAToken newTok = tok.Clone();
                    /*
                     * The new token should inherit nothing from the baggage of tok, whose
                     * only function is to provide the name
                     */
                    newTok.setBeginSubst(new ArrayList<>(2));
                    newTok.setEndSubst(new ArrayList<>(2));
                    newTok.source = null;
                    newTok.column = 0;
                    exp.addToken(newTok);
                    // exp.addToken(new TLAToken(tok.string, 0, TLAToken.IDENT));
                    if (prime) {
                        /*****************************************************
                         * Modified by LL on 30 Aug 2007.  The following      *
                         * call to addTokenOffset was originally a call to    *
                         * addToken.  See the comments for                    *
                         * TLAExpr.addTokenOffset().                          *
                         *****************************************************/
                        final TLAToken primeTok = new TLAToken("'", 0, TLAToken.BUILTIN, true);
                        // The following stuff added by LL in Dec 2011 is bogus.  The
                        // token tok is just the first one of many in the exprn with
                        // the same name for which we want to substitute.  The only
                        // useful data in the token tok is its string.
                        exp.addTokenOffset(primeTok, 0);
                    }
                    if (subr) {
                        final TLAExpr subexp = sub.cloneAndNormalize();

                        /*
                         * We now add the end of the origin of tok to beginSubst
                         * of the first token of subexp and to endSubst of the
                         * last token of subexp.  This indicates that PCal code
                         * corresponding to a region of the TLA+ translation that
                         * includes part of the added subscript and part of the
                         * original expression is a portion of the source of
                         * exprn.
                         */
                        // This is bogus, because we are adding the location of where
                        // the identifier first occurs in exprn to the substitution
                        // vectors of the expression that's going to be substituted in
                        // all instances.
                        /*
                         * However, we do have to move the token's beginSubst and endSubst vectors
                         * to the first and lasts token of the subscript.  Since the
                         * resulting Parens that they generate should be outside
                         * the ones generated by the endSubst vectors of the expression,
                         * we have to add them before that expression's Subst vectors.
                         *
                         * No, no!  This tok is just giving us the name of the tok that
                         * we're going to be substituting for in the expression.  It is not
                         * necessarily the one that we're going to substitute for.
                         */
                        exp.normalize();
                        try {
                            subexp.prepend(exp, 0);
                        } catch (final TLAExprException e) {
                            throw new PcalTLAGenException(e.getMessage());
                        }
                        exp = subexp;
                    }
                    /**********************************************************
                     * Modified by LL on 31 Jan 2006 to comment out the call   *
                     * of MakeExprPretty, since it totally screwed up the      *
                     * formatting when substituting any string containing      *
                     * spaces or multiple lines for a variable.                *
                     **********************************************************/
                    // MakeExprPretty(exp);
                    exprVec.add(exp);
                }
            }
        }
        if (exprVec.size() > 0)
            try {
                expr.substituteForAll(exprVec, stringVec, false);
            } catch (final TLAExprException e) {
                throw new PcalTLAGenException(e.getMessage());
            }
        /*
         * For testing, throw a null pointer exception if the begin/end substitution
         * mapping vectors are not properly matching in the returned expression
         */
//        depths = new int[1000];

        for (int i = 0; i < expr.tokens.size(); i++) {
            final ArrayList<TLAToken> line = expr.tokens.get(i);
            for (final TLAToken tok : line) {
                parenDepth = parenDepth + tok.getBeginSubst().size() - tok.getEndSubst().size();
                if (parenDepth < 0) {
                    throw new NullPointerException("result: begin/end Subst depth negative");
                }
            }
//            depths[i] = parenDepth;
        }
        if (parenDepth != 0) {
            throw new NullPointerException("result: Unmatched begin/subst");
        }
        /*   ------------------ end testing --------------------------*/
        return expr;
    }

    /*********************************************************/
    // LL comment: it appears that PcalTLAGen.self is the
    // current process id if this is being called in the context
    // of a process declared with `process (P = id)'.
    private TLAExpr Self(final String context) {
        TLAExpr s = null;
        if (mp) {
            if (context.equals("procedure"))
                s = selfAsExpr();
            else
                s = self;
        }
        return s;
    }

    /*
     * The following methods are used to add code to tlacode and add the
     * appropriate objects to mappingVector
     */

    /**
     * Adds one token to tlacodeNextLine, and adds the appropriate
     * Begin/EndTLAToken objects to mappingVectorNextLine.  The
     * ...TLAToken objects mark a region that excludes beginning and
     * ending space characters of token--unless the token has
     * only space characters.
     */
    private void addOneTokenToTLA(final String token) {
        String trimmedToken = token.trim();

        int numberOfLeftTrimmedTokens =
                (trimmedToken.length() == 0) ? -1 :
                        token.indexOf(trimmedToken.charAt(0));

        /**
         * Handle a token of only space characters. 
         */
        if (numberOfLeftTrimmedTokens == -1) {
            numberOfLeftTrimmedTokens = 0;
            trimmedToken = token;
        }

        final int objBegin = tlacodeNextLine.length() + numberOfLeftTrimmedTokens;
        mappingVectorNextLine.add(new MappingObject.BeginTLAToken(objBegin));
        mappingVectorNextLine.add(new MappingObject.EndTLAToken(objBegin + trimmedToken.length()));
        tlacodeNextLine = tlacodeNextLine + token;
    }

    /**
     * If region is non-null, then adds string str to the TLA output
     * as a SourceToken object with that region.  Otherwise, it adds
     * it as a TLAToken, with Begin/EndTLAToken objects.
     */
    private void addOneSourceTokenToTLA(final String str, final Region region) {
        if (region == null) {
            addOneTokenToTLA(str);
            return;
        }

        final int beginCol = tlacodeNextLine.length();
        final int endCol = beginCol + str.length();
        mappingVectorNextLine.add(
                new MappingObject.SourceToken(beginCol, endCol, region));
        tlacodeNextLine = tlacodeNextLine + str;
    }

    /**
     * Adds a complete line of TLA "code" that does not correspond to
     * any PlusCal code.  Adds Begin/EndTLAToken objects to the mapping
     * iff the line does not equal "".
     */
    private void addOneLineOfTLA(final String line) {
// temporarily commented out.
        if (tlacode.size() != mappingVector.size()) {
            PcalDebug.ReportBug("tlacode and mappingVector have different lengths");
        }
// The following added during testing.
        endCurrentLineOfTLA();
        if (line.length() == 0) {
            mappingVector.add(new ArrayList<MappingObject>(2));
            tlacode.add("");
            return;
        }
        addOneTokenToTLA(line);
        endCurrentLineOfTLA();
    }

    /**
     * If tlacodeNextLine does not equal "", then add it to tlacode
     * and add mappingVectorNextLine to mappingVector.  If it does equal "",
     * don't add any lines, but add any potentially legal leftovers in
     * mappingVectorNextLine to the previous line.
     */
    private void endCurrentLineOfTLA() {
        if (tlacodeNextLine.length() != 0) {
            tlacode.add(tlacodeNextLine);
            mappingVector.add(mappingVectorNextLine);
            tlacodeNextLine = "";
            mappingVectorNextLine = new ArrayList<>();
        } else {
            if (mappingVectorNextLine.size() != 0) {
                /*
                 * There's something to go in the mappingVector that doesn't
                 * accompany any text.  It should be one or more RightParen or
                 * LeftParen objects, (or perhaps, eventually a Break), in which
                 * case they should be put at the end of the previous mappingVector
                 * line.  Anything else is a mistake.
                 */
                final ArrayList<MappingObject> lastLine = (ArrayList<MappingObject>) mappingVector.get(mappingVector.size() - 1);
                for (int i = 0; i < mappingVectorNextLine.size(); i++) {
                    final MappingObject obj = mappingVectorNextLine.get(i);
                    if (obj.getType() == MappingObject.RIGHT_PAREN ||
                            obj.getType() == MappingObject.LEFT_PAREN ||
                            obj.getType() == MappingObject.BREAK) {
                        lastLine.add(obj);
                    } else {
                        PcalDebug.ReportBug("PcalTLAGen.endCurrentLineOfTLA found problem.");
                    }
                    mappingVectorNextLine = new ArrayList<>();
                }
            }
        }
    }

    /**
     * Adds the expression to tlacode / tlacodeNextLine and its
     * mapping to mappingVector / mappingVectorNextLine.  It adds
     * no space before the expression and leaves the last line of the
     * expression (which could be its first line) at the end of
     * tlacodeNextLine.
     */
    private void addExprToTLA(final TLAExpr expr) {
        final ArrayList<String> sv = expr.toStringVector();
        final ArrayList<ArrayList<MappingObject>> exprMapping = expr.toMappingVector();
        final int indent = tlacodeNextLine.length();
        int nextLine = 0;
        if (indent != 0) {
            /*
             * Need to combine first line of expr with
             * tlacodeNextLine.
             */
            MappingObject.shiftMappingVector(exprMapping, indent);
            tlacodeNextLine = tlacodeNextLine + sv.get(0);
            mappingVectorNextLine.addAll(exprMapping.get(0));
            nextLine = 1;
            if (sv.size() > 1) {
                endCurrentLineOfTLA();
            }
        }
        if (sv.size() > 1) {
            final String spaces = NSpaces(indent);
            while (nextLine < sv.size() - 1) {
                tlacode.add(spaces + sv.get(nextLine));
                mappingVector.add(exprMapping.get(nextLine));
                nextLine++;
            }
            tlacodeNextLine = spaces + sv.get(nextLine);
            mappingVectorNextLine = exprMapping.get(nextLine);
        } else if (indent == 0) {
            /*
             * If indent != 0, then we've already added the one-line expression.
             */
            tlacodeNextLine = tlacodeNextLine + sv.get(0);
            mappingVectorNextLine.addAll(exprMapping.get(0));
        }
    }

    /**
     * Subroutine of GenInit that adds to the TLA translation the Init conjunct
     * corresponding to the VarDecl decl for a global variable and, in a uniprocess
     * algorithm for a procedure or process variable It is called with the
     * StringBuilder `is' containing the text that precedes the "/\" of the
     * conjunct, which will be "Init == " or just spaces.
     */
    private void addVarDeclToTLA(final VarDecl decl, StringBuilder is) {
        is.append("/\\ ");
        addOneTokenToTLA(is.toString());
        addLeftParen(decl.getOrigin());
//        is.append(decl.var);
        is = new StringBuilder(decl.var);
        if (decl.isEq)
            is.append(" = ");
        else
            is.append(" \\in ");
        addOneTokenToTLA(is.toString());
        addLeftParen(decl.val.getOrigin());
        final boolean needsParens = NeedsParentheses(decl.val.toStringVector());
        if (needsParens) {
            addOneTokenToTLA("(");
        }
        addExprToTLA(decl.val);
        if (needsParens) {
            addOneTokenToTLA(")");
        }
        addRightParen(decl.val.getOrigin());
        addRightParen(decl.getOrigin());
        endCurrentLineOfTLA();
    }

    /**
     * Adds a MappingObject.LeftParen object to the mapping vector
     * for the beginning of the Region region, if it's not null.
     */
    private void addLeftParen(final Region region) {
        if (region != null) {
            mappingVectorNextLine.add(
                    new MappingObject.LeftParen(region.getBegin()));
        }
    }

    /**
     * Adds a MappingObject.LeftParen object to the mapping vector
     * for the beginning of the Region region, if it's not null.
     */
    private void addRightParen(final Region region) {
        if (region != null) {
            mappingVectorNextLine.add(
                    new MappingObject.RightParen(region.getEnd()));
        }
    }

    /**
     * Like addLeftParen(ast.getOrigin()), except that it uses
     * loc the location if it is not null.  It is called by
     * GenLabeledStmt and ast.getOrigin() should never be null.
     * However, if it is, then we don't add a Paren; this insures
     * that the matching calls of addLeftParenV and addRightParenV
     * both either do or don't add a Paren.
     */
    private void addLeftParenV(final AST ast, final PCalLocation loc) {
        if (ast.getOrigin() == null) {
            return;
        }
        if (loc != null) {
            mappingVectorNextLine.add(
                    new MappingObject.LeftParen(loc));
        } else {
            addLeftParen(ast.getOrigin());
        }
    }

    /**
     * Like addRightParen(ast.getOrigin()), except that it uses
     * loc as the location if it is not null.  It is called by
     * GenLabeledStmt and ast.getOrigin() should never be null.
     * However, if it is, then we don't add a Paren; this insures
     * that the matching calls of addLeftParenV and addRightParenV
     * both either do or don't add a Paren.
     */
    private void addRightParenV(final AST ast, final PCalLocation loc) {
        if (ast.getOrigin() == null) {
            return;
        }
        if (loc != null) {
            mappingVectorNextLine.add(
                    new MappingObject.RightParen(loc));
        } else {
            addRightParen(ast.getOrigin());
        }
    }
    /* -------------------------------------------------------------------------- */
    /*
     * The following methods and classes of objects are used in GenSpec().
     * See the comments preceding that method above.
     */

    /**
     * A FormulaPair should never have wf = null, but might have sf = null.
     */
    public static class FormulaPair {
        public final String wf;
        public final String sf;

        public FormulaPair(final String wfVal, final String sfVal) {
            this.wf = wfVal;
            this.sf = sfVal;
        }

        /**
         * The string  wf /\ sf , or just wf if sf is null.
         */
        public String singleLine() {
            if (sf == null) {
                return wf;
            }
            return wf + " /\\ " + sf;
        }

        /**
         * The width of the singleLine representation of the
         * conjunction of the formlas.
         */
        public int singleLineWidth() {
            if (sf == null) {
                return wf.length();
            }
            return wf.length() + " /\\ ".length() + sf.length();
        }

        /**
         * The representation of the conjunction of the formulas with
         * prefix /\s, where the first /\ appears in column col (Java
         * numbering), witout any ending "\n"
         */
        public String multiLine(final int col) {
            final String val = "/\\ " + wf;
            if (sf == null) {
                return val;
            }
            return val + "\n" + NSpaces(col) + "/\\ " + sf;
        }
    }

    /**
     * Describes a process fairness formula, as described in the comments
     * preceding the  GetSpec() method above.
     *
     * @author lamport
     */
    public static class ProcessFairness {
        public final String xf; // either "WF" or "SF"
        public final ArrayList<String> prefix;
        public final ArrayList<FormulaPair> prcdFormulas; // fairness conditions for the procedure
        private final PcalParams pcalParams;
        // StringVector either "\A self \in exp : " or
        // "LET self == exp \n IN " (note the ending space) or ""
        public FormulaPair bodyFormulas; // fairness conditions for the proc's body

        /**
         * The constructor
         *
         * @param bodyWF : can be null if bodySF is also null
         * @param bodySF : can be null
         */
        public ProcessFairness(final String xfVal, final ArrayList<String> prefixVal, final String bodyWF,
                               final String bodySF, final ArrayList<FormulaPair> prcdVal, PcalParams pcalParams) {
            this.pcalParams = pcalParams;
            xf = xfVal;
            prefix = prefixVal;
            bodyFormulas = null;
            if (bodyWF != null) {
                bodyFormulas = new FormulaPair(bodyWF, bodySF);
            }
            prcdFormulas = prcdVal;
        }

        /**
         * The width of the fairness formula written as a "single-line"
         * formula.  Single-line means that it is not written as a
         * conjunction list (with a leading /\).  It will actually
         * occupy multiple lines if prefix is a multi-line formula.
         */
        public int singleLineWidth() {
            // Set maxPrefixWidth to length of longest non-final
            // line of prefix, width to lenght of final line
            int maxPrefixWidth = 0;
            int width = 0;
            if (prefix != null && !prefix.isEmpty()) {
                for (int i = 0; i < prefix.size() - 1; i++) {
                    final String line = prefix.get(i);
                    if (line.length() > maxPrefixWidth) {
                        maxPrefixWidth = line.length();
                    }
                    final String lastLine = prefix.get(prefix.size() - 1);
                    width = lastLine.length();
                }
            }
            width = width + bodyFormulas.wf.length();
            if (bodyFormulas.sf != null) {
                width = width + bodyFormulas.sf.length();
            }
            if (prcdFormulas != null) {
                for (FormulaPair prcdFormula : prcdFormulas) {
                    width = width + prcdFormula.singleLineWidth();
                }
            }
            return Math.max(maxPrefixWidth, width);
        }

        /**
         * Returns the prefix as a StringBuilder, assuming it starts
         * in column col.  That is, all but the first line is indented
         * with col spaces, and all but the last line is ended with
         * a \n .
         */
        private StringBuilder prefixAsStringBuilder(final int col) {
            final StringBuilder val = new StringBuilder();
            if (prefix != null && !prefix.isEmpty()) {
                for (int i = 0; i < prefix.size(); i++) {
                    final String line = prefix.get(i);
                    if (i != 0) {
                        val.append(NSpaces(col));
                    }
                    val.append(line);
                    if (i != prefix.size() - 1) {
                        val.append("\n");
                    }
                }
            }
            return val;
        }

        /**
         * The process fairness condition written as a single-line formula,
         * starting in column col.
         */
        public StringBuilder singleLine(final int col) {
            final StringBuilder val = prefixAsStringBuilder(col);
            val.append(bodyFormulas.wf);
            if (bodyFormulas.sf != null) {
                val.append(" /\\ ");
                val.append(bodyFormulas.sf);
            }
            if (prcdFormulas != null) {
                for (FormulaPair prcdFormula : prcdFormulas) {
                    val.append(" /\\ ");
                    val.append(prcdFormula.singleLine());
                }
            }
            return val;
        }

        /**
         * Returns true iff format(col) should return a single-line version
         * of the formula.
         */
        private boolean fitsAsSingleLine(final int col) {
            return (col + singleLineWidth() <= pcalParams.wrapColumn)
                    || (bodyFormulas.sf == null
                    && (prcdFormulas == null || prcdFormulas.isEmpty()));
        }

        /**
         * The process fairness condition written as a formula that
         * begins in column col (Java numbering) and ends with "\n".
         * It is formatted to try to extend no further than column
         * PcalTLAGen.wrapColumn, but no individual formula is split
         * across lines.
         */
        public StringBuilder format(final int col) {
            /*
             * Return the single-line form if either it fits on the
             * line or if it consists of only the wf formula (so it can't
             * be put on multiple lines).
             */
            if (fitsAsSingleLine(col)) {
                return this.singleLine(col);
            }
            final StringBuilder val = prefixAsStringBuilder(col);
            int prefixWidth = 0;
            if (prefix != null && !prefix.isEmpty()) {
                prefixWidth = prefix.get(prefix.size() - 1).length();
            }
            final int curCol = col + prefixWidth;
            String line = this.bodyFormulas.singleLine();
            if (curCol + line.length() + 3 <= pcalParams.wrapColumn) {
                val.append("/\\ ").append(line);
            } else {
                val.append(this.bodyFormulas.multiLine(curCol));
            }
            if (prcdFormulas == null) {
                return val;
            }
            for (int i = 0; i < this.prcdFormulas.size(); i++) {
                final FormulaPair form = this.prcdFormulas.get(i);
                line = form.singleLine();
                // On 2 Apr 2013, LL discovered the following totally bizarre
                // line of code, which inserted copies of "THIS_EXTRA_SPACE_INSERTED" into
                // the translation, which of course then didn't parse.  Apparently some
                // change was made and never tested.  The conjuncts being inserted here
                // seem to be the fairness formulas for procedures in a fair process.
                //
                //val.append("\nTHIS_EXTRA_SPACE_INSERTED");

                // One experiment seems to indicate that the following statement is needed
                // to put the first of the procedures' liveness formulas where it belongs.
                // However, I don't understand the code so I have no idea what actually
                // should be done.  LL 2 Apr 2013
                //
                if (i == 0) {
                    val.append("\n");
                }
                val.append(NSpaces(curCol));
                if (curCol + line.length() + 3 <= pcalParams.wrapColumn) {
                    val.append("/\\ ").append(line).append("\n");
                } else {
                    val.append(form.multiLine(curCol));
                }
            }
            return val;
        }


    }
}
