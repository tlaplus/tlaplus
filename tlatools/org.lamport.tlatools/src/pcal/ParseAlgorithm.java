// macro substitution isn't getting the line/col numbers right
// for assignment statements.

/***************************************************************************
 * CLASS ParseAlgorithm                                                     *
 *                                                                          *
 * The following bug should have been fixed by the addition of the          *
 * Uncomment method by LL on 18 Feb 2006.                                   *
 *                                                                          *
 * BUG: The code for reporting the location of an error has the following   *
 * problem.  If the token where the error occurs is preceded by a comment,  *
 * then the position reported is that of the beginning of the comment       *
 * rather than that of the token.  Search for "BUG" (upper-case) to find    *
 * the source of this bug and how it might be fixed.                        *
 *                                -----------                               *
 *                                                                          *
 * The main method is GetAlgorithm, which constructs the AST node for the   *
 * complete algorithm.                                                      *
 *                                                                          *
 *                                                                          *
 * This class has been extensively rewritten by LL in March 2006 to         *
 * implement the added feature of allowing the translator to insert         *
 * missing labels.                                                          *
 *                                                                          *
 * GetAlgorithm begins by using a recursive-descent parser to construct a   *
 * preliminary AST.  A recursive-descent parser for the actual +CAL         *
 * grammar, as defined by the operator IsAlgorithm of PlusCal.tla, would    *
 * be quite complicated because it would have to look far ahead before      *
 * deciding what kind of node it is processing.  For example, it might      *
 * have to look far down an "if" statement to determine if an <If> is a     *
 * <FinalIf> or a <LabelIf>.  Those distinctions are present in the         *
 * grammar to make sure that labels don't appear where they shouldn't and   *
 * do appear where they should.                                             *
 *                                                                          *
 * Any kind of conventional parsing is out of the question if the           *
 * translator has to add missing labels.  Therefore, the GetAlgorithm       *
 * procedure performs a recursive-descent parsing only down to the level    *
 * of a sequence of <LabeledStmt> objects in the real grammar.              *
 * It parses such a sequence in three steps.                                *
 *                                                                          *
 *  - It calls the procedure GetStmtSeq to build a very simplified AST      *
 *    based on the simplified grammar in the Appendix of "A +CAL User's     *
 *    Manual".  The nodes of the AST are the obvious ones defined in        *
 *    AST.java, where the AST object represents  <Stmt> object.  However,   *
 *    an "if" statement is represented by a LabelIf object with empty       *
 *    labThen and labElse fields (equal to an empty ArrayList), and an         *
 *    "either" statement is represented by a LabelEither object whose       *
 *    clauses contain empty labOr fields.  The AST node's lbl field         *
 *    holds the label (the absence of a label represented by                *
 *    a lbl field equal to the empty string "").  The only difference       *
 *    from the simple grammar is that a <Call> followed by an unlabeled     *
 *    <Return> or <Goto> is converted into a single AST.CallReturn or       *
 *    AST.CallGoto object, respectively.  This pass does not produce any    *
 *    AST.If or AST.Either objects, and any AST.While object it produces    *
 *    has an empty labDo field.                                             *
 *                                                                          *
 *  - It calls the procedure AddLabelsToStmtSeq to check for missing        *
 *    labels and either add them or report an error if it finds one,        *
 *    depending on the value of PcalParams.AddLabels.                       *
 *                                                                          *
 *  - It calls the procedure MakeLabeledStmtSeq to turn the sequence        *
 *    of <Stmt> nodes into a sequence of <LabeledStmt> nodes.  This         *
 *    also turns LabelIf and LabelEither objects of If and Either objects   *
 *    when appropriate                                                      *
 *                                                                          *
 * GetStmtSeq is called on all commands before AddLabelsToStmtSeq is        *
 * called on any of them.  Hence, it's possible to find all the labels in   *
 * the algorithm before having to create any new ones.                      *
 *                                                                          *
 *                       ---------------                                    *
 *                                                                          *
 * SUBSTITUTION                                                             *
 * ------------                                                             *
 * The basic substitution operation is to substitute an expression expr     *
 * for an identifier id in a statement.  There are two places in which      *
 * this substitution can occur: in an expression and for the variable of    *
 * a <SingleAssign> object.  These two substitutions are performed as       *
 * follows:                                                                 *
 *                                                                          *
 *    In an expression, all occurrences of id in the expression that do not *
 *    represent record field names are replaced by expr.  If neither expr   *
 *    nor the expression being substituted in consist of a single token,    *
 *    then expr is enclosed in parentheses in the substitution.             *
 *                                                                          *
 *    In substituting for the variable id in a single assignment, the       *
 *    first token of expr becomes the assignment variable, any remaining    *
 *    tokens of expr are prepended to the subscript.  E.g., substituting    *
 *    "a[1]" for "x" in the assignment  "x[y] := 1" yields the assignment   *
 *    "a[1][y] := 1".                                                       *
 *                                                                          *
 * This class provides the method                                           *
 *                                                                          *
 *    SubstituteInLabeledStmtSeq(stmts, args, params)                       *
 *                                                                          *
 * where                                                                    *
 *                                                                          *
 *    stmts  : A vector of AST.LabeledStmt objects.                         *
 *    args   : A vector of TLAExpr objects.                                 *
 *    params : A vector of String objects.                                  *
 *                                                                          *
 * The vector stmts is the sequence of LabeledStmt object in which the      *
 * substitution is to be done.  Each expression in args is substituted for  *
 * the identifier whose string is the corresponding element of params.      *
 * More precisely, each LabeledStmt object in stmts is replaced by a clone  *
 * of the original object in which the substitution is performed.           *
 ***************************************************************************/
package pcal;

import pcal.AST.Macro;
import pcal.AST.PVarDecl;
import pcal.AST.Procedure;
import pcal.AST.VarDecl;
import pcal.exception.ParseAlgorithmException;
import pcal.exception.TLAExprException;
import pcal.exception.TokenizerException;
import pcal.exception.UnrecoverableException;
import tla2tex.Debug;

import java.util.ArrayList;
import java.util.Hashtable;


public class ParseAlgorithm {
    public final PcalParams pcalParams;
    public final Tokenize tokenizer;
    public final String[] LAT = new String[10];
    /**********************************************************************
     * LAT[0], LAT[1], ...  , LAT[LATsize-1] contain tokens that have      *
     * been read from the algorithm with Tokenize.GetAlgorithmToken but    *
     * not yet processed.  It should never contain a token that's part of  *
     * an Expr.                                                            *
     **********************************************************************/

    public final int[] curTokCol = new int[10];
    public final int[] curTokLine = new int[10];
    /**********************************************************************
     * The charReader argument to the Parse method is put here so other    *
     * methods can access it.  This makes the class totally thread unsafe. *
     **********************************************************************/

    public String currentProcedure;
    /**********************************************************************
     * This is set by GetProcedure to the procedure's name before the      *
     * procedure body is parsed, and is reset to null afterwards.  Hence,  *
     * its value is null unless in the middle of parsing a procedure.      *
     * (Its value is used to check for a <Return> not in a procedure       *
     * body.)                                                              *
     **********************************************************************/

    /*
     * plusLabels and minusLabels are vectors of labels that appear within the
     * current process or procedure with + or - modifiers, respectively.
     * Added in Version 1.5.
     */
    public ArrayList<String> plusLabels;
    public ArrayList<String> minusLabels;
    /**
     * proceduresCalled is the vector of distinct names of
     * procedures called within the current process or procedure.
     */

    /*
     * The following are added to record whether or not the translation needs
     * (a) the variable pc and (b) the stuttering-when-done disjunct of Next.
     * The gotoDoneUsed flag is set true if the algorithm contains a `goto Done'
     * statement, in which case omitPC and omitStutteringWhenDone should be
     * set false.  The gotoUsed flag is set true if any goto is used, in which
     * case omitPC should be set false.  The gotoUsed and gotoDoneUsed flags
     * are set by the getGoto method; the omitPC and  omitStutteringWhenDone
     * flags are set by getAlgorithm, though most of the work is done by the
     * checkBody method.
     *
     * In a more elegant implementation, this information would
     * be saved as part of the AST object for the complete algorithm.  However,
     * since omitting these things is an addition made for Version 1.5, it's
     * easier to modify the "code" generation by having the information
     * available in global variables.
     */
    public boolean gotoUsed;
    public boolean gotoDoneUsed;
    /**********************************************************************
     * Set true if any variable has a default initialization.              *
     * (Added by LL on 22 Aug 2007.)                                       *
     **********************************************************************/
    public boolean omitPC;
    public boolean omitStutteringWhenDone;
    public ArrayList<String> proceduresCalled;
    /**********************************************************************
     * The number to be appended to PcalParams.LabelRoot to form the next  *
     * label to be added.                                                  *
     **********************************************************************/
    public boolean hasDefaultInitialization;
    /***************************************************************************
     *                           CONSTRUCTING THE AST                           *
     *                                                                          *
     * For most nonterminals <NonTerm> in the simple grammar, there is a        *
     * method GetNonTerm() that processes the input from the current position   *
     * and returns an AST.NonTerm object.  There may also be a method           *
     * GetNonTermSeq() that parses a sequence of <NonTerm> nodes and returns a  *
     * vector of AST.NonTerm objects.                                           *
     ***************************************************************************/

    public boolean hasLabel;
    /**********************************************************************
     * This variable is set to true by GetStmtSeq whenever a label is      *
     * found.  It is used in deciding whether or not to add labels to a    *
     * uniprocess algorithm.                                               *
     **********************************************************************/

    public Hashtable<String, String> allLabels;
    /**********************************************************************
     * Set by GetStmtSeq to a table of String objects containing all the   *
     * algorithm's (user-typed) labels.  The strings are the keys, the     *
     * value of all entries is 0.  The value of                            *
     * allLabels.containsKey("foo") is true iff "foo" is a label of the    *
     * algorithm.                                                          *
     **********************************************************************/

    public int nextLabelNum;
    /************************************************************************
     * As described above, the method AddLabelsToStmtSeq determines where    *
     * labels are to be added.  Added labels are reported as a bug if the    *
     * user doesn't want them, and are printed in the terminal output if     *
     * she does and has specified the -reportLabels option.  The i-th entry  *
     * of the vectors addedLabels and addedLabelsLocs records the name of    *
     * the i-th added label and the location of the statement to which it    *
     * was added.                                                            *
     ************************************************************************/
    public ArrayList<String> addedLabels;
    public ArrayList<String> addedLabelsLocs;
    /**********************************************************************
     * Is set to the sequence of procedures.  It's easier making this a    *
     * global variable than passing it as a parameter.                     *
     **********************************************************************/
    public ArrayList<Procedure> procedures;
    /**********************************************************************
     * One of these booleans will be set true when we discover which       *
     * syntax is being used.
     **********************************************************************/
    public boolean pSyntax;
    public boolean cSyntax;
    public boolean inGetMacro = false;
    /**
     * This variable is used by GetLabel to return the location of the label
     * for use in computing the origin field of the AST object in which the
     * label appears.  If GetLabel returns a string other than "", then
     * getLabelLocation is the location at the beginning of the label.
     */
    public PCalLocation getLabelLocation;
    public int LATsize = 0;
    /**********************************************************************
     * curTokCol[i] and curTokLine[i] are the result of calling            *
     * PcalCharReader.getLineNumber() and                                  *
     * PcalCharReader.getColumnNumber() when the reader was positioned     *
     * just before the token in LAT[i].                                    *
     **********************************************************************/

    public int lastTokCol;
    public int lastTokLine;
    private PcalCharReader charReader;
    /**
     * The last string returned by GetAlgToken or gobbled by Gobble...
     */
    private String lastTokString;

    public ParseAlgorithm(PcalParams pcalParams) {

        this.pcalParams = pcalParams;
        this.tokenizer = new Tokenize();
    }

    /**********************************************************************
     * This performs the initialization needed by the various Get...       *
     * methods, including setting charReader.  It is called only by        *
     * GetAlgorithm.  It's been made into a separate method for debugging, *
     * so the various Get methods can be tested without calling            *
     * GetAlgorithm.                                                       *
     **********************************************************************/
    public void Init(final PcalCharReader charR) {
        // initialization moved
        addedLabels = new ArrayList<>();
        addedLabelsLocs = new ArrayList<>();
        nextLabelNum = 1;
        charReader = charR;
        allLabels = new Hashtable<>();
        hasLabel = false;
        hasDefaultInitialization = false;
        currentProcedure = null;
        procedures = new ArrayList<>();

        pSyntax = false;
        cSyntax = false;

        // The following initializations are redundant, but a little redundancy
        // never hurt.
        // The following initializations are redundant, but a little redundancy
        // never hurt.
        plusLabels = new ArrayList<>(0);
        minusLabels = new ArrayList<>(0);
        proceduresCalled = new ArrayList<>(0);

        gotoUsed = false;
        gotoDoneUsed = false;
        // The following two field settings are used because the checks
        // for omitting these things are done in the checkBody method
        // and in getAlgorithm by making them false if they can't be
        // omitted.
        omitPC = true;
        omitStutteringWhenDone = true;
        // if the user has specified an earlier version than 1.5, then
        // don't omit the pc variable or stuttering-when-done clause.
        if (pcalParams.inputVersionNumber < PcalParams.VersionToNumber("1.5")) {
            omitPC = false;
            omitStutteringWhenDone = false;
        }

        /******************************************************************
         * Initialize charReader.                                          *
         ******************************************************************/
        PcalBuiltInSymbols.Initialize();

        /*******************************************************************
         * Performs the initialization method of the AST to create default  *
         * objects for each subclass.                                       *
         *******************************************************************/

        /*
         * Following added by LL on 17 Aug 2015 to fix bug apparently caused by
         * incomplete initialization
         */
        LATsize = 0;
    }

    public AST getAlgorithm(final PcalCharReader charR, final boolean fairAlgorithm) throws ParseAlgorithmException
    /**********************************************************************
     * Assumes that the char reader charR is just past the string          *
     * PcalParams.BeginAlg that marks the character right after            *
     * "--algorithm" or "--fair".  The argument fairAlgorithm is true iff  *
     * the algorithm was begun by "--fair".                                *
     *                                                                     *
     * The AST that it returns does not have the col and line fields set.  *
     * If those fields might ever be used in an error message, they        *
     * should be set to the position of the PcalParams.BeginAlg string by  *
     * whatever method finds that string and calls GetAlgorithm.           *
     **********************************************************************/
    {
        try {
            Init(charR);
            if (fairAlgorithm) {
                final String nextToken = GetAlgToken();
                if (!nextToken.equals(PcalParams.BeginFairAlg2)) {
                    ParsingError("`" + PcalParams.BeginFairAlg + "' not followed by `"
                            + PcalParams.BeginFairAlg2 + "'");
                }
                pcalParams.FairAlgorithm = true;
            }
            final String name = GetAlgToken();
            if (PeekAtAlgToken(1).equals("{")) {
                cSyntax = true;
                MustGobbleThis("{");
            } else {
                pSyntax = true;
            }
            ArrayList<VarDecl> vdecls = new ArrayList<>();
            if (PeekAtAlgToken(1).equals("variable")
                    || PeekAtAlgToken(1).equals("variables")) {
                vdecls = GetVarDecls();
            }
            TLAExpr defs = new TLAExpr();
            if (PeekAtAlgToken(1).equals("define")) {
                MustGobbleThis("define");
                if (cSyntax) {
                    GobbleThis("{");
                }
                defs = GetExpr();
                if (pSyntax) {
                    GobbleThis("end");
                    GobbleThis("define");
                } else {
                    GobbleThis("}");
                }
                GobbleThis(";");
            }
            final ArrayList<Macro> macros = new ArrayList<>();
            while (PeekAtAlgToken(1).equals("macro")) {
                macros.add(GetMacro(macros));
            }
            while (PeekAtAlgToken(1).equals("procedure")) {
                procedures.add(GetProcedure());
                // if there's a procedure, we assume that it's
                // called, so we must not omit the pc variable.
                omitPC = false;
            }
            if ((PeekAtAlgToken(1).equals("fair")
                    && (PeekAtAlgToken(2).equals("process")
                    || (PeekAtAlgToken(2).equals("+")
                    && PeekAtAlgToken(3).equals("process")
            )
            )
            )
                    || PeekAtAlgToken(1).equals("process")) {
                final AST.Multiprocess multiproc = new AST.Multiprocess(pcalParams);
                final TLAtoPCalMapping map = pcalParams.tlaPcalMapping;
                final PCalLocation multiprocBegin = new PCalLocation(map.algLine, map.algColumn);
                multiproc.name = name;
                multiproc.decls = vdecls;
                multiproc.defs = defs;
                multiproc.macros = macros;
                multiproc.prcds = procedures;
                multiproc.procs = new ArrayList<>();
                while (PeekAtAlgToken(1).equals("fair") ||
                        PeekAtAlgToken(1).equals("process")) {
                    int fairness = AST.UNFAIR_PROC;
                    if (PeekAtAlgToken(1).equals("fair")) {
                        MustGobbleThis("fair");
                        if (PeekAtAlgToken(1).equals("+")) {
                            MustGobbleThis("+");
                            fairness = AST.SF_PROC;
                        } else {
                            fairness = AST.WF_PROC;
                        }
                    } else {
                        if (pcalParams.FairnessOption.equals("wf")) {
                            fairness = AST.WF_PROC;
                        } else if (pcalParams.FairnessOption.equals("sf")) {
                            fairness = AST.SF_PROC;
                        }
                    }
                    final AST.Process proc = GetProcess();
                    proc.fairness = fairness;
                    multiproc.procs.add(proc);
                }
                if (pSyntax) {
                    GobbleThis("end");
                    GobbleThis("algorithm");
                } else {
                    GobbleThis("}");
                }
                CheckForDuplicateMacros(multiproc.macros);
                int i = 0;
// LL comment added 11 Mar 2006
// It should be possible to exchange the order of the next
// two while loops, which would cause printing of added labels
// in the correct order, but it doesn't seem to be worth the
// risk that something I haven't thought of will break.

                // See the comment to the checkBody method to see
                // why omitStutteringWhenDoneValue is being set
                // to the correct value of omitStutteringWhenDone.
                // (Added by LL on 30 Mar 2012.)
                boolean omitStutteringWhenDoneValue = false;
                while (i < multiproc.procs.size()) {
                    final AST.Process proc =
                            multiproc.procs.get(i);
                    ExpandMacrosInStmtSeq(proc.body, multiproc.macros);
                    AddLabelsToStmtSeq(proc.body);
                    proc.body = MakeLabeledStmtSeq(proc.body);

                    omitStutteringWhenDone = true;
                    checkBody(proc.body);
                    omitStutteringWhenDoneValue =
                            omitStutteringWhenDoneValue || omitStutteringWhenDone;

                    i = i + 1;
                }
                omitStutteringWhenDone = omitStutteringWhenDoneValue;
                i = 0;
                while (i < multiproc.prcds.size()) {
                    final AST.Procedure prcd =
                            multiproc.prcds.get(i);
                    currentProcedure = prcd.name;
                    ExpandMacrosInStmtSeq(prcd.body, multiproc.macros);
                    AddLabelsToStmtSeq(prcd.body);
                    prcd.body = MakeLabeledStmtSeq(prcd.body);
                    i = i + 1;
                }
                /****************************************************************
                 * Check for added labels, report an error if there shouldn't    *
                 * be any, and print them out if the -reportLabels was           *
                 * specified.                                                    *
                 ****************************************************************/
                if (addedLabels.size() > 0) {
                    if (!pcalParams.LabelFlag) {
                        AddedMessagesError();
                    }
                    if (pcalParams.ReportLabelsFlag) {
                        ReportLabels();
                    } else
                    // SZ March 11, 2009: info reporting using PcalDebug added
                    {
                        PcalDebug.reportInfo("Labels added.");
                    }
                }
                if (gotoDoneUsed) {
                    omitPC = false;
                    omitStutteringWhenDone = false;
                }
                if (gotoUsed) {
                    omitPC = false;
                }
                multiproc.setOrigin(new Region(multiprocBegin,
                        GetLastLocationEnd()));
                return multiproc;
            } else {
                final AST.Uniprocess uniproc = new AST.Uniprocess(pcalParams);
                final TLAtoPCalMapping map = pcalParams.tlaPcalMapping;
                final PCalLocation uniprocBegin = new PCalLocation(map.algLine, map.algColumn);
                uniproc.name = name;
                uniproc.decls = vdecls;
                uniproc.defs = defs;
                uniproc.macros = macros;
                uniproc.prcds = procedures;
                // Version 1.5 allowed "fair" to appear here
                // to specify fairness for a sequential algorithm
                if (pcalParams.inputVersionNumber == PcalParams.VersionToNumber("1.5")) {
                    if (PeekAtAlgToken(1).equals("fair")) {
                        GobbleThis("fair");
                        if (PeekAtAlgToken(1).equals("+")) {
                            GobbleThis("+");
                        }
                        pcalParams.FairnessOption = "wf";
                    }
                }

                // Following if statement added by LL on 5 Oct 2011
                // to fix bug in which --fair uniprocess algorithm
                // wasn't producing fairness condition.
                if (fairAlgorithm) {
                    if (!pcalParams.FairnessOption.equals("")
                            && !pcalParams.FairnessOption.equals("wf")
                            && !pcalParams.FairnessOption.equals("wfNext")) {
                        PcalDebug.reportWarning("Option `" + pcalParams.FairnessOption + "' specified for --fair algorithm.");
                    }
                    pcalParams.FairnessOption = "wf";
                }

                GobbleBeginOrLeftBrace();
                uniproc.body = GetStmtSeq();
                CheckForDuplicateMacros(uniproc.macros);
                ExpandMacrosInStmtSeq(uniproc.body, uniproc.macros);
// LL comment added 11 Mar 2006.
// I moved the following to after processing the procedures
// so added labels are printed in correct order-- e.g., with
// -reportLabels option
                int i = 0;
                while (i < uniproc.prcds.size()) {
                    final AST.Procedure prcd =
                            uniproc.prcds.get(i);
                    currentProcedure = prcd.name;
                    ExpandMacrosInStmtSeq(prcd.body, uniproc.macros);
                    AddLabelsToStmtSeq(prcd.body);
                    prcd.body = MakeLabeledStmtSeq(prcd.body);
                    i = i + 1;
                }
                if (cSyntax) {
                    GobbleThis("}");
                    GobbleThis("}");
                } else {
                    GobbleThis("end");
                    GobbleThis("algorithm");
                }
                AddLabelsToStmtSeq(uniproc.body);
                uniproc.body = MakeLabeledStmtSeq(uniproc.body);
                /****************************************************************
                 * Check for added labels, report an error if there shouldn't    *
                 * be any, and print them out if the -reportLabels was           *
                 * specified.                                                    *
                 ****************************************************************/
                if (addedLabels.size() > 0) {
                    if (hasLabel && !pcalParams.LabelFlag) {
                        AddedMessagesError();
                    }
                    if (pcalParams.ReportLabelsFlag) {
                        ReportLabels();
                    } else
                    // SZ March 11, 2009: info reporting using PcalDebug added
                    {
                        PcalDebug.reportInfo("Labels added.");
                    }
                }

                if (gotoUsed) {
                    omitPC = false;
                }
                if (gotoDoneUsed) {
                    omitPC = false;
                    omitStutteringWhenDone = false;
                } else {
                    checkBody(uniproc.body);
                }
                uniproc.setOrigin(new Region(uniprocBegin,
                        GetLastLocationEnd()));
                return uniproc;
            }
        } catch (final RuntimeException e) {
            // Catch generic/unhandled errors (ArrayIndexOutOfbounds/NullPointers/...) that
            // the nested code might throw at us. Not converting them into a
            // ParseAlgorithmException means the Toolbox silently fails to translate an
            // algorithm (see Github issue at https://github.com/tlaplus/tlaplus/issues/313)
            ParsingError("Unknown error at or before");
            return null;
        }
    }

    /**
     * The argument body is either the body of a uniprocess algorithm or of a process in
     * a multiprocess algorithm.  This procedure sets omitPC or omitStutteringWhenDone
     * to false if this body implies that the pc or stuttering-when-done disjunct
     * cannot be omitted.  This is the case unless the body consists of a single
     * `while (TRUE)' statement.  In that case, the pc cannot be omitted
     * iff there is a label in the body, which is the case iff either the AST.While
     * object has a non-empty labDo field, or the unlabDo field contains a
     * LabelIf or LabelEither. (The pc also cannot be omitted if
     * the body has a procedure call, but that is checked elsewhere.)
     * <p>
     * This method incorrectly sets omitStutteringWhenDone for a multiprocess
     * algorithm.  The omitStutteringWhenDone flag should be set to true
     * iff it is impossible for the algorithm to terminate.  This is true
     * iff there is some process that cannot terminate.  However, since this
     * method is called for each process (or process set), it causes
     * omitStutteringWhenDone to be set false if any process can terminate,
     * rather than being set false iff all processes can terminate.
     * Since this is the right procedure for setting omitPC (since the pc
     * cannot be omitted if it is needed to represent any process), I decided
     * not to modify this method, but to work around the problem in the method
     * that calls it.  Comment added by LL on 30 Mar 2012.
     */
    private void checkBody(final ArrayList<AST> body) {
        // The body should not be empty, so the following
        // test should be redundant.  But just in case the
        // error is being found elsewhere...
        if (body == null || (body.size() == 0)) {
            return;
        }
        if ((body.size() > 1) ||
                !(body.get(0) instanceof final AST.LabeledStmt lblStmt)) {
            omitPC = false;
            omitStutteringWhenDone = false;
            return;
        }
        if ((lblStmt.stmts == null) || (lblStmt.stmts.size() == 0)) {
            // Again, this shouldn't happen.
            return;
        }
        if ((lblStmt.stmts.size() > 1) ||
                !(lblStmt.stmts.get(0) instanceof final AST.While whileStmt)) {
            omitPC = false;
            omitStutteringWhenDone = false;
            return;
        }

        final ArrayList<?> tokens = whileStmt.test.tokens;
        if (tokens.size() != 1) {
            omitPC = false;
            omitStutteringWhenDone = false;
            return;
        }
        final ArrayList<?> line = (ArrayList<?>) tokens.get(0);
        if (line.size() != 1) {
            omitPC = false;
            omitStutteringWhenDone = false;
            return;
        }
        final TLAToken tok = (TLAToken) line.get(0);
        if (!tok.string.equals("TRUE")) {
            omitPC = false;
            omitStutteringWhenDone = false;
            return;
        }
        if ((whileStmt.labDo != null) && (whileStmt.labDo.size() > 0)) {
            omitPC = false;
        }

        if (whileStmt.unlabDo == null) {
            return;
        }

        for (int i = 0; i < whileStmt.unlabDo.size(); i++) {
            final Object obj = whileStmt.unlabDo.get(i);
            // in the following test, I think the LabeledStmt test
            // is unnecessary, because there can only be a LabeledStmt
            // in a while statements unlabDo field if it is preceded by
            // a LabelIf or LabelEither
            if (obj instanceof AST.LabelIf ||
                    obj instanceof AST.LabelEither ||
                    obj instanceof AST.LabeledStmt
            ) {
                omitPC = false;
                return;
            }
        }
    }
    /***********************************************************************
     * This boolean equals true while inside a call to GetMacro.  It is used to
     * flag an error if a label appears within a macro.
     * @throws ParseAlgorithmException *
     ***********************************************************************/

    public void AddedMessagesError() throws ParseAlgorithmException {
        StringBuilder msg;
        if (addedLabels.size() > 1) {
            msg = new StringBuilder("Missing labels at the following locations:");
        } else {
            msg = new StringBuilder("Missing label at the following location:");
        }
        int i = 0;
        while (i < addedLabels.size()) {
            msg.append("\n     ").append(addedLabelsLocs.get(i));
            i = i + 1;
        }
        throw new ParseAlgorithmException(msg.toString());
    }

    public void ReportLabels()
    // SZ March 11, 2009: info reporting using PcalDebug added
    {
        if (addedLabels.size() > 1) {
            PcalDebug.reportInfo("The following labels were added:");
        } else {
            PcalDebug.reportInfo("The following label was added:");
        }
        int i = 0;
        while (i < addedLabels.size()) {
            PcalDebug.reportInfo("  "
                    + addedLabels.get(i)
                    + " at "
                    + addedLabelsLocs.get(i));
            i = i + 1;
        }
    }

    public AST.Procedure GetProcedure() throws ParseAlgorithmException {
        final AST.Procedure result = new AST.Procedure(pcalParams);
        GobbleThis("procedure");
        final PCalLocation beginLoc = GetLastLocationStart();
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.name = GetAlgToken();
        currentProcedure = result.name;
        plusLabels = new ArrayList<>(0);
        minusLabels = new ArrayList<>(0);
        proceduresCalled = new ArrayList<>(0);
        GobbleThis("(");
        result.params = new ArrayList<>();
        boolean lookForComma = false;
        while (!PeekAtAlgToken(1).equals(")")) {
            if (lookForComma) {
                GobbleThis(",");
            }
            result.params.add(GetPVarDecl());
            lookForComma = true;
        }
        MustGobbleThis(")");
        if (PeekAtAlgToken(1).equals("begin")
                || PeekAtAlgToken(1).equals("{")) {
            result.decls = new ArrayList<>(1);
        } else {
            result.decls = GetPVarDecls();
        }
        GobbleBeginOrLeftBrace();
        result.body = GetStmtSeq();
        GobbleEndOrRightBrace("procedure");
        final PCalLocation endLoc = GetLastLocationEnd();
        if (PeekAtAlgToken(1).equals(";")) {
            @SuppressWarnings("unused") final String tok = GetAlgToken();
        }
//       CheckLabeledStmtSeq(result.body) ;
        currentProcedure = null;
        result.plusLabels = plusLabels;
        result.minusLabels = minusLabels;
        result.proceduresCalled = proceduresCalled;
        result.setOrigin(new Region(beginLoc, endLoc));
        return result;
    }

    public AST.Process GetProcess() throws ParseAlgorithmException {
        final AST.Process result = new AST.Process(pcalParams);
        GobbleThis("process");
        final PCalLocation beginLoc = GetLastLocationStart();
        result.col = lastTokCol;
        result.line = lastTokLine;
        if (cSyntax) {
            GobbleThis("(");
        }
        result.name = GetAlgToken();
        result.isEq = GobbleEqualOrIf();
        result.id = GetExpr();
        plusLabels = new ArrayList<>(0);
        minusLabels = new ArrayList<>(0);
        proceduresCalled = new ArrayList<>(0);
        if (cSyntax) {
            GobbleThis(")");
        }
        if (result.id.tokens.size() == 0) {
            ParsingError("Empty process id at ");
        }
        if (PeekAtAlgToken(1).equals("begin")
                || PeekAtAlgToken(1).equals("{")) {
            result.decls = new ArrayList<>(1);
        } else {
            result.decls = GetVarDecls();
        }
        GobbleBeginOrLeftBrace();
        result.body = GetStmtSeq();
        GobbleEndOrRightBrace("process");
        final PCalLocation endLoc = GetLastLocationEnd();
        if (PeekAtAlgToken(1).equals(";")) {
            @SuppressWarnings("unused") final String tok = GetAlgToken();
        }
//       CheckLabeledStmtSeq(result.body) ;
        result.plusLabels = plusLabels;
        result.minusLabels = minusLabels;
        result.proceduresCalled = proceduresCalled;
        result.setOrigin(new Region(beginLoc, endLoc));
        return result;
    }

    public ArrayList<PVarDecl> GetPVarDecls() throws ParseAlgorithmException
    /**********************************************************************
     * Parses a <PVarDecls> as a ArrayList of AST.PVarDecl objects.           *
     **********************************************************************/
    {
        final String tok = PeekAtAlgToken(1);
        if (tok.equals("variables")) {
            MustGobbleThis("variables");
        } else {
            GobbleThis("variable");
        }
        final ArrayList<PVarDecl> result = new ArrayList<>();

        /********************************************************************
         * The <PVarDecls> nonterminal is terminated by a "begin"            *
         * (p-syntax) or "{" (c-syntax) for the procedure.                   *
         ********************************************************************/
        while (!(PeekAtAlgToken(1).equals("begin")
                || PeekAtAlgToken(1).equals("{"))) {
            result.add(GetPVarDecl());
            GobbleCommaOrSemicolon();
            /**************************************************************
             * Changed on 24 Mar 2006 from GobbleThis(";") to allow        *
             * declarations to be separated by commas.                     *
             **************************************************************/
        }
        return result;
    }

    public AST.PVarDecl GetPVarDecl() throws ParseAlgorithmException {
        final AST.PVarDecl pv = new AST.PVarDecl(pcalParams);
        pv.var = GetAlgToken();
        final PCalLocation beginLoc = GetLastLocationStart();
        PCalLocation endLoc = GetLastLocationEnd();
        pv.col = lastTokCol;
        pv.line = lastTokLine;
        if (PeekAtAlgToken(1).equals("=")) {
            GobbleThis("=");
            pv.val = GetExpr();
            endLoc = pv.val.getOrigin().getEnd();
            if (pv.val.tokens.size() == 0) {
                ParsingError("Missing expression at ");
            }
        } else {
            hasDefaultInitialization = true;
        }
        pv.setOrigin(new Region(beginLoc, endLoc));
        return pv;
    }

    public ArrayList<VarDecl> GetVarDecls() throws ParseAlgorithmException
    /**********************************************************************
     * Parses a <VarDecls> as a ArrayList of AST.VarDecl objects.             *
     **********************************************************************/
    {
        final String tok = PeekAtAlgToken(1);
        if (tok.equals("variables")) {
            MustGobbleThis("variables");
        } else {
            GobbleThis("variable");
        }
        final ArrayList<VarDecl> result = new ArrayList<>();

        /********************************************************************
         * The <VarDecls> nonterminal appears in two places:                 *
         *                                                                   *
         * - In a <Procedure> or <Process>, where it is terminated by        *
         *   a "begin" (p-syntax) or "{" (c-syntax).                         *
         *                                                                   *
         * - At the beginning of a <Algorithm>, where it is terminated by    *
         *   "define", "macro", "procedure", "begin" or "{", or "process" .  *
         ********************************************************************/
        while (!(PeekAtAlgToken(1).equals("begin")
                || PeekAtAlgToken(1).equals("{")
                || PeekAtAlgToken(1).equals("procedure")
                || PeekAtAlgToken(1).equals("process")
                || PeekAtAlgToken(1).equals("fair")
                || PeekAtAlgToken(1).equals("define")
                || PeekAtAlgToken(1).equals("macro"))) {
            result.add(GetVarDecl());
        }
        return result;
    }

    public AST.VarDecl GetVarDecl() throws ParseAlgorithmException {
        final AST.VarDecl pv = new AST.VarDecl(pcalParams);
        pv.var = GetAlgToken();
        final PCalLocation beginLoc = GetLastLocationStart();
        PCalLocation endLoc = GetLastLocationEnd();
        pv.col = lastTokCol;
        pv.line = lastTokLine;
        if (PeekAtAlgToken(1).equals("=")
                || PeekAtAlgToken(1).equals("\\in")) {
            pv.isEq = GobbleEqualOrIf();
            pv.val = GetExpr();
            endLoc = pv.val.getOrigin().getEnd();
            if (pv.val.tokens.size() == 0) {
                ParsingError("Missing expression at ");
            }
        } else {
            hasDefaultInitialization = true;
        }

        GobbleCommaOrSemicolon();
        /******************************************************************
         * Changed on 24 Mar 2006 from GobbleThis(";") to allow            *
         * declarations to be separated by commas.                         *
         ******************************************************************/
        pv.setOrigin(new Region(beginLoc, endLoc));
        return pv;
    }

    public TLAExpr GetExpr() throws ParseAlgorithmException {
        if (LATsize != 0) {
            PcalDebug.ReportBug(
                    "ParseAlgorithm: GetExpr called after lookahead");
        }
        final TLAExpr result;
        try {
            result = tokenizer.TokenizeExpr(charReader);
        } catch (final TokenizerException e) {
            throw new ParseAlgorithmException(e.getMessage());
        }
        LAT[LATsize] = tokenizer.Delimiter;
        curTokCol[LATsize] = tokenizer.DelimiterCol;
        curTokLine[LATsize] = tokenizer.DelimiterLine;
        LATsize = LATsize + 1;

        /**
         * If the expression has any tokens, then set the origin to the
         * region comprising the tokens.  Otherwise, set the region to null.
         */
        if (result.tokens != null && result.tokens.size() != 0) {
            final PCalLocation begin = ((TLAToken) ((ArrayList<?>)
                    result.tokens.get(0))
                    .get(0)).source.getBegin();
            final ArrayList<?> lastLineOfTokens = result.tokens.get(
                    result.tokens.size() - 1);
            if (lastLineOfTokens.size() == 0) {
                Debug.ReportBug("Unexpected Event in this.GetExpr");
            }

            final PCalLocation end = ((TLAToken) lastLineOfTokens.get(
                    lastLineOfTokens.size() - 1)).source.getEnd();
            result.setOrigin(new Region(begin, end));
        } else {
            result.setOrigin(null);
        }
        return result;
    }

    /* OBSOLETE */
    public AST.LabeledStmt ObsoleteGetLabeledStmt() throws ParseAlgorithmException {
        if (!IsLabelNext()) {
            ParsingError("Was expecting a label");
        }
        final AST.LabeledStmt result = new AST.LabeledStmt(pcalParams);
        result.label = GetAlgToken();
        if (result.label.equals("Done")) {
            ParsingError("Cannot use `Done' as a label.");
        }
        if (result.label.equals("Error")) {
            ParsingError("Cannot use `Error' as a label.");
        }
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.stmts = new ArrayList<>();
        GobbleThis(":");
        if (PeekAtAlgToken(1).equals("while")) {
            result.stmts.add(GetWhile());
        }
        final ArrayList<AST> stmtSeq = GetStmtSeq();
        int i = 0;
        while (i < stmtSeq.size()) {
            result.stmts.add(stmtSeq.get(i));
            i = i + 1;
        }
        if (result.stmts.size() == 0) {
            ParsingError("Label with no following statement");
        }
        return result;
    }

    public AST.While GetWhile() throws ParseAlgorithmException {
        MustGobbleThis("while");
        final PCalLocation beginLoc = GetLastLocationStart();
        final AST.While result = new AST.While(pcalParams);
        result.col = lastTokCol;
        result.line = lastTokLine;
        if (cSyntax) {
            GobbleThis("(");
        }
        result.test = GetExpr();
        if (cSyntax) {
            GobbleThis(")");
        }
        if (result.test.tokens.size() == 0) {
            ParsingError("Empty while test at ");
        }
        if (pSyntax) {
            GobbleThis("do");
            result.unlabDo = GetStmtSeq();
            GobbleThis("end");
            GobbleThis("while");
            GobbleThis(";");
        } else {
            result.unlabDo = GetCStmt();
        }
        if (result.unlabDo.size() == 0) {
            ParsingError("Missing body of while statement at");
        }
        result.labDo = new ArrayList<>();
        /******************************************************************
         * For historical reasons, some methods expect a labDo field to    *
         * contain a vector, even though they are called before the real   *
         * labDo field is created.                                         *
         ******************************************************************/
        result.setOrigin(new Region(beginLoc,
                result.unlabDo.get(result.unlabDo.size() - 1)
                        .getOrigin().getEnd()));
        return result;
    }

    public String GetLabel() throws ParseAlgorithmException
    /**********************************************************************
     * Checks if a label comes next.  If so, it gobbles it and returns     *
     * the label.  Otherwise, it returns "".                               *
     **********************************************************************/
    {
        String nextLabel = "";
        if (IsLabelNext()) {
            nextLabel = GetAlgToken();
            getLabelLocation = new PCalLocation(lastTokLine - 1, lastTokCol - 1);
            if (inGetMacro) {
                ParsingError("A label may not appear in a macro.");
            }
            if (nextLabel.equals("Done")) {
                ParsingError("Cannot use `Done' as a label.");
            }
            if (nextLabel.equals("Error")) {
                ParsingError("Cannot use `Error' as a label.");
            }
            GobbleThis(":");
            hasLabel = true;
            allLabels.put(nextLabel, "");
            // The following code added by LL on 12 Jan 2011 as part of
            // implementation of the fairness modifiers on labels introduced
            // in Version 1.5.
            // Modified by LL on 20 Mar 2011 to set omitPC false if there's
            // a + or - modifier, since this modifier creates a reference
            // to the label in the fairness condition.
            if (PeekAtAlgToken(1).equals("+")) {
                GobbleThis("+");
                plusLabels.add(nextLabel);
                omitPC = false;
            } else {
                if (PeekAtAlgToken(1).equals("-")) {
                    GobbleThis("-");
                    minusLabels.add(nextLabel);
                    omitPC = false;
                }
            }
        }
        return nextLabel;
    }

    public ArrayList<AST> GetStmtSeq() throws ParseAlgorithmException
    /**********************************************************************
     * Parses a sequence of <Stmt>s and returns the result as a ArrayList of  *
     * <Stmt> nodes.  It detects the end of the sequence by the            *
     * appearance of one of the following tokens                           *
     *                                                                     *
     *   end   else   elsif   or                                           *
     *                                                                     *
     * in the p-syntax or "}" in the c-syntax.                             *
     **********************************************************************/
    {
        final ArrayList<AST> result = new ArrayList<>();
        String tok = PeekAtAlgToken(1);
        while (!((pSyntax
                && (tok.equals("end")
                || tok.equals("else")
                || tok.equals("elsif")
                || tok.equals("or")))
                || (cSyntax && tok.equals("}")))) {
            final String nextLabel = GetLabel();
            final PCalLocation labelLoc = getLabelLocation;
            if (cSyntax && PeekAtAlgToken(1).equals("{")) { /************************************************************
             * We're using c-syntax and the next statement is a          *
             * StmtSeq.                                                  *
             ************************************************************/
                result.addAll(GetCStmtSeq(nextLabel));
            } else { /************************************************************
             * This is an ordinary statement.                            *
             ************************************************************/
                final AST stmt = GetStmt();
                stmt.lbl = nextLabel;
                stmt.lblLocation = labelLoc;
                result.add(stmt);
            }
            tok = PeekAtAlgToken(1);
        }
        if (cSyntax && (result.size() == 0))
        /*****************************************************************
         * I'm not sure if GetStmtSeq should be able to return an empty   *
         * sequence in p-syntax, but it definitely shouldn't in c-syntax  *
         * (I think).                                                     *
         *****************************************************************/ {
            ParsingError("Empty statement list");
        }
        return result;
    }

    public AST GetStmt() throws ParseAlgorithmException {
        final String nextTok = PeekAtAlgToken(1);
        if (nextTok.equals("if")) {
            return GetIf(0);
        }
        if (nextTok.equals("either")) {
            return GetEither();
        }
        if (nextTok.equals("with")) {
            return GetWith(0);
        }
        if (nextTok.equals("when")) {
            return GetWhen(true);
        }
        if (nextTok.equals("await")) {
            return GetWhen(false);
        }
        if (nextTok.equals("print")) {
            return GetPrintS();
        }
        if (nextTok.equals("assert")) {
            return GetAssert();
        }
        if (nextTok.equals("skip")) {
            return GetSkip();
        }
        if (nextTok.equals("call")) {
            return GetCallOrCallReturnOrCallGoto();
        }
        if (nextTok.equals("return")) {
            return GetReturn();
        }
        if (nextTok.equals("goto")) {
            return GetGoto();
        }
        if (nextTok.equals("while")) {
            return GetWhile();
        }
        if (PeekPastAlgToken(1).charAt(0) == '(') {
            return GetMacroCall();
        }
        return GetAssign();
    }

    public ArrayList<AST> GetCStmtSeq(final String lbl) throws ParseAlgorithmException
    /**********************************************************************
     * Gets a c-syntax StmtSeq (enclosed in curly braces) that has a       *
     * label lbl.                                                          *
     **********************************************************************/
    {
        /**
         * The argument lbl must have been obtained by a call to GetLabel,
         * and there must not have been any call to GetLabel after that call.
         * We can therefore get the location of lbl from getLabelLocation.
         */
        final PCalLocation lblLocation = getLabelLocation;
        MustGobbleThis("{");
        final ArrayList<AST> sseq = GetStmtSeq();
        GobbleThis("}");
        GobbleThis(";");
        if (!lbl.equals("")) { /********************************************************
         * There entire StmtSeq is labeled.                      *
         ********************************************************/
            if (!sseq.get(0).lbl.equals("")) {
                throw new ParseAlgorithmException("Duplicate labeling of statement",
                        sseq.get(0));
            }
            final AST firstStmt = sseq.get(0);
            firstStmt.lbl = lbl;
            firstStmt.lblLocation = lblLocation;
        }
        return sseq;
    }

    public ArrayList<AST> GetCStmt() throws ParseAlgorithmException
    /**********************************************************************
     * Get one (possibly labeled) statement in the c-syntax, which could   *
     * be a StmtSeq, so this returns a vector of AST nodes.                *
     **********************************************************************/
    {
        final String label = GetLabel();
        final PCalLocation labelLocation = getLabelLocation;
        if (PeekAtAlgToken(1).equals("{")) {
            return GetCStmtSeq(label);
        }
        final AST stmt = GetStmt();
        stmt.lbl = label;
        stmt.lblLocation = labelLocation;
        final ArrayList<AST> result = new ArrayList<>();
        result.add(stmt);
        return result;
    }

    public boolean IsLabelNext() throws ParseAlgorithmException
    /**********************************************************************
     * Peeks at the next token and perhaps at the next two characters to   *
     * determine if the next token is a label.  The tricky part is         *
     * distinguishing "label : " from "var :=" when the next token isn't   *
     * a keyword.  Since this is called at the beginning of a syntactic    *
     * unit that might be a labeled statement, I believe that the only     *
     * keywords it needs to check are                                      *
     *                                                                     *
     *    while  if  else  elsif  either  or  end   with  when  skip       *
     *    call  return  assert print                                       *
     **********************************************************************/
    {
        String tok = PeekAtAlgToken(1);
        if ((tok.equals("while"))
                || (tok.equals("if"))
                || (tok.equals("assert"))
                || (tok.equals("print"))
                || (tok.equals("else"))
                || (tok.equals("elsif"))
                || (tok.equals("either"))
                || (tok.equals("or"))
                || (tok.equals("end"))
                || (tok.equals("with"))
                || (tok.equals("when"))
                || (tok.equals("await"))
                || (tok.equals("skip"))
                || (tok.equals("call"))
                || (tok.equals("return"))
                || (tok.equals("goto"))
        ) {
            return false;
        }
        tok = charReader.peek();
        return (tok.length() != 0) // I don't think this can happen.
                && (tok.charAt(0) == ':')
                && ((tok.length() <= 1)
                || (tok.charAt(1) != '='));
    }

    public AST.LabelIf GetIf(final int depth) throws ParseAlgorithmException
    /**********************************************************************
     * If depth = 0, then the next token is "if" and this is the start of  *
     * an if statement.                                                    *
     *                                                                     *
     * If depth > 0, then the next token is "elsif".  An "elsif" is        *
     * equivalent to "else if" except that the "end if" of the outer "if"  *
     * also ends the inner "if".  Hence, an "elsif" is parsed like an      *
     * "if", but it doesn't gobble the "end if".  So there's really no     *
     * reason to count the depth, beyond knowing if it's 0 or not, but     *
     * having the depth might be useful for debugging.  This parses any    *
     * "if" statement as a LabelIf.  It may later be replaced by an If.    *
     *	                                                                   *
     * Note: The origin is set so that the region ends at the end of the   *
     * last statement in the then or else (as appropriate).  However, the  *
     * region should end at the end of the "end if" for P syntax or at the *
     * end of the "}" if the then or else clause is a statement sequence.  *
     * To correct this, need to have GetCStmt (and perhaps GetStmtSeq)     *
     * return (by a variable) whether or not there is an ending "}" and    *
     * its location if there is one.                                       *
     **********************************************************************/
    {
        if (depth == 0) {
            MustGobbleThis("if");
        } else {
            MustGobbleThis("elsif");
        }
        final PCalLocation beginLoc = GetLastLocationStart();
        final AST.LabelIf result = new AST.LabelIf(pcalParams);
        result.col = lastTokCol;
        result.line = lastTokLine;
        if (cSyntax) {
            GobbleThis("(");
        }
        result.test = GetExpr();
        if (cSyntax) {
            GobbleThis(")");
        }
        if (result.test.tokens.size() == 0) {
            ParsingError("Empty if test at ");
        }
        if (pSyntax) {
            GobbleThis("then");
            result.unlabThen = GetStmtSeq();
        } else {
            result.unlabThen = GetCStmt();
        }
        final String nextTok = PeekAtAlgToken(1);
        if (pSyntax) {
            switch (nextTok) {
                case "else" -> {
                    MustGobbleThis("else");
                    result.unlabElse = GetStmtSeq();
                }
                case "elsif" -> {
                    final AST.LabelIf innerIf = GetIf(depth + 1);
                    result.unlabElse = new ArrayList<>();
                    result.unlabElse.add(innerIf);
                }
                case "end" -> result.unlabElse = new ArrayList<>();
                default -> ParsingError(
                        "Expecting \"else\", \"elsif\", or \"end\"");
            }
            if (depth == 0) {
                GobbleThis("end");
                GobbleThis("if");
                GobbleThis(";");
            }
        } else /* c syntax */ {
            if (nextTok.equals("else")) {
                MustGobbleThis("else");
                result.unlabElse = GetCStmt();
            } else {
                result.unlabElse = new ArrayList<>();
            }
        }
        result.labThen = new ArrayList<>();
        result.labElse = new ArrayList<>();

        /**
         * Set lastStmt to the AST node of the last statement in the
         * if, which is either at the end of the end clause or, if there is none,
         * at the end of the then clause.
         */
        AST lastStmt;
        if (result.unlabElse.size() != 0) {
            lastStmt = result.unlabElse.get(result.unlabElse.size() - 1);
        } else {
            lastStmt = result.unlabThen.get(result.unlabThen.size() - 1);
        }

        /**
         * Set the LabelIf's origin to the region from the beginning of the "if"
         * to the end of the last then or else statement.
         */
        result.setOrigin(new Region(beginLoc, lastStmt.getOrigin().getEnd()));
        return result;
    }

    public AST.LabelEither GetEither() throws ParseAlgorithmException {
        MustGobbleThis("either");
        final PCalLocation beginLoc = GetLastLocationStart();
        final AST.LabelEither result = new AST.LabelEither(pcalParams);
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.clauses = new ArrayList<>();
        boolean done = false;
        boolean hasOr = false;
        while (!done) {
            final AST.Clause nextClause = new AST.Clause(pcalParams);
            nextClause.labOr = new ArrayList<>();
            if (pSyntax) {
                nextClause.unlabOr = GetStmtSeq();
            } else {
                nextClause.unlabOr = GetCStmt();
            }
            if (nextClause.unlabOr.size() == 0) {
                throw new ParseAlgorithmException(
                        "`either' statement with empty `or' clause", result);
            }
            nextClause.setOrigin(new Region(
                    nextClause.unlabOr.get(0).getOrigin().getBegin(),
                    nextClause.unlabOr.get(nextClause.unlabOr.size() - 1)
                            .getOrigin().getEnd()));
            result.clauses.add(nextClause);
            final String nextTok = PeekAtAlgToken(1);
            if (nextTok.equals("or")) {
                MustGobbleThis("or");
                hasOr = true;
            } else {
                done = true;
            }
        }
        if (pSyntax) {
            MustGobbleThis("end");
            GobbleThis("either");
            GobbleThis(";");
        }
        if (!hasOr) {
            throw new ParseAlgorithmException("`either' statement has no `or'", result);
        }
        result.setOrigin(new Region(beginLoc,
                result.clauses.get(result.clauses.size() - 1)
                        .getOrigin().getEnd()));
        return result;
    }

    /**
     * For constructing the TLA+ to PlusCal mapping, the original GetWith
     * procedure was given a second argument and was renamed InnerGetWidth.
     * See the comments for that method
     */
    public AST GetWith(final int depth) throws ParseAlgorithmException {
        return InnerGetWith(depth, null);
    }

    public AST InnerGetWith(final int depth, final PCalLocation beginLoc) throws ParseAlgorithmException
    /**********************************************************************
     * A with statement has p-syntax                                       *
     *                                                                     *
     *    <With> ::= "with" <VarEqOrIn>^+ "do" <SimpleStmt>^+ "end either" *
     *       where <VarEqOrIn> ::= <Variable> [=|\in] <Expr> ";"           *
     *                                                                     *
     * where the last ";" before the "do" is optional.  The c-syntax is    *
     * analogous.                                                          *
     *                                                                     *
     * This is converted to a nest of k With objects, where k is the       *
     * number of <VarEqOrIn> terms.  If depth = 0, then the next token is  *
     * the "with".  If depth > 0, then what follows is a <VarEqOrIn>       *
     * term.                                                               *
     *                                                                     *
     * We give all the origin of all the inner with objects the same       *
     * beginning location as the outermost one, which is the beginning of  *
     * the "with" token, If depth > 0, then beginLoc is the that location. *
     * Its value is ignored if depth = 0.  This results in all the inner   *
     * With objects having the same origin as the outer one.               *
     **********************************************************************/
    {
        PCalLocation begLoc = beginLoc;
        if (depth == 0) {
            GobbleThis("with");
            begLoc = GetLastLocationStart();
            if (cSyntax) {
                GobbleThis("(");
            }
        }
        final AST.With result = new AST.With(pcalParams);
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.var = GetAlgToken();
        result.isEq = GobbleEqualOrIf();
        result.exp = GetExpr();
        if (pSyntax || !PeekAtAlgToken(1).equals(")")) {
            GobbleCommaOrSemicolon();
            /**************************************************************
             * Gobble the ";" or "," ending the <VarEqOrIn>, which may be  *
             * eliminated before a ")" or "do".                            *
             **************************************************************/
        }
        if (result.exp.tokens.size() == 0) {
            ParsingError("Empty with expression at ");
        }
        if (pSyntax && PeekAtAlgToken(1).equals("do")) {
            GobbleThis("do");
            result.Do = GetStmtSeq();
            GobbleThis("end");
            GobbleThis("with");
            GobbleThis(";");
        } else if (cSyntax && PeekAtAlgToken(1).equals(")")) {
            MustGobbleThis(")");
            result.Do = GetCStmt();
        } else {
            result.Do = new ArrayList<>();
            result.Do.add(InnerGetWith(depth + 1, begLoc));
        }
        try {
            result.setOrigin(new Region(begLoc,
                    result.Do.get(result.Do.size() - 1).getOrigin().getEnd()));
        } catch (final IndexOutOfBoundsException e) {
            throw new ParseAlgorithmException("Missing body of with statement", result);
        }
        return result;
    }

    public AST.Assign GetAssign() throws ParseAlgorithmException {
        final AST.Assign result = new AST.Assign(pcalParams);
        result.col = curTokCol[0] + 1;
        result.line = curTokLine[0] + 1;
        /******************************************************************
         * We use the fact here that this method is called after           *
         * PeekAtAlgToken(1), so LAT[0] contains the next token.           *
         ******************************************************************/
        result.ass = new ArrayList<>();
        result.ass.add(GetSingleAssign());
        while (PeekAtAlgToken(1).equals("||")) {
            @SuppressWarnings("unused") final String throwAway = GetAlgToken();
            try {
                result.ass.add(GetSingleAssign());
            } catch (final ParseAlgorithmException e) {
                ParsingError("Bad assignment statement at ");
            }
        }
        GobbleThis(";");
        final AST firstAssign = result.ass.get(0);
        final AST lastAssign = result.ass.get(result.ass.size() - 1);
        result.setOrigin(new Region(firstAssign.getOrigin().getBegin(),
                lastAssign.getOrigin().getEnd()));
        return result;
    }

    public AST.SingleAssign GetSingleAssign() throws ParseAlgorithmException {
        final AST.SingleAssign result = new AST.SingleAssign(pcalParams);
        result.col = curTokCol[0] + 1;
        result.line = curTokLine[0] + 1;
        /******************************************************************
         * We use the fact here that this method is called after           *
         * PeekAtAlgToken(1), so LAT[0] contains the next token.           *
         ******************************************************************/
        result.lhs = GetLhs();
        GobbleThis(":=");
        result.rhs = GetExpr();
        if (result.rhs.tokens.size() == 0) {
            ParsingError("Empty right-hand side of assignment at ");
        }
        result.setOrigin(new Region(result.lhs.getOrigin().getBegin(),
                result.rhs.getOrigin().getEnd()));
        return result;
    }

    public AST.Lhs GetLhs() throws ParseAlgorithmException {
        final AST.Lhs result = new AST.Lhs(pcalParams);
        result.col = curTokCol[0] + 1;
        result.line = curTokLine[0] + 1;
        /******************************************************************
         * We use the fact here that this method is called after           *
         * PeekAtAlgToken(1), so LAT[0] contains the next token.           *
         ******************************************************************/
        PCalLocation beginLoc;
        PCalLocation endLoc;
        try {
            result.var = GetAlgToken();

            /**
             * beginning of LHS's region is the beginning of the variable.  Its
             * end is the end of the subscript expression, if there is one, else
             * the end of the variable token.
             */
            beginLoc = GetLastLocationStart();
            endLoc = GetLastLocationEnd();

            result.sub = GetExpr();
        } catch (final ParseAlgorithmException e) {
            throw new ParseAlgorithmException(e.getMessage());
        }
        if (result.sub.getOrigin() != null) {
            endLoc = result.sub.getOrigin().getEnd();
        }
        result.setOrigin(new Region(beginLoc, endLoc));
        return result;
    }

    public AST.PrintS GetPrintS() throws ParseAlgorithmException {
        MustGobbleThis("print");
        final PCalLocation beginLoc = GetLastLocationStart();
        final AST.PrintS result = new AST.PrintS(pcalParams);
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.exp = GetExpr();
        if (result.exp.tokens.size() == 0) {
            ParsingError("Empty expression in print statement at ");
        }
        result.setOrigin(new Region(beginLoc, result.exp.getOrigin().getEnd()));
        GobbleThis(";");
        return result;
    }

    public AST.Assert GetAssert() throws ParseAlgorithmException {
        final AST.Assert result = new AST.Assert(pcalParams);
        MustGobbleThis("assert");
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.exp = GetExpr();
        if (result.exp.tokens.size() == 0) {
            ParsingError("Empty expression in assert statement at ");
        }
        GobbleThis(";");
        result.setOrigin(new Region(new PCalLocation(
                result.line - 1, result.col - 1),
                result.exp.getOrigin().getEnd()));
        return result;
    }

    public AST.Skip GetSkip() throws ParseAlgorithmException {
        final AST.Skip result = new AST.Skip(pcalParams);
        MustGobbleThis("skip");
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.setOrigin(new Region(lastTokLine - 1, lastTokCol - 1, 4));
        GobbleThis(";");
        return result;
    }

    public AST.When GetWhen(final boolean isWhen) throws ParseAlgorithmException
    /**********************************************************************
     * Called with isWhen = true for a "when"                              *
     *                    = false for an "await"                           *
     **********************************************************************/
    {
        final AST.When result = new AST.When(pcalParams);
        if (isWhen) {
            MustGobbleThis("when");
        } else {
            MustGobbleThis("await");
        }
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.exp = GetExpr();
        result.setOrigin(new Region(new PCalLocation(
                result.line - 1, result.col - 1),
                result.exp.getOrigin().getEnd()));
        if (result.exp.tokens.size() == 0) {
            ParsingError("Empty expression in when statement at ");
        }
        GobbleThis(";");
        return result;
    }

    public AST.Call GetCall() throws ParseAlgorithmException {
        MustGobbleThis("call");
        final AST.Call result = new AST.Call(pcalParams);
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.to = GetAlgToken();
        GobbleThis("(");
        result.args = new ArrayList<>();
        boolean moreArgs = (PeekPastAlgToken(0).charAt(0) != ')');
        while (moreArgs) {
            result.args.add(GetExpr());
            if (result.args.get(result.args.size() - 1).tokens.size() == 0) {
                ParsingError("Empty argument in call statement at ");
            }
            if (!PeekAtAlgToken(1).equals(")")) {
                GobbleThis(",");
            } else {
                moreArgs = false;
            }
        }
        GobbleThis(")");
        result.setOrigin(new Region(new PCalLocation(result.line - 1, result.col - 1),
                new PCalLocation(lastTokLine - 1, lastTokCol)));
        // token ")" has width 1.
        GobbleThis(";");
        /*
         * Add the called procedure's name to proceduresCalled if it
         * is not already in it.
         */
        int i = 0;
        while ((i < proceduresCalled.size())
                && !result.to.equals(proceduresCalled.get(i))) {
            i++;
        }
        if (i == proceduresCalled.size()) {
            proceduresCalled.add(result.to);
        }
        return result;
    }

    public AST.Return GetReturn() throws ParseAlgorithmException
    /**********************************************************************
     * Note: GetReturn should not complain if the return is not inside a   *
     * procedure because it could be in a macro that is called only from   *
     * inside a procedure.                                                 *
     **********************************************************************/
    {
        final AST.Return result = new AST.Return(pcalParams);
        MustGobbleThis("return");
        result.setOrigin(new Region(GetLastLocationStart(), GetLastLocationEnd()));
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.from = currentProcedure;
        result.setOrigin(new Region(lastTokLine - 1, lastTokCol - 1, 6));
        GobbleThis(";");
        return result;
    }

    public AST GetCallOrCallReturnOrCallGoto() throws ParseAlgorithmException
    /**********************************************************************
     * Note: should not complain if it finds a return that is not inside   *
     * a procedure because it could be in a macro that is called only      *
     * from inside a procedure.                                            *
     **********************************************************************/
    {
        final AST.Call theCall = GetCall();
        if (PeekAtAlgToken(1).equals("return")) {
            MustGobbleThis("return");
            final PCalLocation end = new PCalLocation(lastTokLine - 1, lastTokCol + 5);
            GobbleThis(";");
            final AST.CallReturn result = new AST.CallReturn(pcalParams);
            result.col = theCall.col;
            result.line = theCall.line;
            result.to = theCall.to;
            result.from = currentProcedure;
            result.args = theCall.args;
            result.setOrigin(new Region(theCall.getOrigin().getBegin(), end));
            return result;
        } else if (PeekAtAlgToken(1).equals("goto")) {
            MustGobbleThis("goto");
            final AST.CallGoto result = new AST.CallGoto(pcalParams);
            result.col = theCall.col;
            result.line = theCall.line;
            result.to = theCall.to;
            result.after = GetAlgToken();
            result.args = theCall.args;
            final PCalLocation end = new PCalLocation(lastTokLine - 1, lastTokCol - 1 + result.to.length());
            result.setOrigin(new Region(theCall.getOrigin().getBegin(), end));
            gotoUsed = true;
            if (result.to.equals("Done") || result.to.equals("\"Done\"")) {
                gotoDoneUsed = true;
            }
            GobbleThis(";");
            return result;
        } else {
            return theCall;
        }
    }

    public AST.Goto GetGoto() throws ParseAlgorithmException {
        MustGobbleThis("goto");
        final AST.Goto result = new AST.Goto(pcalParams);
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.to = GetAlgToken();
        result.setOrigin(new Region(new PCalLocation(result.line - 1, result.col - 1),
                new PCalLocation(lastTokLine - 1, lastTokCol - 1 + result.to.length())));
        gotoUsed = true;
        // The translator accepts `goto "Done"' and treats it like
        // `goto Done'.  Testing reveals that the outer
        // parentheses seem to be removed before we get here, but I
        // don't trust my tests, so let's check for both.
        if (result.to.equals("Done") || result.to.equals("\"Done\"")) {
            gotoDoneUsed = true;
        }
        GobbleThis(";");
        return result;
    }

    /**
     * GetMacro changed by LL on 14 July 2011 to take the vector of macros
     * as an argument that it passes to ExpandMacrosInStmtSeq.  (Previously,
     * it had passed an empty vector.)  This allows macros to be called inside
     * previously declared macros.  I don't remember why this wasn't done
     * originally, instead of not allowing macros to be called inside macros.
     * I'm afraid that there was a reason that will appear later.  For that reason,
     * the original GetMacro procedure is contained in the comments above.  To
     * back out of this change, just remove the argument from the one call
     * of GetMacro, and change the error message generated in
     * ExpandMacroCall.
     */
    public AST.Macro GetMacro(final ArrayList<Macro> macros) throws ParseAlgorithmException
    /**********************************************************************
     * This method was largely copied from GetProcedure.                   *
     **********************************************************************/
    {
        final AST.Macro result = new AST.Macro(pcalParams);
        inGetMacro = true;
        MustGobbleThis("macro");
        final PCalLocation beginLoc = GetLastLocationStart();
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.name = GetAlgToken();
        GobbleThis("(");
        result.params = new ArrayList<>();
        boolean lookForComma = false;
        while (!PeekAtAlgToken(1).equals(")")) {
            if (lookForComma) {
                GobbleThis(",");
            }
            result.params.add(GetAlgToken());
            lookForComma = true;
        }
        MustGobbleThis(")");
        GobbleBeginOrLeftBrace();
        result.body = GetStmtSeq();
        GobbleEndOrRightBrace("macro");
        result.setOrigin(new Region(beginLoc, GetLastLocationEnd()));
        if (PeekAtAlgToken(1).equals(";")) {
            @SuppressWarnings("unused") final String tok = GetAlgToken();
        }

        ExpandMacrosInStmtSeq(result.body, macros);

        inGetMacro = false;
        return result;
    }

    public AST.MacroCall GetMacroCall() throws ParseAlgorithmException {
        final AST.MacroCall result = new AST.MacroCall(pcalParams);
        result.name = GetAlgToken();
        final PCalLocation beginLoc = GetLastLocationStart();
        result.col = lastTokCol;
        result.line = lastTokLine;
        MustGobbleThis("(");
        result.args = new ArrayList<>();
        boolean moreArgs = (PeekPastAlgToken(0).charAt(0) != ')');
        while (moreArgs) {
            result.args.add(GetExpr());
            if (result.args.get(result.args.size() - 1).tokens.size() == 0) {
                ParsingError("Empty argument in call statement at ");
            }
            if (!PeekAtAlgToken(1).equals(")")) {
                GobbleThis(",");
            } else {
                moreArgs = false;
            }
        }
        GobbleThis(")");
        result.setOrigin(new Region(beginLoc, GetLastLocationEnd()));
        GobbleThis(";");
        return result;
    }

    /***************************************************************************
     *                          NEW METHODS ADDED Mar 2006
     * @throws ParseAlgorithmException *
     ***************************************************************************/

    public void AddLabelsToStmtSeq(final ArrayList<AST> stmtseq) throws ParseAlgorithmException {
        InnerAddLabels(stmtseq,
                true,            // firstLabeled
                false,           // inWith
                new ArrayList<>(),    // inAssigned = {}
                new ArrayList<>());  // outAssigned
    }

    /***************************************************************************
     * InnerAddLabels is the recursive procedure used to perform the work of    *
     * AddLabelsToStmtSeq.  It returns the value false if the new value of      *
     * stmtseq has no call or return statements and no labels; otherwise it     *
     * returns true.  The return value generally indicates if the calling       *
     * procedure needs to add a label to some following statement.              *
     *                                                                          *
     ***************************************************************************/
    public boolean InnerAddLabels(
            final ArrayList<AST> stmtseq,
            /********************************************************************
             * The sequence of statements to which labels are to be added.       *
             ********************************************************************/
            final boolean firstLabeled,
            /********************************************************************
             * True iff the first statement of the sequence needs a label.       *
             ********************************************************************/
            final boolean inWith,
            /********************************************************************
             * True iff stmtseq occurs within a `with' statement.                *
             ********************************************************************/
            final ArrayList<String> inAssigned,
            /********************************************************************
             * The set of variables to which assignments have been made in the   *
             * current step before executing stmtseq.  When calling              *
             * InnerAddLabels for an outermost `with', this will be set to the   *
             * empty set.                                                        *
             ********************************************************************/
            final ArrayList<String> outAssigned) throws ParseAlgorithmException
    /********************************************************************
     * This is a call-by-reference argument used to return the set of    *
     * variables to which values have been assigned in the current step  *
     * upon completing this sequence of statements.  It need not be a    *
     * superset of vlbsAssigned if there could be a label inside         *
     * stmtseq that starts a new step--which is the case if inWith =     *
     * false.                                                            *
     ********************************************************************/
    {
        int i = 0;


        /********************************************************************
         * Initialize outAssigned, outWithAssigned                           *
         ********************************************************************/
        Copy(inAssigned, outAssigned);

        boolean nextStepNeedsLabel = firstLabeled;
        /******************************************************************
         * True iff the next step requires a label--e.g., because the      *
         * previous step is a return or an if containing a label.  It is   *
         * also the value returned by the entire procedure.                *
         ******************************************************************/

        boolean hadOrAddedLabel = false;
        /******************************************************************
         * True iff a label has been found or added somewhere inside       *
         * stmtseq.                                                        *
         ******************************************************************/

        while (i < stmtseq.size()) {
            final AST stmt = stmtseq.get(i);
            if (!stmt.lbl.equals("")) {
                hadOrAddedLabel = true;
                outAssigned.clear();
                if (inWith) {
                    throw new ParseAlgorithmException("Label in `with' statement",
                            stmt);
                }
            }
            if (nextStepNeedsLabel) {
                if (inWith) {
                    throw new ParseAlgorithmException(
                            "Statement follows `call' or `return' inside a " +
                                    "`with' statement.",
                            stmt);
                }

                NeedsLabel(stmtseq.get(i));
                nextStepNeedsLabel = false;
                hadOrAddedLabel = true;
                outAssigned.clear();
                /***********************************************************
                 * outAssigned := {}                                        *
                 ***********************************************************/
            }
            if (stmt instanceof AST.LabelIf tstmt) { /************************************************************
             * This is an if statement.                                  *
             *   - Call InnerAddLabels on the the unlabThen and          *
             *     unlabElse fields.                                     *
             *   - Set outAssigned to the union of the values            *
             *     returned by the two calls.                            *
             *   - Set nextStepNeedsLabel to true iff either call        *
             *     returns true.                                         *
             ************************************************************/
                /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
                final ArrayList<String> thenAssigned = new ArrayList<>();
                final ArrayList<String> elseAssigned = new ArrayList<>();
                nextStepNeedsLabel =
                        InnerAddLabels(tstmt.unlabThen,
                                false,             // firstLabeled
                                inWith,            // inWith
                                outAssigned,       // inAssigned = {}
                                thenAssigned);    // outAssigned
                nextStepNeedsLabel =
                        InnerAddLabels(tstmt.unlabElse,
                                false,             // firstLabeled
                                inWith,            // inWith
                                outAssigned,       // inAssigned = {}
                                elseAssigned)      // outAssigned
                                || nextStepNeedsLabel;
// PcalDebug.printVector(outAssigned, "mid outAssigned") ;
                Copy(Union(thenAssigned, elseAssigned), outAssigned);
// PcalDebug.printVector(outAssigned, "pst outAssigned") ;
            } else if (stmt instanceof AST.LabelEither obj) { /************************************************************
             * This is a LabelEither object.  The sequence of its        *
             * clauses' unlabOr fields are handled in much the same way  *
             * as unlabThen and unlabElse fields for a LabelIf object.   *
             ************************************************************/
                /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
                int j = 0;
                final ArrayList<String> newOutAssigned = new ArrayList<>();
                while (j < obj.clauses.size()) {
                    final AST.Clause clause = obj.clauses.get(j);
                    final ArrayList<String> orAssigned = new ArrayList<>();
                    nextStepNeedsLabel =
                            InnerAddLabels(clause.unlabOr,
                                    false,             // firstLabeled
                                    inWith,            // inWith
                                    outAssigned,       // inAssigned = {}
                                    orAssigned)        // outAssigned
                                    || nextStepNeedsLabel;
                    Copy(Union(orAssigned, newOutAssigned), newOutAssigned);
                    j = j + 1;
                }
                Copy(newOutAssigned, outAssigned);
            } else if (stmt instanceof AST.While obj) { /************************************************************
             * This is a while statement.                                *
             *   - Add a label if needed and clear outAssigned.          *
             *   - Call InnerAddLabels on the unlabDo clause.            *
             *   - set nextStepNeedsLabel to false                       *
             ************************************************************/
                /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
                if (inWith) {
                    throw new ParseAlgorithmException(
                            "`while' inside a `with' statement", stmt);
                }
                NeedsLabel(stmt);
                hadOrAddedLabel = true;
                outAssigned.clear();
                final ArrayList<String> newOutAssigned = new ArrayList<>();
                InnerAddLabels(obj.unlabDo,
                        false,             // firstLabeled
                        false,             // inWith
                        outAssigned,       // inAssigned = {}
                        newOutAssigned);  // outAssigned
                /**********************************************************
                 * A label is never needed after a `while' statement       *
                 * because that statement immediately follows the labeled  *
                 * test.                                                   *
                 **********************************************************/
            } else if (stmt instanceof AST.With obj) { /************************************************************
             * This is a with statement.  Apply InnerAddLabels to the    *
             * Do field.  If inWith = false, then this is an outermost   *
             * `with'.  In that case, call with inAssigned = {}, and     *
             * add a label to the statement iff the variables assigned   *
             * within the `with' has nonempty intersection with the      *
             * inAssigned parameter of the current call.                 *
             ************************************************************/
                /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
                final ArrayList<String> newInAssigned = new ArrayList<>();
                if (inWith) {
                    Copy(inAssigned, newInAssigned);
                }
                final ArrayList<String> newOutAssigned = new ArrayList<>();
                nextStepNeedsLabel =
                        InnerAddLabels(obj.Do,
                                false,             // firstLabeled
                                true,              // inWith
                                newInAssigned,     // inAssigned
                                newOutAssigned);  // outAssigned
                Copy(newOutAssigned, outAssigned);
                if (!inWith) { /********************************************************
                 * This is an outermost `with'.                          *
                 ********************************************************/
                    if (!HasEmptyIntersection(inAssigned, outAssigned)) { /****************************************************
                     * This `with' needs a label.                        *
                     ****************************************************/
                        NeedsLabel(stmt);
                        hadOrAddedLabel = true;
                        outAssigned.clear();
                    }
                }
            } else if (stmt instanceof AST.Assign obj) { /************************************************************
             * This is an Assign statement.  Set assignedVbls to the     *
             * set of variables being assigned.  If this has non-empty   *
             * intersection with outAssigned, then statement needs a     *
             * label.  Else add those variables to outAssigned.  Set     *
             * nextStepNeedsLabel false, since there's no a priori       *
             * reason why an assignment needs a label after it.          *
             ************************************************************/

                /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
/************************************************************
 * assignedVbls := the set of variables being assigned.      *
 ************************************************************/
                final ArrayList<String> assignedVbls = new ArrayList<>();
                int j = 0;
                while (j < obj.ass.size()) {
                    final AST.SingleAssign assgn =
                            obj.ass.get(j);
                    final String vbl = assgn.lhs.var;
                    if (!IsIn(vbl, assignedVbls)) {
                        assignedVbls.add(vbl);
                    }
                    j = j + 1;
                }
                if (HasEmptyIntersection(outAssigned, assignedVbls)) {
                    Copy(Union(outAssigned, assignedVbls), outAssigned);
                } else { /********************************************************
                 * Statement needs a label.                              *
                 ********************************************************/
                    if (inWith) {
                        throw new ParseAlgorithmException(
                                "Second assignment to same variable " +
                                        "inside a `with' statement",
                                stmt);
                    }

                    NeedsLabel(stmt);
                    hadOrAddedLabel = true;
                    Copy(assignedVbls, outAssigned);
                }

            } else { /************************************************************
             * Some other statement type.  Set nextStepNeedsLabel and    *
             * set assignedVbls to the set of variables being assigned   *
             * by this statement.  Should set nextStepNeedsLabel to      *
             * true and set assignedVbls to a non-empty set iff this is  *
             * a call, return, callReturn, or callGoto.                  *
             ************************************************************/
                final ArrayList<String> assignedVbls = new ArrayList<>();

                /************************************************************
                 * Set isCallOrReturn true iff this is a call, return,       *
                 * callReturn, or callGoto.  Will set setsPrcdVbls true iff  *
                 * this is a return or callReturn or a call of               *
                 * currentProcedure.                                         *
                 ************************************************************/
                boolean isCallOrReturn = false;
                boolean setsPrcdVbls = false;
                if (stmt instanceof AST.Call obj) {
                    /******************************************************
                     * Sets obj to an alias of stmt of the right type.     *
                     ******************************************************/
                    isCallOrReturn = true;
                    if (obj.to.equals(currentProcedure)) {
                        setsPrcdVbls = true;
                    }
                } else if (stmt instanceof AST.CallGoto obj) {
                    isCallOrReturn = true;
                    if (obj.to.equals(currentProcedure)) {
                        setsPrcdVbls = true;
                    }
                } else if (stmt instanceof AST.Return
                        || stmt instanceof AST.CallReturn
                ) {
                    isCallOrReturn = true;
                    setsPrcdVbls = true;
                }
                // The following "else if" clause was originally missing;
                // It was added on 15 May 2006.
                else if (stmt instanceof AST.Goto obj) {
                    nextStepNeedsLabel = true;
                }
                if (isCallOrReturn) {
                    nextStepNeedsLabel = true;
                    assignedVbls.add("stack");
                    /*******************************************************
                     * A call or return assigns to `stack'.                 *
                     *******************************************************/
                    if (setsPrcdVbls) {
                        int j = 0;
                        while (j < procedures.size()) {
                            final AST.Procedure prcd =
                                    procedures.get(j);
                            int k = 0;
                            while (k < prcd.params.size()) {
                                final AST.PVarDecl decl =
                                        prcd.params.get(k);
                                assignedVbls.add(decl.var);
                                k = k + 1;
                            }
                            k = 0;
                            while (k < prcd.decls.size()) {
                                final AST.PVarDecl decl =
                                        prcd.decls.get(k);
                                assignedVbls.add(decl.var);
                                k = k + 1;
                            }
                            j = j + 1;
                        }
                    }
                }
                if (HasEmptyIntersection(outAssigned, assignedVbls)) {
                    Copy(Union(outAssigned, assignedVbls), outAssigned);
                } else { /********************************************************
                 * Statement needs a label.                              *
                 ********************************************************/
                    if (inWith) {
                        throw new ParseAlgorithmException(
                                "Call or return makes second assignment " +
                                        "to a variable inside a `with' statement",
                                stmt);
                    }
                    NeedsLabel(stmt);
                    hadOrAddedLabel = true;
                    Copy(assignedVbls, outAssigned);
                }

            }

            i = i + 1;
        }
        return hadOrAddedLabel || nextStepNeedsLabel;
    }

    public void NeedsLabel(final AST stmt)
    /**********************************************************************
     * Add a label to statement stmt if it doesn't already have one.  The  *
     * label is PcalParams.LabelRoot concatenated with the next number     *
     * greater than or equal to nextLabelNum for which the resulting       *
     * label has not been typed by the user.                               *
     **********************************************************************/
    {
        if (stmt.lbl.equals("")) {
            String lbl = pcalParams.LabelRoot + nextLabelNum;
            nextLabelNum = nextLabelNum + 1;
            while (allLabels.containsKey(lbl)) {
                lbl = pcalParams.LabelRoot + nextLabelNum;
                nextLabelNum = nextLabelNum + 1;
            }
            stmt.lbl = lbl;
            addedLabels.add(lbl);
            addedLabelsLocs.add(stmt.location());
        }
    }

    /***************************************************************************
     *                   SETS OF STRINGS                                        *
     *                                                                          *
     * Methods for handling sets of strings, where such a set is represented    *
     * as a vector of its elements.                                             *
     ***************************************************************************/
    public boolean IsIn(final String elt, final ArrayList<String> set)
    /**********************************************************************
     * True iff elt is in `set'.  Implemented in a dumb way because it     *
     * should usually be called when it returns false.                     *
     **********************************************************************/
    {
        int i = 0;
        boolean result = false;
        while (i < set.size()) {
            result = result || elt.equals(set.get(i));
            i = i + 1;
        }
        return result;
    }

    public boolean HasEmptyIntersection(final ArrayList<String> S, final ArrayList<String> T)
    /**********************************************************************
     * Returns the value of (S \cap T = {}).  Implemented in a dumb way    *
     * because it should usually be called to return false.                *
     **********************************************************************/
    {
        boolean negResult = false;
        int i = 0;
        while (i < T.size()) {
            negResult = negResult || IsIn(T.get(i), S);
            i = i + 1;
        }
        return !negResult;
    }

    public ArrayList<String> Union(final ArrayList<String> S, final ArrayList<String> T)
    /**********************************************************************
     * Returns S \cup T.                                                   *
     **********************************************************************/
    {
        @SuppressWarnings("unchecked") final ArrayList<String> result = (ArrayList<String>) S.clone();
        int i = 0;
        while (i < T.size()) {
            final String str = T.get(i);
            if (!IsIn(str, result)) {
                result.add(str);
            }
            i = i + 1;
        }
        return result;
    }

    public void Copy(final ArrayList<String> in, final ArrayList<String> out)
    /**********************************************************************
     * Sets the non-null vector `out' to a copy of the non-null vector     *
     * `in'.  Note that `out' is a "call-by-reference" argument, while     *
     * `in' is a "call-by-value" argument.                                 *
     **********************************************************************/
    {
        out.clear();
        int i = 0;
        while (i < in.size()) {
            out.add(in.get(i));
            i = i + 1;
        }
    }

    public ArrayList<AST> MakeLabeledStmtSeq(final ArrayList<AST> stmtseq) throws ParseAlgorithmException
    /**********************************************************************
     * Returns the sequence of <LabeledStmt> objects represented by the    *
     * sequence of <Stmt> objects and their lbl fields.                    *
     **********************************************************************/
    {
        final ArrayList<AST> result = InnerMakeLabeledStmtSeq(stmtseq);
        CheckLabeledStmtSeq(result);
        return result;
    }

    public ArrayList<AST> InnerMakeLabeledStmtSeq(final ArrayList<AST> stmtseq)
    /**********************************************************************
     * This does the real work of MakeLabeledStmtSeq.  It is made a        *
     * separate procedure to avoid calling ClassifyStmtSeq with every      *
     * recursive call.                                                     *
     **********************************************************************/
    {
        final ArrayList<AST> result = new ArrayList<>();
        int nextStmt = 0;
        while (nextStmt < stmtseq.size()) {
            final AST.LabeledStmt lstmt = new AST.LabeledStmt(pcalParams);
            AST stmt = stmtseq.get(nextStmt);
            /**************************************************************
             * lstmt is the current <LabeledStmt> being constructed, and   *
             * stmt is the next <Stmt> in stmtseq.                         *
             **************************************************************/

            /****************************************************************
             * Set the location of lstmt.                                    *
             ****************************************************************/
            lstmt.col = stmt.col;
            lstmt.line = stmt.line;
            lstmt.macroCol = stmt.macroCol;
            lstmt.macroLine = stmt.macroLine;
            PcalDebug.Assert(!stmt.lbl.equals(""),
                    "Missing Label in MakeLabeledStmtSeq");

            /****************************************************************
             * Set its label.                                                *
             ****************************************************************/
            lstmt.label = stmt.lbl;

            if (stmt.lbl.equals("")) {
                Debug.ReportBug(
                        "ParseAlgorithmInnerMakeLabeledStmtSeq found null label starting labeled stmt seq");
            }

            lstmt.stmts = new ArrayList<>();
            PCalLocation lstmtBegin = null;
            if (!stmt.lbl.equals("")) {
                lstmtBegin = stmt.lblLocation;
            }

            /****************************************************************
             * lstmt.stmts is obtained from the sequence of <Stmt>s          *
             * consisting of stmt and all immediately following unlabeled    *
             * statements in stmtseq.                                        *
             ****************************************************************/
            boolean firstTime = true;
            while ((nextStmt < stmtseq.size())
                    && (firstTime
                    || stmt.lbl.equals(""))) {
                firstTime = false;
                lstmt.stmts.add(stmt);
                nextStmt = nextStmt + 1;
                if (nextStmt < stmtseq.size()) {
                    stmt = stmtseq.get(nextStmt);
                }
            }
            FixStmtSeq(lstmt.stmts);
            final int numberOfStmts = lstmt.stmts.size();
            if (numberOfStmts == 0) {
                Debug.ReportBug(
                        "Found empty statement sequence in InnerMakeLabeledStmtSeq");
            }

            if (lstmtBegin == null) {
                lstmtBegin = lstmt.stmts.get(0).getOrigin().getBegin();
            }
            final PCalLocation lstmtEnd = lstmt.stmts.get(numberOfStmts - 1)
                    .getOrigin().getEnd();
            lstmt.setOrigin(new Region(lstmtBegin, lstmtEnd));
            result.add(lstmt);
        }
        return result;
    }

    public void FixStmtSeq(final ArrayList<AST> stmtseq)
    /**********************************************************************
     * stmtseq is a sequence of statement objects that are produced by     *
     * GetStmtSeq.  This procedure expands the substatements within each   *
     * LabelIf, LabelEither, and While object in stmtseq.  For a LabelIf,  *
     * this removes the labeled statements from the unlabThen and          *
     * unlabElse sequences and puts them in labThen and labElse.           *
     **********************************************************************/
    {
        int i = 0;
        while (i < stmtseq.size()) {
            final AST stmt = stmtseq.get(i);
            if (stmt instanceof AST.LabelIf obj) { /************************************************************
             * This is an if statement.  Set the unlabThen field to the  *
             * result of calling FixStmtSeq on the prefix of its         *
             * current value consisting of unlabeled statements.  Set    *
             * labThen to the sequence of labeled statement obtained by  *
             * calling InnerMakeLabeledStmtSeq on the rest of the        *
             * statement sequence.                                       *
             ************************************************************/
                /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
                ArrayList<AST> curr = obj.unlabThen;
                obj.unlabThen = new ArrayList<>();
                while ((curr.size() > 0)
                        && curr.get(0).lbl.equals("")) {
                    obj.unlabThen.add(curr.get(0));
                    curr.remove(0);
                }
                FixStmtSeq(obj.unlabThen);
                obj.labThen = InnerMakeLabeledStmtSeq(curr);
                /********************************************************
                 * Set the unlabElse and labElse fields in an analogous  *
                 * fashion.                                              *
                 ********************************************************/
                curr = obj.unlabElse;
                obj.unlabElse = new ArrayList<>();
                while ((curr.size() > 0)
                        && curr.get(0).lbl.equals("")) {
                    obj.unlabElse.add(curr.get(0));
                    curr.remove(0);
                }
                FixStmtSeq(obj.unlabElse);
                obj.labElse = InnerMakeLabeledStmtSeq(curr);
            } else if (stmt instanceof AST.LabelEither obj) { /************************************************************
             * This is a LabelEither object.  For each `or' clause, set  *
             * the unlabDo and labDo fields in the same way as the       *
             * unlabThen and labThen fields for a LabelIf object.        *
             ************************************************************/
                /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
                int j = 0;
                while (j < obj.clauses.size()) {
                    final AST.Clause clause = obj.clauses.get(j);
                    final ArrayList<AST> curr = clause.unlabOr;
                    clause.unlabOr = new ArrayList<>();
                    while ((curr.size() > 0)
                            && curr.get(0).lbl.equals("")) {
                        clause.unlabOr.add(curr.get(0));
                        curr.remove(0);
                    }
                    FixStmtSeq(clause.unlabOr);
                    clause.labOr = InnerMakeLabeledStmtSeq(curr);
                    j = j + 1;
                }

            } else if (stmt instanceof AST.While obj) { /********************************************************
             * This is a while statement.  Set the unlabDo field to  *
             * the prefix of its current value consisting of         *
             * unlabeled statements.  Set labDo to the sequence of   *
             * labeled statement obtained by calling                 *
             * InnerMakeLabeledStmtSeq on the rest of the statement  *
             * sequence.                                             *
             ********************************************************/
                /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
                final ArrayList<AST> curr = obj.unlabDo;
                obj.unlabDo = new ArrayList<>();
                while ((curr.size() > 0)
                        && curr.get(0).lbl.equals("")) {
                    obj.unlabDo.add(curr.get(0));
                    curr.remove(0);
                }
                FixStmtSeq(obj.unlabDo);
                obj.labDo = InnerMakeLabeledStmtSeq(curr);
            }
            i = i + 1;
        }
    }

    /***************************************************************************
     *                    CHECKING AND FIXING THE AST                           *
     *                                                                          *
     * Methods for checking the AST constructed from the simplified grammar,    *
     * converting <LabeledIf> nodes to <If> nodes where appropriate, and        *
     * checking that the AST obeys the actual grammar contained in the +CAL     *
     * document (so the rules for where labels can appear are satisfied).
     * @throws ParseAlgorithmException *
     ***************************************************************************/
    public void CheckLabeledStmtSeq(final ArrayList<AST> stmtseq) throws ParseAlgorithmException {
        int i = 0;
        while (i < stmtseq.size()) {
            final AST.LabeledStmt stmt = (AST.LabeledStmt) stmtseq.get(i);
            @SuppressWarnings("unused") final int ignore = ClassifyStmtSeq(stmt.stmts);
            i = i + 1;
        }
    }

    public int ClassifyStmtSeq(final ArrayList<AST> stmtseq) throws ParseAlgorithmException
    /**********************************************************************
     * ArrayList stmtseq must be a vector of <Stmt>s.  This method returns    *
     *                                                                     *
     *    0 : If stmtseq contains no call, return, goto or labeled         *
     *        statement nested within any of its statements.               *
     *                                                                     *
     *    1 : If stmtseq contains a call, return, or goto  but no labeled  *
     *        statement.                                                   *
     *                                                                     *
     *    2 : If stmtseq contains a labeled statement.                     *
     *                                                                     *
     * It checks that any calls, returns, gotos, or inner labeled          *
     * statements come where they belong, and it converts LabelIf and      *
     * LabelEither objects to If and Either objects where appropriate.     *
     **********************************************************************/
    {
        int i = 0;
        int result = 0;
        while (i < stmtseq.size()) {
            AST node = stmtseq.get(i);
            if (node instanceof AST.LabelIf ifNode) {
                result = ClassifyIf(ifNode);
                if (result < 2) {
                    final AST.If newIf = new AST.If(pcalParams);
                    newIf.test = ifNode.test;
                    newIf.Then = ifNode.unlabThen;
                    newIf.Else = ifNode.unlabElse;
                    newIf.setOrigin(ifNode.getOrigin());
                    stmtseq.set(i, newIf);
                }
            } else if (node instanceof AST.LabelEither eitherNode) {
                result = ClassifyEither(eitherNode);
                if (result < 2) {
                    final AST.Either newEither = new AST.Either(pcalParams);
                    newEither.ors = new ArrayList<>();
                    int j = 0;
                    while (j < eitherNode.clauses.size()) {
                        newEither.ors.add(
                                eitherNode.clauses.get(j).unlabOr);
                        j = j + 1;
                    }
                    newEither.setOrigin(eitherNode.getOrigin());
                    stmtseq.set(i, newEither);
                }
            } else if (node instanceof AST.With obj) {
                result = ClassifyStmtSeq(obj.Do);
                if (result == 2) {
                    throw new ParseAlgorithmException(
                            "with statement at " + node.location() +
                                    " contains a labeled statement");
                }
            } else if (node instanceof AST.While obj) {
                if (i != 0) {
                    PcalDebug.ReportBug(
                            "this.ClassifyStmtSeq encountered `while'" +
                                    " not at beginning of StmtSeq.");
                }
                @SuppressWarnings("unused") final int ignore = ClassifyStmtSeq(obj.unlabDo);
                CheckLabeledStmtSeq(obj.labDo);
            } else if (node instanceof AST.Call) {
                if (!((i < stmtseq.size() - 1)
                        && (stmtseq.get(
                        i + 1) instanceof AST.Return)
                )
                ) {
                    result = 1;
                }
            } else if ((node instanceof AST.Return)
                    || (node instanceof AST.CallReturn)
            ) {
                if (currentProcedure == null) {
                    throw new ParseAlgorithmException(
                            "return statement not in a procedure at "
                                    + node.location());
                }
                result = 1;
            } else if (node instanceof AST.Goto
                    || node instanceof AST.CallGoto
            ) {
                result = 1;
            } else if (!(node instanceof AST.Assign
                    || node instanceof AST.When
                    || node instanceof AST.PrintS
                    || node instanceof AST.Assert
                    || node instanceof AST.Skip
                    || node instanceof AST.MacroCall)
            ) {
                PcalDebug.ReportBug(
                        "this.ClassifyStmtSeq encountered the unexpected" +
                                " statement type " + node.getClass());
            }
            if (result > 0) {
                if (i == stmtseq.size() - 1) {
                    return result;
                } else {
                    node = stmtseq.get(i + 1);
                    PcalDebug.ReportBug(
                            "Translator discovered later than it should have " +
                                    " that\n  " +
                                    "Statement at " + node.location() +
                                    " must have a label");
                }
            }
            i = i + 1;
        }
        return result;
    }

    public int ClassifyIf(final AST.LabelIf node) throws ParseAlgorithmException
    /**********************************************************************
     * Checks a LabelIf node and returns the kind of nonterminal of the    *
     * real BNF grammar with the following encoding it should really be,   *
     * as follows                                                          *
     *                                                                     *
     *     0 : <If>                                                        *
     *     1 : <FinalIf>                                                   *
     *     2 : <LabelIf>                                                   *
     *                                                                     *
     * It is a <LabelIf> iff it contains a labeled statement somewhere     *
     * within it (possibly nested inside another <If>.                     *
     **********************************************************************/
    { /********************************************************************
     * Do checking in order that finds first error in the algorithm      *
     * first.                                                            *
     ********************************************************************/
        final int thenClass = ClassifyStmtSeq(node.unlabThen);
        boolean isLabeled = false;
        if (node.labThen.size() > 0) {
            isLabeled = true;
            CheckLabeledStmtSeq(node.labThen);
        }
        final int elseClass = ClassifyStmtSeq(node.unlabElse);
        if (node.labElse.size() > 0) {
            isLabeled = true;
            CheckLabeledStmtSeq(node.labElse);
        }
        if (isLabeled
                || (thenClass == 2)
                || (elseClass == 2)) {
            return 2;
        }
        if (thenClass + elseClass > 0) {
            return 1;
        }
        return 0;
    }

    public int ClassifyEither(final AST.LabelEither node) throws ParseAlgorithmException
    /**********************************************************************
     * Checks a LabelEither node and returns the kind of nonterminal of    *
     * the real BNF grammar with the following encoding it should really   *
     * be, as follows                                                      *
     *                                                                     *
     *     0 : <Either>                                                    *
     *     1 : <FinalEither>                                               *
     *     2 : <LabelEither>                                               *
     *                                                                     *
     * It is a <LabelEither> iff it contains a labeled statement           *
     * somewhere within it (possibly nested inside another <Either>.       *
     **********************************************************************/
    { /********************************************************************
     * Do checking in order that finds first error in the algorithm      *
     * first.                                                            *
     ********************************************************************/
        int theClass = 0;
        int i = 0;
        while (i < node.clauses.size()) {
            final AST.Clause currClause = node.clauses.get(i);
            final int unlabClass = ClassifyStmtSeq(currClause.unlabOr);
            if (unlabClass > theClass) {
                theClass = unlabClass;
            }
            if (currClause.labOr.size() > 0) {
                theClass = 2;
                CheckLabeledStmtSeq(currClause.labOr);
            }
            i = i + 1;
        }
        return theClass;
    }

    /***************************************************************************
     *                         MACRO EXPANSION                                  *
     *                                                                          *
     * Methods for expanding macros.
     * @throws ParseAlgorithmException *
     ***************************************************************************/

    public void CheckForDuplicateMacros(final ArrayList<Macro> macros) throws ParseAlgorithmException
    /**********************************************************************
     * Argument macros is a vector of AST.Macro                            *
     **********************************************************************/
    {
        int i = 0;
        while (i < macros.size()) {
            final String namei = macros.get(i).name;
            int j = i + 1;
            while (j < macros.size()) {
                if (namei.equals(macros.get(j).name)) {
                    throw new ParseAlgorithmException(
                            "Multiple definitions of macro name `" + namei + "'");
                }
                j = j + 1;
            }
            i = i + 1;
        }
    }

    public void ExpandMacrosInStmtSeq(final ArrayList<AST> stmtseq, final ArrayList<Macro> macros) throws ParseAlgorithmException
    /**********************************************************************
     * This is called on a sequence stmtseq of statements, before          *
     * MakeLabeledStmtSeq has been called.  Therefore, stmtseq contains    *
     * no AST.If or AST.Either objects, and with empty lab...  fields in   *
     * AST.LabelIf, AST.LabelEither, and AST.while objects.                *
     **********************************************************************/
    {
        int i = 0;
        while (i < stmtseq.size()) {
            final AST node = stmtseq.get(i);
            if (node instanceof AST.LabelIf obj) {
                ExpandMacrosInStmtSeq(obj.unlabThen,
                        macros);
                ExpandMacrosInStmtSeq(obj.unlabElse,
                        macros);
            } else if (node instanceof AST.LabelEither eNode) {
                int j = 0;
                while (j < eNode.clauses.size()) {
                    ExpandMacrosInStmtSeq(
                            eNode.clauses.get(j).unlabOr,
                            macros);
                    j = j + 1;
                }
            } else if (node instanceof AST.With obj) {
                ExpandMacrosInStmtSeq(obj.Do, macros);
            } else if (node instanceof AST.While obj) {
                ExpandMacrosInStmtSeq(obj.unlabDo, macros);
            } else if (node instanceof AST.MacroCall obj) {
                final ArrayList<AST> expansion =
                        ExpandMacroCall(obj, macros);

                stmtseq.remove(i);
                int j = expansion.size();
                while (j > 0) {
                    stmtseq.add(i, expansion.get(j - 1));
                    j = j - 1;
                }
                i = i + expansion.size() - 1;
            }
            i = i + 1;
        }
    }

    public ArrayList<AST> ExpandMacroCall(final AST.MacroCall call, final ArrayList<Macro> macros) throws ParseAlgorithmException { // Set macroDef to the Macro object
        AST.Macro macroDef = null;
        int i = 0;
        while (i < macros.size()) {
            final AST.Macro md = macros.get(i);
            if (md.name.equals(call.name)) {
                macroDef = md;
            }
            i = i + 1;
        }

        if (macroDef == null) {
            throw new ParseAlgorithmException("Macro " + call.name +
                    // This error message changed by LL on 14 July 2011 when GetMacro was
                    // changed to allow macros to call other macros.  Change back the message
                    // to back out of that other change.
                    //
                    //  " undefined or called inside a macro definition,\n    at "
                    " undefined,\n    at " + call.location());
        }

        final int numOfArgs = call.args.size();
        if (macroDef.params.size() != numOfArgs) {
            throw new ParseAlgorithmException("Macro " + call.name +
                    " called with wrong number of arguments at "
                    + "\n    " + call.location());
        }
        final ArrayList<AST> result = SubstituteInStmtSeq(macroDef.body,
                call.args,
                macroDef.params,
                call.line,
                call.col);
        /*
         * Copy lbl and lblOrigin fields of call to first statement of expansion.
         * Set the macroOriginBegin and macroOriginEnd of the first and last
         * statements.  Note that either (or both) of those fields could already
         * be set if the statement arose from the expansion of a macro in the
         * current macro.  However, since the PcalTLAGen.GenLabeledStmt method
         * wants those fields set from the macro call in the main body of the
         * PlusCal algorithm, which is the last one expanded in a sequence
         * of macros calling macros.
         */
        if (result.size() > 0) {
            final AST first = result.get(0);
            first.lbl = call.lbl;
            first.lblLocation = call.lblLocation;
            final Region callOrigin = call.getOrigin();
            if (callOrigin != null) {
                first.macroOriginBegin = callOrigin.getBegin();
                final AST last = result.get(result.size() - 1);
                last.macroOriginEnd = callOrigin.getEnd();
            }
        }

        return result;
    }

    public ArrayList<AST> SubstituteInLabeledStmtSeq(
            final ArrayList<AST> stmts,  // of AST.LabeledStmt
            final ArrayList<TLAExpr> args,   // of TLAExpr
            final ArrayList<String> params) throws ParseAlgorithmException // of String
    {
        final ArrayList<AST> result = new ArrayList<>();
        int i = 0;
        while (i < stmts.size()) {
            result.add(SubstituteInLabeledStmt(
                    (AST.LabeledStmt) stmts.get(i),
                    args,
                    params));
            i = i + 1;
        }

        return result;
    }

    public AST.LabeledStmt SubstituteInLabeledStmt(
            final AST.LabeledStmt stmt,
            final ArrayList<TLAExpr> args,   // of TLAExpr
            final ArrayList<String> params) throws ParseAlgorithmException // of String
    {
        final AST.LabeledStmt result = new AST.LabeledStmt(pcalParams);
        result.label = stmt.label;
        result.stmts = SubstituteInStmtSeq(stmt.stmts, args, params, -1, 0);
        result.setOrigin(stmt.getOrigin());
        return result;
    }

    /***************************************************************************
     * The SubstituteInStmtSeq method does substitutions only in the class of   *
     * statements found in the body of a macro.  However, it is simple to       *
     * define a SubstituteInLabeledStmtSeq method and enhance                   *
     * SubstituteInStmtSeq so the SubstituteInLabeledStmtSeq can be used to do  *
     * arbitrary substitutions in the body of a process or uniprocess           *
     * algorithm.                                                               *
     ***************************************************************************/
    public ArrayList<AST> SubstituteInStmtSeq(final ArrayList<AST> stmts, // of AST
                                              final ArrayList<TLAExpr> args,   // of TLAExpr
                                              final ArrayList<String> params, // of String
                                              final int macroLine,
                                              final int macroCol) throws ParseAlgorithmException
    /*********************************************************************
     * A vector of new AST nodes obtained from the statements in stmts    *
     * by substituting the expressions in args for the corresponding      *
     * parameters in params inside the expansion of a macro call at line  *
     * macroLine, column macroCol, where macroLine = -1 if this is not    *
     * being called because of a macro expansion.                         *
     *********************************************************************/
    {
        final ArrayList<AST> result = new ArrayList<>();
        int i = 0;
        while (i < stmts.size()) {
            result.add(SubstituteInStmt(stmts.get(i),
                    args,
                    params,
                    macroLine,
                    macroCol));
            i = i + 1;
        }

        return result;
    }

    @SuppressWarnings("unchecked")
    public AST SubstituteInStmt(final AST stmt,
                                final ArrayList<TLAExpr> args,   // of TLAExpr
                                final ArrayList<String> params, // of String
                                final int macroLine,
                                final int macroCol) throws ParseAlgorithmException
    /*********************************************************************
     * A new AST node obtained from statement stmt by substituting the    *
     * expressions in args for the corresponding parameters in params     *
     * inside the expansion of a macro call at line macroLine, column     *
     * macroCol, where macroLine = -1 if this is not being called during  *
     * macro expansion.                                                   *
     *                                                                    *
     * Note that the origin of the new node should be the same as that of *
     * the original.                                                      *
     *********************************************************************/
    { /*******************************************************************
     * The following statements are ones that may appear in a macro     *
     * definition body.                                                 *
     *******************************************************************/
        try {
            if (stmt instanceof AST.Assign tstmt) {
                final AST.Assign result = new AST.Assign(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                int i = 0;
                result.ass = new ArrayList<>();
                while (i < tstmt.ass.size()) {
                    result.ass.add(
                            SubstituteInSingleAssign(
                                    tstmt.ass.get(i),
                                    args, params, macroLine, macroCol));
                    i = i + 1;
                }
                return result;
            }

            if (stmt instanceof AST.If tstmt) {
                final AST.If result = new AST.If(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }

                result.test = tstmt.test.cloneAndNormalize();
                result.test.substituteForAll(args, params);

                result.Then = SubstituteInStmtSeq(
                        tstmt.Then, args, params, macroLine, macroCol);

                result.Else = SubstituteInStmtSeq(
                        tstmt.Else, args, params, macroLine, macroCol);

                return result;
            }

            if (stmt instanceof AST.Either tstmt) {
                final AST.Either result = new AST.Either(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                result.ors = new ArrayList<>();
                int i = 0;
                while (i < tstmt.ors.size()) {
                    result.ors.add(
                            SubstituteInStmtSeq(
                                    (ArrayList<AST>) tstmt.ors.get(i),
                                    args, params, macroLine, macroCol));
                    i = i + 1;
                }

                return result;
            }

            if (stmt instanceof AST.With tstmt) {
                final AST.With result = new AST.With(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }

                result.var = tstmt.var;
                result.isEq = tstmt.isEq;
                result.exp = tstmt.exp.cloneAndNormalize();
                result.exp.substituteForAll(args, params);
                result.Do = SubstituteInStmtSeq(
                        tstmt.Do, args, params, macroLine, macroCol);
                return result;
            }

            if (stmt instanceof AST.When tstmt) {
                final AST.When result = new AST.When(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }

                result.exp = tstmt.exp.cloneAndNormalize();
                result.exp.substituteForAll(args, params);
                return result;
            }

            if (stmt instanceof AST.Assert tstmt) {
                final AST.Assert result = new AST.Assert(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }

                result.exp = tstmt.exp.cloneAndNormalize();
                result.exp.substituteForAll(args, params);
                return result;
            }


            if (stmt instanceof AST.Skip tstmt) {
                final AST.Skip result = new AST.Skip(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                return result;
            }


            if (stmt instanceof AST.PrintS tstmt) {
                final AST.PrintS result = new AST.PrintS(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                result.exp = tstmt.exp.cloneAndNormalize();
                result.exp.substituteForAll(args, params);
                return result;
            }

            /*******************************************************************
             * The following statements are ones that may not appear in a macro *
             * definition body.                                                 *
             *******************************************************************/
            if (stmt instanceof AST.While tstmt) {
                final AST.While result = new AST.While(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                result.test = tstmt.test.cloneAndNormalize();
                result.test.substituteForAll(args, params);
                result.unlabDo =
                        SubstituteInStmtSeq(tstmt.unlabDo,
                                args,
                                params,
                                macroLine,
                                macroCol);
                result.labDo =
                        SubstituteInLabeledStmtSeq(tstmt.labDo,
                                args,
                                params);

                return result;
            }

            if (stmt instanceof AST.LabelIf tstmt) {
                final AST.LabelIf result = new AST.LabelIf(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                result.test = tstmt.test.cloneAndNormalize();
                result.test.substituteForAll(args, params);
                result.unlabThen =
                        SubstituteInStmtSeq(tstmt.unlabThen,
                                args,
                                params,
                                macroLine,
                                macroCol);
                result.labThen =
                        SubstituteInLabeledStmtSeq(tstmt.labThen,
                                args,
                                params);
                result.unlabElse =
                        SubstituteInStmtSeq(tstmt.unlabElse,
                                args,
                                params,
                                macroLine,
                                macroCol);
                result.labElse =
                        SubstituteInLabeledStmtSeq(tstmt.labElse,
                                args,
                                params);

                return result;
            }

            if (stmt instanceof AST.LabelEither tstmt) {
                final AST.LabelEither result = new AST.LabelEither(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                result.clauses = new ArrayList<>();
                int i = 0;
                while (i < tstmt.clauses.size()) {
                    final AST.Clause oldClause =
                            tstmt.clauses.get(i);
                    final AST.Clause newClause = new AST.Clause(pcalParams);
                    newClause.setOrigin(oldClause.getOrigin());
                    newClause.labOr = SubstituteInLabeledStmtSeq(
                            oldClause.labOr,
                            args,
                            params);
                    newClause.unlabOr = SubstituteInStmtSeq(
                            oldClause.unlabOr,
                            args,
                            params,
                            macroLine,
                            macroCol);
                    result.clauses.add(newClause);
                    i = i + 1;
                }
                return result;
            }

            if (stmt instanceof AST.Call tstmt) {
                final AST.Call result = new AST.Call(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                result.to = tstmt.to;
                result.returnTo = tstmt.returnTo;
                result.args =
                        TLAExpr.SeqSubstituteForAll(tstmt.args, args, params);
                return result;
            }

            if (stmt instanceof AST.Return tstmt) {
                final AST.Return result = new AST.Return(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                result.from = tstmt.from;
                return result;
            }

            if (stmt instanceof AST.CallReturn tstmt) {
                final AST.CallReturn result = new AST.CallReturn(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                result.to = tstmt.to;
                result.from = tstmt.from;
                result.args =
                        TLAExpr.SeqSubstituteForAll(tstmt.args, args, params);
                return result;
            }

            if (stmt instanceof AST.CallGoto tstmt) {
                final AST.CallGoto result = new AST.CallGoto(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                result.to = tstmt.to;
                result.after = tstmt.after;
                result.args =
                        TLAExpr.SeqSubstituteForAll(tstmt.args, args, params);
                return result;
            }

            if (stmt instanceof AST.Goto tstmt) {
                final AST.Goto result = new AST.Goto(pcalParams);
                result.col = tstmt.col;
                result.line = tstmt.line;
                result.macroCol = tstmt.macroCol;
                result.macroLine = tstmt.macroLine;
                result.setOrigin(tstmt.getOrigin());
                if (macroLine > 0) {
                    result.macroLine = macroLine;
                    result.macroCol = macroCol;
                }
                result.to = tstmt.to;
                return result;
            }

            PcalDebug.ReportBug(
                    "Found unexpected statement type in macro at" +
                            stmt.location());
            return new AST(pcalParams); // Needed to keep Java from complaining.
        } catch (final UnrecoverableException e) {
            throw new ParseAlgorithmException(e.getMessage());
        }
    }

    public AST.SingleAssign SubstituteInSingleAssign(
            final AST.SingleAssign assgn,
            final ArrayList<TLAExpr> args,   // of TLAExpr
            final ArrayList<String> params, // of String
            final int macroLine,
            final int macroCol) throws ParseAlgorithmException
    /*********************************************************************
     * A new AST.SingleAssign node obtained from assgn by substituting    *
     * the expressions in args for the corresponding parameters in        *
     * params inside the expansion of a macro call at line macroLine,     *
     * column macroCol, where macroLine = -1 if this is not being called  *
     * during macro expansion.                                            *
     *********************************************************************/
    {
        try {
            final AST.SingleAssign result = new AST.SingleAssign(pcalParams);
            result.setOrigin(assgn.getOrigin());
            result.col = assgn.col;
            result.line = assgn.line;
            result.macroCol = assgn.macroCol;
            result.macroLine = assgn.macroLine;
            if (macroLine > 0) {
                result.macroLine = macroLine;
                result.macroCol = macroCol;
            }
            /*******************************************************************
             * Do substitution in right-hand-side expression.                   *
             *******************************************************************/
            result.rhs = assgn.rhs.cloneAndNormalize();
            result.rhs.substituteForAll(args, params);

            result.lhs = new AST.Lhs(pcalParams);
            result.lhs.setOrigin(assgn.getOrigin());
            result.lhs.sub = assgn.lhs.sub;
            /*******************************************************************
             * If there is a subscript on the left-hand-side, substitute in     *
             * it.                                                              *
             *******************************************************************/
            if ((assgn.lhs.sub.tokens != null)
                    && (assgn.lhs.sub.tokens.size() != 0))
            /***************************************************************
             * I'm not sure any more if an AST.SingleAssign representing    *
             * an assignment with no subscript has a null sub field or a    *
             * vector of length 0.                                          *
             ***************************************************************/ {
                result.lhs.sub = assgn.lhs.sub.cloneAndNormalize();
                result.lhs.sub.substituteForAll(args, params);
            }

            /*******************************************************************
             * Do substitution for the variable if necessary.                   *
             *******************************************************************/
            result.lhs.var = assgn.lhs.var;

            int i = 0;
            boolean found = false;
            while ((i < params.size())
                    && !found) {
                if (result.lhs.var.equals(params.get(i))) {
                    found = true;
                } else {
                    i = i + 1;
                }
            }

            if (found) {
                final TLAExpr subForVar = args.get(i);
                final TLAToken varToken = subForVar.tokenAt(new IntPair(0, 0));
                if (varToken.type != TLAToken.IDENT) {
                    throw new ParseAlgorithmException(
                            "Macro expansion substitutes `" + varToken.string +
                                    "' for assignment variable\n    at " + result.location());
                }
                result.lhs.var = varToken.string;

                if (subForVar.stepCoord(new IntPair(0, 0), 1) != null) { /***********************************************************
                 * More than a single token is being substituted for the    *
                 * variable--for example, we may be substituting "x[0]"     *
                 * for "y" in "y[i] := ...".  The rest of the expression    *
                 * must therefore be prepended to the subscript.            *
                 *                                                          *
                 * We first set exprCopy to a clone of the substituting     *
                 * expression with the first token (the one that became     *
                 * the assignment variable) removed.                        *
                 ***********************************************************/
                    final TLAExpr exprCopy = subForVar.cloneAndNormalize();
                    final ArrayList<?> firstLine = exprCopy.tokens.get(0);
                    firstLine.remove(0);
                    exprCopy.normalize();
                    /*********************************************************
                     * We must normalize because the deleted token may be an  *
                     * anchor token, and the deletion might have created an   *
                     * empty first line.                                      *
                     *********************************************************/
                    if ((result.lhs.sub == null)
                            || (result.lhs.sub.tokens.size() == 0))
                    /********************************************************
                     * I'm not sure any more if an AST.SingleAssign          *
                     * representing an assignment with no subscript has a    *
                     * null sub field or a vector of length 0.               *
                     ********************************************************/ { /*******************************************************
                     * There was no subscript in the original statement.    *
                     *******************************************************/
                        result.lhs.sub = exprCopy;
                    } else { /*******************************************************
                     * There was already a subscript, so we must prepend.   *
                     * We don't add any space after the prepended           *
                     * expression because, to be sensible, the existing     *
                     * subscript must begin with "[" or ".".                *
                     *******************************************************/
                        result.lhs.sub.prepend(exprCopy, 0);
                    }
                }
            }
            return result;
        } catch (final TLAExprException e) {
            throw new ParseAlgorithmException(e.getMessage());
        }
    }

    /*************************** UTILITY METHODS ******************************/
//    private String Loc(int line , int col)
//      { return  }
    private void ParsingError(final String msg) throws ParseAlgorithmException {
        throw new ParseAlgorithmException(
                msg + "\n    line " + lastTokLine + ", column " + lastTokCol);
    }

    public void GobbleCommaOrSemicolon() throws ParseAlgorithmException
    /**********************************************************************
     * Equivalent to GobbleThis(",") if the next token is a ",", else to   *
     * GobbleThis(";").                                                    *
     **********************************************************************/
    {
        final String nxt = PeekAtAlgToken(1);
        if (nxt.equals(",")) {
            GobbleThis(",");
        } else {
            GobbleThis(";");
        }
    }

    public void GobbleBeginOrLeftBrace() throws ParseAlgorithmException
    /**********************************************************************
     * Used when expecting a "begin" in the p-syntax or a "{" in the       *
     * c-syntax.  Gobbles is and sets pSyntax or cSyntax.                  *
     **********************************************************************/
    {
        if (pSyntax) {
            GobbleThis("begin");
        } else if (cSyntax) {
            GobbleThis("{");
        } else {
            PcalDebug.ReportBug("Syntax not initialized.");
        }
    }

    public void GobbleEndOrRightBrace(final String str) throws ParseAlgorithmException
    /**********************************************************************
     * Used when expecting an "end str" in the p-syntax or a "}" in the    *
     * c-syntax.                                                           *
     **********************************************************************/
    {
        if (pSyntax) {
            GobbleThis("end");
            GobbleThis(str);
        } else if (cSyntax) {
            GobbleThis("}");
        } else {
            PcalDebug.ReportBug("Bad call of GobbleEndRightBrace");
        }
    }

    public void GobbleThis(final String str) throws ParseAlgorithmException { /********************************************************************
     * If the next token is not str, then report an error.  Otherwise,   *
     * just move past the token.  However, if str is a semicolon and     *
     * the next token indicates that the input is missing an obviously   *
     * unnecessary semicolon, then don't report an error--for example,   *
     * if the next token is "end".  If the missing semicolon should      *
     * really be there--for example, if the user typed "x : = x + 1      *
     * print x", then print a warning message about the missing          *
     * semicolon.  The missing semicolon is innocuous if the next token  *
     * is                                                                *
     *                                                                   *
     *    end  begin  else  elsif  or  macro  procedure  process  define *
     *                                                                   *
     * in the p-syntax or "{" or "}" in the c-syntax.  Since GobbleThis  *
     * can be called before we know which syntax is used, it ignores     *
     * the missing semicolon in either case.                             *
     *                                                                   *
     * It used to produce a warning if the next token is                 *
     *                                                                   *
     *    if  either  while  with  call  return  goto  print  assert     *
     *    skip                                                           *
     *                                                                   *
     * However, in this case the translation could be incorrect because  *
     * the missing ";" could have caused a label to be incorporated as   *
     * part of the previous statement.  So, it produces a missing ";"    *
     * error.  The case is still tested for and a different error        *
     * message produced that might be more helpful.                      *
     ********************************************************************/
        if (str.equals(";")) {
            final String nxt = PeekAtAlgToken(1);
            if (nxt.equals("end")
                    || nxt.equals("begin")
                    || nxt.equals("else")
                    || nxt.equals("elsif")
                    || nxt.equals("or")
                    || nxt.equals("do")
                    || nxt.equals("macro")
                    || nxt.equals("procedure")
                    || nxt.equals("process")
                    || nxt.equals("fair")
                    || nxt.equals("define")
                    || nxt.equals("}")
                    || nxt.equals("{")
            ) {
                return;
            }
            if (nxt.equals("if")
                    || nxt.equals("either")
                    || nxt.equals("while")
                    || nxt.equals("with")
                    || nxt.equals("call")
                    || nxt.equals("return")
                    || nxt.equals("goto")
                    || nxt.equals("print")
                    || nxt.equals("assert")
                    || nxt.equals("skip")
            ) { /************************************************************
             * This was changed from a warning to an error by LL on 28   *
             * Feb 2006 because the translation will be incorrect if     *
             * there is a label following the missing ";".               *
             ************************************************************/
                throw new ParseAlgorithmException("Missing `;' before line " +
                        (curTokLine[0] + 1) +
                        ", column " +
                        (curTokCol[0] + 1));
            }
        }
        final String tok = GetAlgToken();
        if (!tok.equals(str)) {
            ParsingError("Expected \"" + str + "\" but found \""
                    + tok + "\"");
        }
    }

    public void MustGobbleThis(final String str) throws ParseAlgorithmException {
        final String tok;
        try {
            tok = GetAlgToken();
        } catch (final ParseAlgorithmException e) {
            throw new ParseAlgorithmException(e.getMessage());
        }
        if (!tok.equals(str)) {
            ParsingError("Expected \"" + str + "\" but found \"" + tok + "\"");
        }
    }
    /*********************************************************************
     * The column and line number of the last token returned with          *
     * GetAlgToken, where the numbering starts at 1.  The translation      *
     * from Java ordinals to human ordinals occurs when these variables    *
     * are set.                                                            *
     * @throws ParseAlgorithmException *                                   *
     **********************************************************************/

    public boolean GobbleEqualOrIf() throws ParseAlgorithmException
    /**********************************************************************
     * Gobbles the next token, returns true if it is "=", false if it is   *
     * "\in", and reports an error otherwise.                              *
     **********************************************************************/
    {
        final String tok = GetAlgToken();
        if (tok.equals("=")) {
            return true;
        }
        if (tok.equals("\\in")) {
            return false;
        }
        ParsingError("Expected \"=\" or \"\\in\"  but found \""
                + tok + "\"");
        return false; // Never executed, but the compiler needs it.
    }

    /**
     * Returns the PCalLocation object corresponding to the beginning of
     * the last token returned by GetAlgToken or gobbled by a Gobble...
     * method.
     */
    private PCalLocation GetLastLocationStart() {
        return new PCalLocation(lastTokLine - 1, lastTokCol - 1);
    }

    /**
     * Returns the PCalLocation object corresponding to the position to
     * the right of the last token returned by GetAlgToken or gobbled by
     * a Gobble... method.
     */
    private PCalLocation GetLastLocationEnd() {
        return new PCalLocation(lastTokLine - 1, lastTokCol - 1 + lastTokString.length());
    }

    public String GetAlgToken() throws ParseAlgorithmException
    /**********************************************************************
     * Return the next algorithm token.                                      *
     **********************************************************************/
    {
        if (LATsize == 0) {
            charReader.peek();
/***************************************************************************
 * The following bug should have been fixed by the addition of the          *
 * Uncomment method by LL on 18 Feb 2006.                                   *
 *                                                                          *
 *                               BUG                                        *
 *                                                                          *
 * This is the source of the position-reporting bug.  If there's a comment  *
 * between the current position and the beginning of the next non-comment   *
 * token, then charReader.peek() will position the reader at the beginnig   *
 * of the comment.                                                          *
 *                                                                          *
 * One fix is to implement a peek() method that skips over comments.  Such  *
 * a method needs to be implemented in the Tokenize class.  However, that   *
 * requires modifying the actual tokenizing code, whic requires             *
 * understanding it.  A better fix might be to move LAT and LATsize to the  *
 * Tokenize class, so both GetAlgorithmToken and TokenizeExpr get their       *
 * tokens from it.  This would permit a real PeekAtAlgToken method to be    *
 * implemented in the Tokenize class that can be called to look             *
 * arbitrarily far ahead in the token stream without interfering with the   *
 * tokenizing of expressions.  The PcalCharReader's kludgy "peek" method    *
 * would then not be needed.  However, this fix requires modifying a fair   *
 * amount of code.                                                          *
 ***************************************************************************/
            lastTokCol = charReader.getColumnNumber() + 1;
            lastTokLine = charReader.getLineNumber() + 1;
            final String tok;
            try {
                tok = tokenizer.GetAlgorithmToken(charReader);
            } catch (final TokenizerException e) {
                throw new ParseAlgorithmException(e.getMessage());
            }
            lastTokString = tok;
            return tok;
        }
        lastTokCol = curTokCol[0] + 1;
        lastTokLine = curTokLine[0] + 1;
        final String result = LAT[0];
        int i = 1;
        while (i < LATsize) {
            LAT[i - 1] = LAT[i];
            curTokCol[i - 1] = curTokCol[i];
            curTokLine[i - 1] = curTokLine[i];
            i = i + 1;
        }
        LATsize = LATsize - 1;
        lastTokString = result;
        return result;
    }

    public String PeekAtAlgToken(final int tokNum) throws ParseAlgorithmException
    /**********************************************************************
     * This returns the tokNum-th token ahead, but does not actually       *
     * remove any token from the input stream.  PeekAtAlgToken(1) returns  *
     * the next token, PeekAtAlgToken(2) returns the one after that, etc.  *
     **********************************************************************/
    {
        while ((LATsize < tokNum)) { /****************************************************************
         * Move charReader to beginning of next non-space token and get  *
         * line and column numbers.                                      *
         ****************************************************************/

            /****************************************************************
             * Change made 14 January 2009 by LL. Changed call of            *
             * charReader.peek() to this call plus test for end of file to   *
             * correct bug_08_12_12.                                         *
             ****************************************************************/
            if (charReader.peek().equals("\t")) {
                throw new ParseAlgorithmException(
                        "Premature end of file, perhaps because of " +
                                "unclosed comment, near\n" +
                                "    line " + (curTokLine[LATsize] + 1) +
                                ", column " + (curTokCol[LATsize] + 1));
            }
            curTokCol[LATsize] = charReader.getColumnNumber();
            curTokLine[LATsize] = charReader.getLineNumber();
            try {
                LAT[LATsize] = tokenizer.GetAlgorithmToken(charReader);
            } catch (final TokenizerException e) {
                throw new ParseAlgorithmException(e.getMessage());
            }
            LATsize = LATsize + 1;
        }
        return LAT[tokNum - 1];
    }

    public String PeekPastAlgToken(final int tokNum) throws ParseAlgorithmException
    /**********************************************************************
     * This performs and returns the results of a PcalCharReader.peek()    *
     * at the input stream after the tokNum-th token after the current     *
     * one, where tokNum = 0 means from the current logical point in the   *
     * input stream.  This produces an error if tokNum > LATsize, meaning  *
     * that you can't perform this operation at a point before a token     *
     * that has been peeked at using PeekAtAlgToken.                       *
     **********************************************************************/
    {
        if (tokNum < LATsize) {
            PcalDebug.ReportBug("this.PeekPastAlgToken called " +
                    "to peek after a token" +
                    "\n    it has already peeked at");
        }
        while (tokNum > LATsize) {
            try {
                LAT[LATsize] = tokenizer.GetAlgorithmToken(charReader);
            } catch (final TokenizerException e) {
                throw new ParseAlgorithmException(e.getMessage());
            }
            LATsize = LATsize + 1;
        }
        return charReader.peek();
    }


    /***************************************************************************
     *                    The Uncomment Method                                  *
     *                                                                          *
     * Several parsing bugs arose because the peek-ahead kludgery was confused  *
     * by comments.  The simple solution was to remove comments before          *
     * parsing.  The Uncomment method does this.  It is called on a copy of     *
     * the input used only to create the abstract syntax tree, so it doesn't    *
     * matter what it does to anything outside the algorithm.  Therefore, the   *
     * method doesn't bother to try to find the actual end of the algorithm.    *
     * It stops the processing if it finds an unmatched *), since it then       *
     * should be outside the algorithm.                                         *
     *                                                                          *
     * Bug fixed by LL on 28 Feb 2006
     ***************************************************************************/
    public void uncomment(final ArrayList<String> inp,
                          final int begLine,
                          final int begCol) throws ParseAlgorithmException

    /**********************************************************************
     * Replace all (* *) comments by spaces, and delete all \* comments,   *
     * in the string vector inp, starting at line begLine and column       *
     * begCol, and ending with the first unmatched *) .                    *
     *                                                                     *
     * Note: The proper handling of \* with respect to (* *) is indicated  *
     * by the observation that both                                        *
     *                                                                     *
     *       \*  (* xxx                                                    *
     *                                                                     *
     * and                                                                 *
     *                                                                     *
     *       (* \* xx *)                                                   *
     *                                                                     *
     * are complete comments.                                              *
     **********************************************************************/
    {
        int line = begLine;
        int col = begCol;
        boolean notDone = true;
        int commentDepth = 0;
        StringBuilder newLine =
                new StringBuilder(inp.get(line).substring(0, col));
        while (notDone && line < inp.size()) {
            final String oldLine = inp.get(line);
            boolean inString = false;
            while (notDone && col < oldLine.length()) {
                final char inChar = oldLine.charAt(col);
                char outChar = inChar;
                if ((inChar == '(')
                        && !inString
                        && (col < oldLine.length() - 1)
                        && (oldLine.charAt(col + 1) == '*')) {
                    commentDepth = commentDepth + 1;
                    outChar = ' ';
                    col = col + 1;
                    newLine.append(outChar);
                } else if ((inChar == '*')
                        && !inString
                        && (col < oldLine.length() - 1)
                        && (oldLine.charAt(col + 1) == ')')) {
                    if (commentDepth == 0) { // This end comment must come after the end of
                        // the algorithm.
                        newLine.append(inChar);
                        outChar = ')';
                        col = col + 1;
                        notDone = false;
                    } else {
                        commentDepth = commentDepth - 1;
                        outChar = ' ';
                        col = col + 1;
                        newLine.append(outChar);
                    }
                } else if (commentDepth == 0) { /********************************************************
                 * Not in a comment.                                     *
                 ********************************************************/
                    if (inString) {
                        if (inChar == '"' /* " */) {
                            inString = false;
                        } else if ((inChar == '\\')
                                && (col < oldLine.length() - 1)) {
                            newLine.append(inChar);
                            outChar = oldLine.charAt(col + 1);
                            col = col + 1;
                        }
                    } else // Not in a string.
                    {
                        if ((inChar == '\\')
                                && (col < oldLine.length() - 1)
                                && (oldLine.charAt(col + 1) == '*')) { // End-of-line comment
                            outChar = ' ';
                            col = oldLine.length();
                        } else if (inChar == '"') {
                            inString = true;
                        }
                    }
                } else { /********************************************************
                 * In a comment.                                         *
                 ********************************************************/
                    outChar = ' ';
                }
                newLine.append(outChar);
                col = col + 1;
            }
            if (inString) {
                throw new ParseAlgorithmException("Unterminated string in line " +
                        (line + 1));
            }
            inp.set(line, newLine.toString());
            newLine = new StringBuilder();
            col = 0;
            line = line + 1;
        }
    }

    /**************** CODE ADDED FOR HANDLING A .pcal FILE **********************/


/***************************************************************************
 *         ARGUMENTS OF METHODS FOR PROCESSING THE pcal INPUT               *
 *                                                                          *
 * Many of the following methods for processing the pcal input start at a   *
 * certain point and process a region of the input.  Those for which the    *
 * region can extend across multiple lines have the following arguments.    *
 * (An arguments will not appear if it can have only one possible value     *
 * or is not needed.)                                                       *
 *                                                                          *
 * StringVector inputVec                                                    *
 *    The pcal input file, usually with tabs removed.                       *
 *                                                                          *
 * IntPair curLoc                                                           *
 *    The <line, column> location (in Java coordinates) of the beginning    *
 *    of the region to process.  This object is modified by the method      *
 *    to leave it pointing immediately after the last character of the      *
 *    region that was processed.  If that character ends a line, then       *
 *    it points to the nonexistent character after the last character       *
 *    on the line.  (That is, the value of curLoc does not point to         *
 *    the first character on the next line.)                                *
 *                                                                          *
 * String errorMsg                                                          *
 *    Used only for a method that has multiple uses and can throw a         *
 *    ParseAlgorithmException.  It is the error reported if the             *
 *    exception is thrown.                                                  *
 *                                                                          *
 * Some methods just process a single line of the input.  Those have the    *
 * following arguments:                                                     *
 *                                                                          *
 * - A string that is the current line.                                     *
 *                                                                          *
 * - An int that is the position within the line of the beginning of        *
 *   the region.                                                            *
 *                                                                          *
 * They return a value that is the position on the line immediately after   *
 * the end of the region.  (This will equal the length of the line if the   *
 * region goes to the end of the line.)                                     *
 ***************************************************************************/

    /***
     * If curLoc points to a version statement, this method processes the
     * statement.  It is a no-op otherwise.  It calls PcalParams.ProcessVersion
     * to do the actual processing, and writes the statement to the tla output
     * file.  There is no comment removal.  The method returns false iff there is an
     * error,calling PcalDebug.reportError to report the error.
     *
     * See the comments above for an explanation of the arguments.
     */
    /***************************
     public boolean ProcessVersion(ArrayList inputVec,
     IntPair curLoc) {
     String curLine = GotoNextNonSpace(inputVec, curLoc);
     boolean error = false;
     if (curLine.substring(curLoc.two).startsWith("version")) {
     // Process the version number and move curLoc and curLine
     // to just after the closing ")".
     curLoc.two = curLoc.two + 7; // go to position after "version"
     curLine = GotoNextNonSpace(inputVec,  curLoc);
     if (!curLine.substring(curLoc.two).startsWith("(")) {
     curLoc.one = inputVec.size();
     error = true;
     }
     curLoc.two ++;
     curLine = GotoNextNonSpace(inputVec,  curLoc);
     int endOfArg = NextDelimiterCol(curLine, curLoc.two);
     if (!PcalParams.ProcessVersion(curLine.substring(curLoc.two, endOfArg))){
     curLoc.one = inputVec.size();
     error = true;
     }
     curLoc.two = endOfArg;
     curLine = GotoNextNonSpace(inputVec, curLoc);
     if (!error && !curLine.substring(curLoc.two).startsWith(")")) {
     curLoc.one = inputVec.size();
     error = true;
     }
     curLoc.two ++;
     // curLine = GotoNextNonSpace(untabInputVec, outputVec, curLoc);
     }
     if (error)
     { PcalDebug.reportError("Error in version statement");
     return false;
     }
     return true ;
     }
     ************************/

    /***
     * If the next non-space character is the beginning of the "options" string of
     * an options statement, then this method processes the statement.  Otherwise,
     * it does nothing.  The actual processing of the arguments is done by calling
     * trans.parseAndProcessArguments.  It returns STATUS_OK unless there is an
     * options statement with an error, in which case it returns the error status.
     * The options statement is written to the tla output.  There is no removal of comments.
     *
     * See the comments above for an explanation of the arguments.
     */
    public int ProcessOptions(final ArrayList<?> untabInputVec, final IntPair curLoc) {
        String curLine = GotoNextNonSpace(untabInputVec, curLoc);
        if (curLine.substring(curLoc.two).startsWith("options")) {
            // Process the options and move curLoc and curLine
            // to just after the closing ")".
            curLoc.two = curLoc.two + 7; // go to position after "options"
            curLine = GotoNextNonSpace(untabInputVec, curLoc);
            if (!curLine.substring(curLoc.two).startsWith("(")) {
                curLoc.one = untabInputVec.size();
                PcalDebug.reportError("`PlusCal options' not followed by '('");
                return trans.STATUS_EXIT_WITH_ERRORS;
            }
            curLoc.two++;
            curLine = GotoNextNonSpace(untabInputVec, curLoc);

            final ArrayList<String> argsVec = new ArrayList<>();
            // the vector of option arguments

            while (curLoc.one < untabInputVec.size() && (curLine.charAt(curLoc.two) != ')')) {
                if (curLine.charAt(curLoc.two) == ',') {
                    curLoc.two++;
                } else {
                    final int endOfArg = NextDelimiterCol(curLine, curLoc.two);
                    argsVec.add(curLine.substring(curLoc.two, endOfArg));
                    curLoc.two = endOfArg;
                }
                curLine = GotoNextNonSpace(untabInputVec, curLoc);
            }

            if (!(curLoc.one < untabInputVec.size())) {
                PcalDebug.reportError("No closing ')' found in options statement");
                return trans.STATUS_EXIT_WITH_ERRORS;
            }
            curLoc.two++;
            curLine = GotoNextNonSpace(untabInputVec, curLoc);

            // Process the options arguments.
            argsVec.add(""); // add dummy final argument
            final String[] argsArray = new String[argsVec.size()];
            for (int i = 0; i < argsArray.length; i++) {
                argsArray[i] = argsVec.get(i);
            }
// printArray(argsArray);
            final int status = trans.parseAndProcessArguments(this.pcalParams, argsArray);
            return status;
        }
        return trans.STATUS_OK;
    }

    /**
     * Searches for token, starting from curLoc in the String ArrayList inputVec, and
     * updates curLoc to the position immediately after the token if it's found.
     * Otherwise, it throws a ParseAlgorithmException.  The token must be
     * a sequence of letters, numbers, and "_" characters that is terminated by
     * any other kind of character or the end of a line.
     * <p>
     * See the comments above for an explanation of the arguments.
     *
     * @param token    The token being searched for.
     * @param inputVec Input String ArrayList
     * @param curLoc   <row, column> (Java coordinates) of beginning of search.
     */
    public void FindToken(
            final String token,
            final ArrayList<?> inputVec,
            final IntPair curLoc,
            final String errorMsg  // The error message to be reported if not found.
    )
            throws ParseAlgorithmException {
        boolean found = false;
        while ((!found) && (curLoc.one < inputVec.size())) {
            final String curLine = GotoNextNonSpace(inputVec, curLoc);
            if (curLine.substring(curLoc.two).startsWith(token)) {
                final int endLoc = curLoc.two + token.length();
                if ((endLoc >= curLine.length()) ||
                        !(Character.isLetter(curLine.charAt(endLoc)) ||
                                (curLine.charAt(endLoc) == '_'))) {
                    found = true;
                    curLoc.two = endLoc;
                }
            }
            curLoc.two = NextSpaceCol(curLine, curLoc.two);

        } // end of while, either found beginning or at end of file
        if (!found) {
            throw new ParseAlgorithmException(errorMsg);
        }

    }


    /***********************************************************************
     * Below are a bunch of methods called Next...  that are implemented    *
     * using the String class's split() method.  Since there's no           *
     * specification of that method, this is dangerous.  The one trap I've  *
     * found so far is this: experimentation suggests that if the regexp    *
     * identifies the entire string as being composed of splitting          *
     * strings, then it returns an array of length 0.  Who knows what       *
     * other features are lurking.  I thought of using the following        *
     * commented-out method NextCharOf to reimplement these methods, but I  *
     * decided not to bother.  Beware.                                      *
     ***********************************************************************/
/**
 * Returns the position of the first space at or after position col
 * in str, or str.size() if there is none.
 */

    /**
     * Returns the position of the first space , ",", or ")" at or after position col
     * in str, or str.size() if there is none.
     */
    private int NextDelimiterCol(final String str, final int col) {
        final String[] splitStr = str.substring(col).split("[ ,)]");
        if (splitStr.length == 0) {
            return col;
        }
        return col + splitStr[0].length();
    }

    /**
     * Returns the position of the first spaceat or after position col in
     * str, or str.size() if there is none.
     */
    private int NextSpaceCol(final String str, final int col) {
        final String[] splitStr = str.substring(col).split(" ");
        if (splitStr.length == 0) {
            return col;
        }
        return col + splitStr[0].length();
    }

    /**
     * Returns the position of the first character not a letter, number,
     * or "_" at or after position col in str, or str.size() if there is
     * none.
     */
    public int NextNonIdChar(final String str, final int col) {
        int curCol = col;
        char c = str.charAt(col);
        while ((curCol < str.length()) &&
                (Character.isLetter(c) || Character.isDigit(c) ||
                        (c == '_'))) {
            curCol++;
            if (curCol < str.length()) {
                c = str.charAt(curCol);
            }
        }
        return curCol;
    }


    /**
     * This method searches for the next non-space character and sets curLoc to
     * its location.  If there is no non-space character found, then the location
     * is set to column 0 of the first row after the end if inputVec.  It returns
     * the line to which curLoc is pointing to, or "" if loc is after the end of the
     * Note: it does the right thing if loc is the column after the end of a row.
     * <p>
     * See the comments above for an explanation of the arguments.  (No comment
     * removal is possible.)
     */
    public String GotoNextNonSpace(final ArrayList<?> inputVec, final IntPair curLoc) {
        boolean found = false;
        while ((!found) && curLoc.one < inputVec.size()) {
            final String line = (String) inputVec.get(curLoc.one);
            while ((!found) && curLoc.two < line.length()) {
                if (line.charAt(curLoc.two) == ' ') {
                    curLoc.two++;
                } else {
                    found = true;
                }
            }
            if (!found) {
                curLoc.one++;
                curLoc.two = 0;
            }
        }
        if (curLoc.one < inputVec.size()) {
            return (String) inputVec.get(curLoc.one);
        }
        return "";
    }


    /**
     * Like GotoNextNonSpace except it also skips over comments.
     *
     * See the comments above for an explanation of the arguments.
     *
     * @param inputVec
     * @param outputVec
     * @param curLoc
     * @param replace
     * @return
     */


    /**
     * This method assumes that str is a string whose character at
     * position loc is a quote (").  It returns the position immediately after
     * the matching quote that ends a TLA+ string.  If there is no matching
     * quote, then it throws a ParseAlgorithmException, reporting the error at
     * line line+1, column loc+1
     */
    public int findEndOfString(final String str, final int loc, final int line)
            throws ParseAlgorithmException {
        int pos = loc + 1;
        boolean found = false;
        while ((!found) && (pos < str.length())) {
            final char c = str.charAt(pos);
            if (c == '"') {
                found = true;
            } else if (c == '\\' && (pos < str.length() - 1)) {
                pos++;
            }
            pos++;
        }
        if (!found) {
            throw new ParseAlgorithmException("Unterminated string begun at line "
                    + "\n    line " + (line + 1) + ", column " + (loc + 1));
        }
        return pos;
    }

    /**
     * Finds the end of a comment in the String ArrayList inputVec, assuming
     * that loc is the location of the "(" in the "(*" that begins the comment,
     * and advances loc to the position just beyond the end of the closing "*)".
     * <p>
     * See the comments above for an explanation of the arguments.
     */
    public void gotoEndOfComment(final ArrayList<?> inputVec,  // ArrayList of strings
//                                       ArrayList outputVec, // null or ArrayList of strings
                                 final IntPair curLoc
                                 // <row, column> in Java coordinates of
                                 // "(*" that begins a comment.
//                                       boolean replace // true iff comment should
                                 // be replaced by spaces.
    )
            throws ParseAlgorithmException {
        boolean found = false;
        String curLine = (String) inputVec.get(curLoc.one);

        curLoc.two = curLoc.two + 2; // skip over "(*"

        while ((!found) && (curLoc.one < inputVec.size())) {
            while ((!found) && (curLoc.two < curLine.length())) {
                final char c = curLine.charAt(curLoc.two);
                if ((c == '(')
                        && (curLoc.two + 1 < curLine.length())
                        && (curLine.charAt(curLoc.two + 1) == '*')) {
                    // this character begins an inner comment.
                    // must set inputVec to correct value if replacing
                    gotoEndOfComment(inputVec, curLoc);
                    // must reset curLine and newLine
                    curLine = (String) inputVec.get(curLoc.one);
                } else if ((c == '*')
                        && (curLoc.two + 1 < curLine.length())
                        && (curLine.charAt(curLoc.two + 1) == ')')) {
                    // this character begins the comment-ending "*)"
                    curLoc.two = curLoc.two + 2;
                    found = true;
                } else {
                    curLoc.two++;
                }
            } // end of loop over characters in curLine
            if (!found) {
                curLoc.one++;
                curLoc.two = 0;
                if (curLoc.one < inputVec.size()) {
                    curLine = (String) inputVec.get(curLoc.one);
                }
            }
        } // end of while loop over lines.
        if (!found) {
            throw new ParseAlgorithmException("Unterminated comment begun at line "
                    + "\n    line " + (curLoc.one + 1) + ", column " + (curLoc.two + 1));
        }
    }

    // Copied from StringHelper
    public final void printArray(final Object[] array) {
        if (array == null) {
            System.out.println("null array");
            return;
        }
        if (array.length == 0) {
            System.out.println("zero-length array");
            return;
        }
        System.out.println("0-" + array[0].toString() + "-0");
        for (int i = 1; i < array.length; i++) {
            System.out.println("*-" + array[i].toString() + "-*");
        }
    }

}

