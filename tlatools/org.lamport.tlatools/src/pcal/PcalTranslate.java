/***************************************************************************
 * CLASS PcalTranslate                                                      *
 * last modified on Mon 20 Mar 2006 at  9:04:28 PST by lamport              *
 *      modified on Fri  9 Sep 2005 at 20:58:27 UT by keith                 *
 *                                                                          *
 * Given an AST, "explode" it: generate a new AST that has all Call,        *
 *   Return, CallReturn, GoTo and While replaced by variable, stack and     *
 *   pc manipulation; add explicit pc testing and pc setting for control    *
 *   flow; replace LabelIf with LabeledStmt and control flow                *
 *   implementation. The exploded AST maintains the structure except        *
 *   that once down to the LabeledStmt level, it is flat. The only depth    *
 *   is introduced by the If statement (since this depth is reflected in    *
 *   the generated TLA+ code).                                              *
 *                                                                          *
 * LL comment added 25 Jan 2006.  I don't understand what the preceding     *
 * sentence means.  I presume that Either should be added as a              *
 * "depth-introducing" statement.  But what about a With, since Withs can   *
 * also be nested?                                                          *
 *                                                                          *
 *      AST Explode (AST ast, PcalSymTab symtab)                            *
 *                                                                          *
 *   There are a few other public methods that can be used to generate      *
 *   snippets of TLAExpr. I only use them here.                             *
 ****************************************************************************/

package pcal;

import pcal.AST.Either;
import pcal.AST.If;
import pcal.AST.LabeledStmt;
import pcal.exception.PcalTranslateException;

import java.util.ArrayList;
import java.util.Objects;

// Using untyped objects is part of architecture
// Added suppression after typing what could be typed
@SuppressWarnings({"unchecked", "rawtypes"})
public class PcalTranslate {

    private final ParseAlgorithm parseAlgorithm;
    private final PcalParams pcalParams;
    private PcalSymTab st = null;  /* Set by invocation of Explode */
    /**
     * The following field added by LL on 7 June 2010 to allow return statements
     * to be used in macros.  It is initialized to null by Explode and is
     * set and reset by ExplodeProcedure so it equals the name of the current
     * procedure iff Exploding statements within a procedure.
     * <p>
     * See the comments for ExplodeReturn for more details.
     */
    private String currentProcedure;

    public PcalTranslate(final ParseAlgorithm parseAlgorithm) {

        this.parseAlgorithm = parseAlgorithm;
        this.pcalParams = parseAlgorithm.pcalParams;
    }

    /*************************************************************************
     * Routines for constructing snippets of +cal code                       *
     *************************************************************************/

    public static ArrayList<?> DiscardLastElement(final ArrayList<?> v) {
        if (v.size() > 0) v.remove(v.size() - 1);
        return v;
    }

    public static <T> ArrayList<T> Singleton(final T obj) {
        /*********************************************************************
         * If we think of a vector as a sequence, then this returns <<obj>>. *
         *********************************************************************/
        final ArrayList<T> result = new ArrayList<>();
        result.add(obj);
        return result;
    }

    public static <T> ArrayList<T> Pair(final T obj1, final T obj2) {
        /*********************************************************************
         * If we think of a vector as a sequence, then this returns          *
         * << obj1,  obj2 >>.                                                *
         *********************************************************************/
        final ArrayList<T> result = new ArrayList<>();
        result.add(obj1);
        result.add(obj2);
        return result;
    }

    public static ArrayList<Object> Triple(final Object obj1, final Object obj2, final Object obj3) {
        /*********************************************************************
         * If we think of a vector as a sequence, then this returns          *
         * << obj1,  obj2, obj3 >>.                                          *
         *********************************************************************/
        final ArrayList<Object> result = new ArrayList<>();
        result.add(obj1);
        result.add(obj2);
        result.add(obj3);
        return result;
    }

    public static <T> ArrayList<ArrayList<T>> Singleton2(final T obj) {
        /*********************************************************************
         * If we think of a vector as a sequence, then this returns          *
         * << <<obj>> >>.                                                    *
         *********************************************************************/
        return Singleton(Singleton(obj));
    }

    public static BoolObj BO(final boolean v) {
        /*********************************************************************
         * What I want to do is define a constructor for the BoolObj class    *
         * with an argument that is the value of the val field.  But I don't  *
         * remember how to do that and don't have access to any Java          *
         * documentation, so I'm defining BO to be that constructor.          *
         *********************************************************************/
        final BoolObj res = new BoolObj();
        res.val = v;
        return res;
    }

    public static TLAToken StringToken(final String str) {
        /*********************************************************************
         * Returns a new STRING token with string str.                       *
         *********************************************************************/
        final TLAToken result = new TLAToken();
        result.string = str;
        result.type = TLAToken.STRING;
        return result;
    }

    public static TLAToken AddedToken(final String str) {
        /*********************************************************************
         * Returns a new ADDED token with string str.                       *
         *********************************************************************/
        final TLAToken result = new TLAToken();
        result.string = str;
        result.type = TLAToken.ADDED;
        return result;
    }

    public static TLAToken BuiltInToken(final String str)
    /*********************************************************************
     * Returns a new BUILTIN token with string str.  (A token like "="    *
     * has type BUILTIN, though in the translation phase, there will      *
     * probably be no difference in how BUILTIN and IDENT tokens are      *
     * handled.)                                                          *
     *********************************************************************/
    {
        final TLAToken result = new TLAToken();
        result.string = str;
        result.type = TLAToken.BUILTIN;
        return result;
    }

    public static TLAToken IdentToken(final String str) {
        /*********************************************************************
         * Returns a new IDENT token for identifier str.                     *
         *********************************************************************/
        final TLAToken result = new TLAToken();
        result.string = str;
        result.type = TLAToken.IDENT;
        return result;
    }

    public static TLAExpr MakeExpr(final ArrayList<ArrayList<TLAToken>> vec) {
        /*********************************************************************
         * Makes a normalized expression exp with exp.tokens = vec.           *
         *********************************************************************/
        final TLAExpr result = new TLAExpr(vec);
        result.normalize();
        return result;
    }

    public static TLAExpr TokVectorToExpr(final ArrayList<TLAToken> vec, final int spaces)
    /*********************************************************************
     * If vec is a vector of TLAToken objects, then this method returns   *
     * a TLAExpr describing a one-line expression composed of clones of   *
     * the tokens in vec separated by `spaces' spaces.                    *
     * Called only by PcalTranslate.CheckPC.                              *
     *********************************************************************/
    {
        final ArrayList<TLAToken> firstLine = new ArrayList<>();
        int nextCol = 0;
        int i = 0;
        while (i < vec.size()) {
            final TLAToken tok = vec.get(i).Clone();
            tok.column = nextCol;
            firstLine.add(tok);
            nextCol = nextCol + tok.getWidth() + spaces;
            i = i + 1;
        }

        return MakeExpr(Singleton(firstLine));
    }

    public static void MakeNewStackTopExprPretty(final TLAExpr expr) {
        /*********************************************************************
         * Sets columns so this expr looks nice.                             *
         * Assumes exprs that this module generates for Call and CallReturn. *
         * Lines up the |-> tokens with the one for [ << procedure |-> ...   *
         * (that is, at column 16) when it can. The record names all appear  *
         * in column 6.                                                      *
         *********************************************************************/
        ArrayList<TLAToken> line; /* ArrayList of TLAToken */
        int nextCol;
        for (int i = 0; i < expr.tokens.size(); i++) {
            line = expr.tokens.get(i);
            if (i == 0 || i == expr.tokens.size() - 1) nextCol = 1;
            else nextCol = 6;
            for (final TLAToken tok : line) {
                tok.column = nextCol;
                nextCol = nextCol + tok.getWidth();
                if (tok.type == TLAToken.BUILTIN && tok.string.equals("|->")) {
                    tok.column = tok.column + 1;
                    if (tok.column < 16) tok.column = 16;
                    nextCol = tok.column + 5;
                } else if (tok.type == TLAToken.BUILTIN && tok.string.equals("[")) {
                    nextCol = nextCol + 1;
                } else if (tok.type == TLAToken.BUILTIN && tok.string.equals("]")) {
                    tok.column = tok.column + 1;
                    nextCol = nextCol + 1;
                } else if (tok.type == TLAToken.BUILTIN && tok.string.equals("<<")) {
                    nextCol = nextCol + 1;
                } else if (tok.type == TLAToken.BUILTIN && tok.string.equals(">>")) {
                    tok.column = tok.column + 1;
                    nextCol = nextCol + 1;
                } else if (tok.type == TLAToken.BUILTIN && tok.string.equals("\\o")) {
                    tok.column = tok.column + 1;
                    nextCol = nextCol + 2;
                }

            }
        }
    }

    /*********************************************************************
     * true if expr is TRUE or ( TRUE )                                   *
     *********************************************************************/
    public static boolean IsTRUE(final TLAExpr expr) {
        final ArrayList<ArrayList<TLAToken>> tokens = expr.tokens;
        if (tokens.size() > 1) return false;
        final ArrayList<TLAToken> line = tokens.get(0);
        if (line.size() == 1) {
            final TLAToken tok = line.get(0);
            return tok.string.equals("TRUE");
        } else if (line.size() == 3) {
            final TLAToken tok1 = line.get(0);
            final TLAToken tok2 = line.get(1);
            final TLAToken tok3 = line.get(2);
            return tok1.string.equals("(")
                    && tok2.string.equals("TRUE")
                    && tok3.string.equals(")");
        } else return false;
    }

    public AST.Assign MakeAssign(final String id, final TLAExpr exp) {
        /*********************************************************************
         * Makes the assignment statement id := exp.                         *
         *                                                                   *
         * It is called only by UpdatePC, with id = "pc".                    *
         *********************************************************************/
        final AST.SingleAssign sAss = new AST.SingleAssign(pcalParams);
        sAss.lhs.var = id;
        sAss.lhs.sub = MakeExpr(new ArrayList<>());
        sAss.rhs = exp;
        final AST.Assign result = new AST.Assign(pcalParams);
        result.ass = Singleton(sAss);
        return result;
    }

    private AST.When CheckPC(final String label) {
        /*********************************************************************
         * Generate when pc = label ;                                         *
         *********************************************************************/
        final AST.When checkPC = new AST.When(pcalParams);
        final ArrayList<TLAToken> toks = new ArrayList<>();
        toks.add(AddedToken("pc"));
        toks.add(BuiltInToken("="));
        toks.add(StringToken(label));
        checkPC.exp = TokVectorToExpr(toks, 1);
        return checkPC;
    }

    private AST.Assign UpdatePC(final String next) {
        /*********************************************************************
         * Generate pc := next ;                                              *
         *********************************************************************/
        return MakeAssign("pc", MakeExpr(Singleton2(StringToken(next))));
    }

    /*************************************************************************
     * Explode
     **
     *************************************************************************/

    public AST Explode(final AST ast, final PcalSymTab symtab) throws PcalTranslateException {
        /*********************************************************************
         * Expand while, labeled if, and nexted labeled with a sequence of    *
         * of flat labeled statements. Control flow is added via assignments  *
         * to pc. This expansion produces a new AST.                          *
         *********************************************************************/
        st = symtab;
        currentProcedure = null;  // added by LL on 7 June 2010
        if (ast instanceof AST.Uniprocess u)
            return ExplodeUniprocess(u);
        else if (ast instanceof AST.Multiprocess m)
            return ExplodeMultiprocess(m);
        else {
            PcalDebug.ReportBug("Unexpected AST type.");
            return null;
        }
    }

    private AST.Uniprocess ExplodeUniprocess(final AST.Uniprocess ast) throws PcalTranslateException {
        /*********************************************************************
         * Generate new AST.Uniprocess that has exploded labeled statements.  *
         *********************************************************************/
        int i = 0;
        final AST.Uniprocess newast = new AST.Uniprocess(pcalParams);
        newast.col = ast.col;
        newast.line = ast.line;
        newast.name = ast.name;
        newast.decls = ast.decls;
        newast.prcds = new ArrayList<>(ast.prcds.size());
        newast.defs = ast.defs;  // added 25 Jan 2006 by LL
        newast.setOrigin(ast.getOrigin());
        while (i < ast.prcds.size()) {
            newast.prcds.add(
                    ExplodeProcedure(ast.prcds.get(i)));
            i = i + 1;
        }
        i = 0;
        newast.body = new ArrayList<>(ast.body.size());
        AST.LabeledStmt thisLS = (ast.body.size() > 0)
                ? (AST.LabeledStmt) ast.body.get(0) : null;
        AST.LabeledStmt nextLS = (ast.body.size() > 1)
                ? (AST.LabeledStmt) ast.body.get(1) : null;
        while (i < ast.body.size()) {
            final String next = (nextLS == null)
// Replacement of following line by LL on 3 Feb 2006, since
// label "Done" never has to be renamed, since "Done" is not
// a legal user label.
//                ? st.UseThis(PcalSymTab.LABEL, "Done", "")
                    ? "Done"
                    : nextLS.label;
            newast.body.addAll(ExplodeLabeledStmt(Objects.requireNonNull(thisLS), next));
            i = i + 1;
            thisLS = nextLS;
            nextLS = (ast.body.size() > i + 1)
                    ? (AST.LabeledStmt) ast.body.get(i + 1) : null;
        }
        return newast;
    }

    private AST.Multiprocess ExplodeMultiprocess(final AST.Multiprocess ast) throws PcalTranslateException {
        /*********************************************************************
         * Generate new AST.Multiprocess with exploded labeled statements.    *
         *********************************************************************/
        int i = 0;
        final AST.Multiprocess newast = new AST.Multiprocess(pcalParams);
        newast.col = ast.col;
        newast.line = ast.line;
        newast.name = ast.name;
        newast.decls = ast.decls;
        newast.prcds = new ArrayList<>(ast.prcds.size());
        newast.defs = ast.defs;  // added 25 Jan 2006 by LL
        newast.setOrigin(ast.getOrigin());
        while (i < ast.prcds.size()) {
            newast.prcds.add(ExplodeProcedure(ast.prcds.get(i)));
            i = i + 1;
        }
        i = 0;
        newast.procs = new ArrayList<>(ast.procs.size());
        while (i < ast.procs.size()) {
            newast.procs.add(ExplodeProcess(ast.procs.get(i)));
            i = i + 1;
        }
        return newast;
    }

    private AST.Procedure ExplodeProcedure(final AST.Procedure ast) throws PcalTranslateException {
        /*********************************************************************
         * Generate new AST.Procedure with exploded labeled statements.       *
         *********************************************************************/
        int i = 0;
        final AST.Procedure newast = new AST.Procedure(pcalParams);
        newast.setOrigin(ast.getOrigin());
        newast.col = ast.col;
        newast.line = ast.line;
        newast.name = ast.name;
        currentProcedure = ast.name;  // Added by LL on 7 June 2010
        newast.params = ast.params;
        newast.decls = ast.decls;
        newast.body = new ArrayList<>(ast.body.size());
        AST.LabeledStmt thisLS = (ast.body.size() > 0)
                ? (AST.LabeledStmt) ast.body.get(0) : null;
        AST.LabeledStmt nextLS = (ast.body.size() > 1)
                ? (AST.LabeledStmt) ast.body.get(1) : null;
        while (i < ast.body.size()) {
            final String next = (nextLS == null)
                    ? st.UseThis(PcalSymTab.LABEL, "Error", "")
                    : nextLS.label;
            newast.body.addAll(ExplodeLabeledStmt(Objects.requireNonNull(thisLS), next));
            i = i + 1;
            thisLS = nextLS;
            nextLS = (ast.body.size() > i + 1)
                    ? (AST.LabeledStmt) ast.body.get(i + 1) : null;
        }
        currentProcedure = null;  // Added by LL on 7 June 2010
        return newast;
    }

    private AST.Process ExplodeProcess(final AST.Process ast) throws PcalTranslateException {
        /*********************************************************************
         * Generate new AST.Process with exploded labeled statements.         *
         *********************************************************************/
        int i = 0;
        final AST.Process newast = new AST.Process(pcalParams);
        newast.setOrigin(ast.getOrigin());
        newast.col = ast.col;
        newast.line = ast.line;
        newast.name = ast.name;
        newast.isEq = ast.isEq;
        newast.id = ast.id;
        newast.decls = ast.decls;
        newast.body = new ArrayList<>();
        AST.LabeledStmt thisLS = (ast.body.size() > 0)
                ? (AST.LabeledStmt) ast.body.get(0) : null;
        AST.LabeledStmt nextLS = (ast.body.size() > 1)
                ? (AST.LabeledStmt) ast.body.get(1) : null;
        while (i < ast.body.size()) {
            final String next = (nextLS == null)
// Replacement of following line by LL on 3 Feb 2006, since
// label "Done" never has to be renamed, since "Done" is not
// a legal user label.
//                ? st.UseThis(PcalSymTab.LABEL, "Done", "")
                    ? "Done"
                    : nextLS.label;
            newast.body.addAll(ExplodeLabeledStmt(Objects.requireNonNull(thisLS), next));
            i = i + 1;
            thisLS = nextLS;
            nextLS = (ast.body.size() > i + 1)
                    ? (AST.LabeledStmt) ast.body.get(i + 1) : null;
        }
        return newast;
    }

    private ArrayList<Object> CopyAndExplodeLastStmt(final ArrayList<AST> stmts, final String next) throws PcalTranslateException {
        /**************************************************************
         * The arguments are:                                               *
         *                                                                  *
         *    stmts : a (perhaps null) ArrayList of statements                 *
         *    next  : the label of the next control point following stmts.  *
         *                                                                  *
         * It returns a triple <<result1, result2, needsGoto>>, where       *
         *                                                                  *
         *   result1 : A vector equal to stmts with the last statement      *
         *             replaced if necessary by the exploded version--      *
         *             namely, if it is a goto, call, return, or            *
         *             callreturn, or if it is a statement with one of      *
         *             these statements or a labeled statement nested       *
         *             within it.                                           *
         *                                                                  *
         *   result2 : A (possibly empty) vector that is the sequence of    *
         *             labeled statements generated by exploding the last   *
         *             statement of stmts.                                  *
         *                                                                  *
         *   needsGoto : A boolean that equals true iff the sequence        *
         *               result1 of statements needs a goto at the end to   *
         *               transfer control to `next'.  In other words, it    *
         *               equals false if result1 contains the necessary     *
         *               goto statements and no goto must be added.         *
         *                                                                  *
         * Modified by LL on 25 Jan 2006 to handle the `either' statement   *
         * and to correct the following bug.  If a labeled statement ended  *
         * with an `if' statement, then gotos were added to both the then   *
         * and else clause, even if there was no transfer of control        *
         * within those clauses, so a single goto after the `if' would      *
         * work.  Similarly, if the statement ended with a `with', the      *
         * goto at the end would always be placed inside the `with' when    *
         * it logically belonged outside.                                   *
         **************************************************************/
        ArrayList<AST> result1 = new ArrayList<>(); /* a vector of statements */
        ArrayList<AST> result2 = new ArrayList<>(); /* a vector of labeled statements */
        boolean needsGoto = false;
        if (stmts != null && stmts.size() > 0) {
            final AST last = stmts.get(stmts.size() - 1);
            result1 = stmts;
            if (last instanceof AST.LabelIf l) {
                final ArrayList<Object> pair = ExplodeLabelIf(l, next);
                /*********************************************************
                 * Because a LabelIf has a label in the `then' or `else'  *
                 * clause, ExplodeLabelIf always has to add the           *
                 * necessary gotos.                                       *
                 *********************************************************/
                result1.remove(result1.size() - 1);
                result1.addAll((ArrayList) pair.get(0));
                result2 = (ArrayList) pair.get(1);
            }
            // LabelEither added by LL on 25 Jan 2006
            else if (last instanceof AST.LabelEither l) {
                final ArrayList<Object> pair = ExplodeLabelEither(l, next);
                /*********************************************************
                 * Because a LabelEither has a label in some clause,      *
                 * ExplodeLabelEither always has to add the necessary     *
                 * gotos.                                                 *
                 *********************************************************/
                result1.remove(result1.size() - 1);
                result1.addAll((ArrayList) pair.get(0));
                result2 = (ArrayList) pair.get(1);
            } else if (last instanceof AST.Goto g) {
                result1.remove(result1.size() - 1);
                // Note: if there's a GotoObj, then omitPC should be false.
                result1.add(UpdatePC(g.to));
            } else if (last instanceof AST.Call c) {
                result1.remove(result1.size() - 1);
                result1.addAll(ExplodeCall(c, next));
            } else if (last instanceof AST.Return r) {
                result1.remove(result1.size() - 1);
                result1.addAll(ExplodeReturn(r, next));
            } else if (last instanceof AST.CallReturn cr) {
                result1.remove(result1.size() - 1);
                result1.addAll(ExplodeCallReturn(cr, next));
            } else if (last instanceof AST.CallGoto cg) {
                result1.remove(result1.size() - 1);
                result1.addAll(ExplodeCallGoto(cg, next));
            } else if (last instanceof AST.If If) {
                final ArrayList<?> p1 = CopyAndExplodeLastStmt(If.Then, next);
                final ArrayList<?> p2 = CopyAndExplodeLastStmt(If.Else, next);
                result2.addAll((ArrayList) p1.get(1));
                result2.addAll((ArrayList) p2.get(1));
                If.Then = (ArrayList) p1.get(0);
                If.Else = (ArrayList) p2.get(0);
                if (!parseAlgorithm.omitPC) {
                    final boolean thenNeedsGoto = ((BoolObj) p1.get(2)).val;
                    final boolean elseNeedsGoto = ((BoolObj) p2.get(2)).val;
                    needsGoto = thenNeedsGoto && elseNeedsGoto;
                    if (!needsGoto) {
                        if (thenNeedsGoto) {
                            If.Then.add(UpdatePC(next));
                        }
                        if (elseNeedsGoto) {
                            If.Else.add(UpdatePC(next));
                        }
                    }
                }
            }
            // EitherObj added by LL on 25 Jan 2006
            else if (last instanceof AST.Either Either) {
                needsGoto = true;
                final ArrayList<Object> needsGotoVec = new ArrayList<>();
                for (int i = 0; i < Either.ors.size(); i++) {
                    final ArrayList<Object> thisP = CopyAndExplodeLastStmt(
                            (ArrayList) Either.ors.get(i), next);

                    Either.ors.set(i, thisP.get(0));
                    result2.addAll((ArrayList) thisP.get(1));
                    needsGoto = needsGoto && ((BoolObj) thisP.get(2)).val;
                    needsGotoVec.add(thisP.get(2));
                }
                if (!parseAlgorithm.omitPC) {
                    if (!needsGoto) {
                        /* Each `or' clause needs a goto. */
                        for (int i = 0; i < Either.ors.size(); i++) {
                            if (((BoolObj) needsGotoVec.get(i)).val) {
                                ((ArrayList)
                                        Either.ors.get(i)).add(
                                        UpdatePC(next));
                            }
                        }
                    }
                }
            } else if (last instanceof AST.With with) {
                final ArrayList<?> p = CopyAndExplodeLastStmt(with.Do, next);
                with.Do = (ArrayList) p.get(0);
                result2.addAll((ArrayList) p.get(1));
                /*********************************************************
                 * This statement should be a no-op because a `with'      *
                 * should have no labels inside it.  Perhaps we should    *
                 * add a test for this.  (LL comment)                     *
                 *********************************************************/
                needsGoto = ((BoolObj) p.get(2)).val;
            } else needsGoto = true; // result1.add(UpdatePC(next));
        } else {
            /* This is an empty sequence of statements.  */
            needsGoto = true;
        }
//        else  result1.add(UpdatePC(next));
        if (parseAlgorithm.omitPC) {
            needsGoto = false;
        }
        return Triple(result1, result2, BO(needsGoto));
    }

    private ArrayList<Object>
    CopyAndExplodeLastStmtWithGoto(final ArrayList stmts, final String next) throws PcalTranslateException {
        /*********************************************************************
         * Added by LL on 5 Feb 2011: The following comment seems to be       *
         * wrong, and the method adds a goto iff the 3rd element of the       *
         * value returned by CopyAndExplodeLastStmt equals true.              *
         *                                                                    *
         * Like CopyAndExplodeLastStmt, but it always adds a goto and         *
         * returns only a pair consisting of the first two elements of the    *
         * triple returned by CopyAndExplodeLastStmt.                         *
         *********************************************************************/
        final ArrayList<Object> res = CopyAndExplodeLastStmt(stmts, next);
        if (((BoolObj) res.get(2)).val) {
            ((ArrayList) res.get(0)).add(UpdatePC(next));
        }
        return Pair(res.get(0), res.get(1));
    }

    private ArrayList<LabeledStmt> ExplodeLabeledStmt(final AST.LabeledStmt ast,
                                                      final String next) throws PcalTranslateException {
        /******************************************************************
         * label SL -->                                                    *
         * label when pc = "label" ;                                       *
         *       SL                                                        *
         *       pc := next;                                               *
         *                                                                 *
         * Comment added by LL on 30 Jan 2006.                             *
         * I have no idea what the comment above is supposed to mean, but  *
         * this seems to return a sequence of labeled statements,          *
         * consisting of the exploded version of the labeled stmt ast      *
         * followed by the exploded labeled statements contained within    *
         * it.                                                             *
         ******************************************************************/
        /* Handle case of initial while separately */
        if (ast.stmts.size() > 0 &&
                ast.stmts.get(0) instanceof AST.While) {
            return ExplodeWhile(ast, next);
        }
        final AST.LabeledStmt newast = new AST.LabeledStmt(pcalParams);
        final ArrayList<Object> pair =
                CopyAndExplodeLastStmtWithGoto((ArrayList) ast.stmts.clone(),
                        next);
        final ArrayList<LabeledStmt> result = new ArrayList<>();
        newast.setOrigin(ast.getOrigin());
        newast.col = ast.col;
        newast.line = ast.line;
        newast.label = ast.label;
        /* add the statements with last exploded */
        newast.stmts = (ArrayList) pair.get(0);
        if (!parseAlgorithm.omitPC) {
            /* prepend pc check */
            newast.stmts.add(0, CheckPC(newast.label));
            result.add(newast);
        }
        /* add recursively generated labeled statements */
        result.addAll((ArrayList) pair.get(1));
        return result;
    }

    private ArrayList<LabeledStmt> ExplodeLabeledStmtSeq(final ArrayList seq,
                                                         final String next) throws PcalTranslateException {
        /**********************************************************************
         * seq is a sequence of LabeledStmts, and `next' is the label that     *
         * follows them.  Returns the sequence of LabeledStmts obtained by     *
         * iteratively calling ExplodeLabeledStmt to explode the statements    *
         * in seq.                                                             *
         *                                                                     *
         * Added by LL on 30 Jan 2006.  I don't know why this method did not   *
         * already exist, since it must have been written in-line about 5      *
         * times in various other methods.                                     *
         **********************************************************************/
        final ArrayList<LabeledStmt> result = new ArrayList<>();
        for (int i = 0; i < seq.size(); i++) {
            final AST.LabeledStmt stmt = (AST.LabeledStmt) seq.get(i);
            final String nxt = (i < seq.size() - 1) ?
                    ((AST.LabeledStmt) seq.get(i + 1)).label : next;
            result.addAll(ExplodeLabeledStmt(stmt, nxt));
        }
        return result;
    }

    /*
     * Experimentation shows that the following method is called with ast
     * equal to a LabeledStmt such that the first elementof ast.stmts
     * is an AST.While node, and the remaining elements are the unlabeled
     * statements following the source `while' statement.
     */
    private ArrayList<LabeledStmt> ExplodeWhile(final AST.LabeledStmt ast,
                                                final String next) throws PcalTranslateException {
        /*******************************************************************
         * label test unlabDo labDo next -->                                *
         * label when pc = "label" ;                                        *
         *       if test then unlabDo; pc := ld1;                           *
         *       else rest of statements                                    *
         *            pc := next                                            *
         * ld1   ...                                                        *
         * ldk   ...                                                        *
         *       pc := "label";                                             *
         *                                                                  *
         * Returns a pair that's like the first two elements of the         *
         * triple returned by CopyAndExplodeLastStmt.  (It always adds      *
         * the necessary goto to transfer control.)                         *
         *                                                                  *
         * If the test is TRUE or (TRUE) then the exploded code is          *
         * simplified to eliminate the if statement.  Any code that would   *
         * be executed in the "else" clause is discarded.  A warning        *
         * message is generated when the exploded code is simplified.       *
         *******************************************************************/
        final ArrayList<LabeledStmt> result = new ArrayList<>();
        final AST.While w = (AST.While) ast.stmts.get(0);

        final AST.LabeledStmt newast = new AST.LabeledStmt(pcalParams);
        /*
         * We set the origin of the new LabeledStatement to that of
         * ast, if there is a statement that follows the While.  Otherwise,
         * it goes from the label to the end of the If constructed from the while.
         *
         * We set the origin of the If constructed from the while to the end
         * its unLabDo if there is a non-empty labDo, otherwise to the end
         * of the While.
         */
        final PCalLocation newastBeginLoc = ast.getOrigin().getBegin();
        final PCalLocation whileBeginLoc = w.getOrigin().getBegin();
        final PCalLocation whileEndUnlabDoLoc =
                (w.unlabDo.size() != 0) ?
                        w.unlabDo.get(w.unlabDo.size() - 1).getOrigin().getEnd() :
                        w.test.getOrigin().getEnd();
        final PCalLocation whileEndLoc =
                // The original code contained
                //
                //     (w.labDo.size() != 0) ? w.getOrigin().getEnd() : whileEndUnlabDoLoc ;
                //
                // which does not implement the comment above.
                (ast.stmts.size() != 1) ? ast.getOrigin().getEnd() : whileEndUnlabDoLoc;
        newast.setOrigin(new Region(newastBeginLoc, whileEndLoc));
        newast.col = ast.col;
        newast.line = ast.line;
        newast.label = ast.label;
        newast.stmts = new ArrayList();

        if (!parseAlgorithm.omitPC) {
            newast.stmts.add(CheckPC(ast.label));   // pc test
        }

        /* determine where control goes after unlabDo is executed */
        AST.LabeledStmt firstLS = (w.labDo.size() == 0)
                ? null : (AST.LabeledStmt) w.labDo.get(0);
        /* explode unlabDo */
        final String unlabDoNext = (firstLS == null) ? ast.label : firstLS.label;
        final ArrayList<Object> pair1 =
                CopyAndExplodeLastStmtWithGoto((ArrayList) w.unlabDo.clone(),
                        unlabDoNext);
        /* explode the rest of the statements */
        final ArrayList<AST> rest = (ArrayList<AST>) ast.stmts.clone();
        // Note: experimentation shows that clone() does a shallow copy, so
        // the elements of rest are == to the elements of ast.stmts.
        rest.remove(0);
        final ArrayList<Object> pair2 = CopyAndExplodeLastStmtWithGoto(rest, next);

        if (IsTRUE(w.test)) // Optimized translation of while TRUE do
            newast.stmts.addAll((ArrayList) pair1.get(0));
        else {
            final AST.If ifS = new AST.If(pcalParams);
            ifS.test = w.test;
            ifS.Then = (ArrayList) pair1.get(0);
            ifS.Else = (ArrayList) pair2.get(0);
            ifS.setOrigin(new Region(whileBeginLoc, whileEndLoc));
            newast.stmts.add(ifS);
        }
        result.add(newast);

        /* explode the enclosed labeled statements and add to the result */
        for (int i = 0; i < w.labDo.size(); i++) {
            final AST.LabeledStmt nextLS = (w.labDo.size() > i + 1)
                    ? (AST.LabeledStmt) w.labDo.get(i + 1) : null;
            final String nextLSL = (nextLS == null) ? ast.label : nextLS.label;
            result.addAll(ExplodeLabeledStmt(Objects.requireNonNull(firstLS), nextLSL));
            firstLS = nextLS;
        }

        result.addAll((ArrayList) pair1.get(1));

        // If IsTRUE(w.test) is true and pair2.get(1) is not an empty
        // list, then there are unreachable statements after the While and
        // we should probably report an error.
        if (!IsTRUE(w.test))
            result.addAll((ArrayList) pair2.get(1));

        return result;
    }

    private ArrayList<Object> ExplodeLabelIf(final AST.LabelIf ast, final String next) throws PcalTranslateException {
        /***************************************************************
         *       test unlabThen labThen unlabElse labElse next -->     *
         *       if test then                                          *
         *          unlabThen                                          *
         *          pc := lt1                                          *
         *       else                                                  *
         *          unlabElse                                          *
         *          pc := le1                                          *
         * lt1   ...                                                   *
         * ltk   ...                                                   *
         *       pc := next;                                           *
         * le1   ...                                                   *
         * lek   ...                                                   *
         *       pc := next;                                           *
         *                                                             *
         * The result is a pair: the first is a vector of statements   *
         * corresponding to the block before lt1, and the second is    *
         * is a vector of the remaining labeled statements.            *
         ***************************************************************/
        int i = 0;
        final ArrayList<If> result1 = new ArrayList<>(); /* If for unlabeled statements */
        final ArrayList<LabeledStmt> result2 = new ArrayList<>(); /* the labeled statements */
        final AST.If newif = new AST.If(pcalParams);
        AST.LabeledStmt firstThen = (ast.labThen.size() > 0)
                ? (AST.LabeledStmt) ast.labThen.get(0) : null;
        AST.LabeledStmt firstElse = (ast.labElse.size() > 0)
                ? (AST.LabeledStmt) ast.labElse.get(0) : null;
        final ArrayList<Object> explodedThen =
                CopyAndExplodeLastStmtWithGoto(ast.unlabThen,
                        (firstThen == null)
                                ? next : firstThen.label);
        final ArrayList<Object> explodedElse =
                CopyAndExplodeLastStmtWithGoto(ast.unlabElse,
                        (firstElse == null)
                                ? next : firstElse.label);
        /* Construct if statement */
        newif.test = ast.test;
        newif.col = ast.col;
        newif.line = ast.line;
        newif.Then = (ArrayList) explodedThen.get(0);
        newif.Else = (ArrayList) explodedElse.get(0);
        newif.setOrigin(ast.getOrigin());
        /*
         * The LabelIf object ast has a labeled statement in its then clause iff
         * ast.labThen or explodedThen.get(1) has non-zero length.
         * It has a labeled statement in its else clause iff
         * ast.labElse or explodedElse.get(1) has non-zero length.
         */
        newif.setSource(
                ((ast.labThen.size() != 0 ||
                        ((ArrayList) explodedThen.get(1)).size() != 0)
                        ? If.BROKEN_THEN : 0)
                        +
                        ((ast.labElse.size() != 0 ||
                                ((ArrayList) explodedElse.get(1)).size() != 0)
                                ? If.BROKEN_ELSE : 0)
        );
        result1.add(newif);

        /* Explode the labeled then statements */
        AST.LabeledStmt nextThen = (ast.labThen.size() > 1)
                ? (AST.LabeledStmt) ast.labThen.get(1) : null;
        while (i < ast.labThen.size()) {
            final String nextThenLabel = (nextThen == null) ? next : nextThen.label;
            result2.addAll(ExplodeLabeledStmt(Objects.requireNonNull(firstThen), nextThenLabel));
            i = i + 1;
            firstThen = nextThen;
            nextThen = (ast.labThen.size() > i + 1)
                    ? (AST.LabeledStmt) ast.labThen.get(i + 1) : null;
        }
        /* Explode the labeled else statements */
        AST.LabeledStmt nextElse = (ast.labElse.size() > 1)
                ? (AST.LabeledStmt) ast.labElse.get(1) : null;
        i = 0;
        while (i < ast.labElse.size()) {
            final String nextElseLabel = (nextElse == null) ? next : nextElse.label;
            result2.addAll(ExplodeLabeledStmt(Objects.requireNonNull(firstElse), nextElseLabel));
            i = i + 1;
            firstElse = nextElse;
            nextElse = (ast.labElse.size() > i + 1)
                    ? (AST.LabeledStmt) ast.labElse.get(i + 1) : null;
        }


        /* Add labeled statements from exploding unlabThen and unlabElse */
        result2.addAll((ArrayList) explodedThen.get(1));
        result2.addAll((ArrayList) explodedElse.get(1));
        return Pair(result1, result2);
    }

    private ArrayList<Object> ExplodeLabelEither(final AST.LabelEither ast,
                                                 final String next) throws PcalTranslateException {
        /*******************************************************************
         * Analogous to ExplodeLabelIf, except it hasa sequence of clauses  *
         * rather than just the then and else clauses.                      *
         *                                                                  *
         * The result is a pair: the first is a vector of statements        *
         * corresponding to the block before lt1, and the second is         *
         * is a vector of the remaining labeled statements.                 *
         *******************************************************************/
        final ArrayList<Either> result1 = new ArrayList<>(); /* For the Either object.           */
        final ArrayList<LabeledStmt> result2 = new ArrayList<>(); /* The internal labeled statements. */
        final AST.Either newEither = new AST.Either(pcalParams);

        /* Construct Either object */
        newEither.col = ast.col;
        newEither.line = ast.line;
        newEither.setOrigin(ast.getOrigin());
        newEither.ors = new ArrayList<>();
        for (int i = 0; i < ast.clauses.size(); i++) {
            final AST.Clause clause = ast.clauses.get(i);
            final ArrayList<Object> res =
                    CopyAndExplodeLastStmtWithGoto(
                            clause.unlabOr,
                            (clause.labOr.size() > 0) ?
                                    ((AST.LabeledStmt) clause.labOr.get(0)).label : next
                    );
            /**
             * Set clause.broken, which should be true iff clause.labOr or
             * res.get(1) is non-empty.
             */
            if (clause.labOr.size() != 0 || ((ArrayList) res.get(1)).size() != 0) {
                clause.setBroken(true);
            }
            newEither.ors.add(res.get(0));
            result2.addAll((ArrayList) res.get(1));
            result2.addAll(ExplodeLabeledStmtSeq(clause.labOr, next));
        }
        result1.add(newEither);
        return Pair(result1, result2);
    }

    /***********************************************************************
     * Generate sequence of statements corresponding to call                *
     *                                                                      *
     * Modified 1 Feb 2006 by LL to put the initialization of the           *
     * procedure's local variables as a sequence of separate assignment     *
     * statements, executed after the initialization of the formal          *
     * parameters.                                                          *
     *                                                                      *
     * Modified by LL on 2 Feb 2006 to add line and column numbers to the   *
     * newly created statements for error reporting.
     **
     ***********************************************************************/
    private ArrayList<AST.Assign> ExplodeCall(final AST.Call ast, final String next) throws PcalTranslateException {
        final ArrayList<AST.Assign> result = new ArrayList<>();
        final int to = st.FindProc(ast.to);
        /*******************************************************************
         * Error check added by LL on 30 Jan 2006 to fix bug_05_12_10.      *
         *******************************************************************/
        if (to == st.procs.size()) {
            throw new PcalTranslateException("Call of non-existent procedure " + ast.to,
                    ast);
        }
        final PcalSymTab.ProcedureEntry pe =
                st.procs.get(to);
        /*******************************************************************
         * Set ass to a multiple assignment that pushes the call record on  *
         * the stack, sets the called procedure's parameters.               *
         *                                                                  *
         * The call record put on the stack is:                             *
         *   procedure |-> ast.to                                           *
         *   pc |-> next                                                    *
         *   for each procedure variable v of ast.to v |-> v                *
         *   for each parameter p of ast.to p |-> p                         *
         *******************************************************************/
        AST.Assign ass = new AST.Assign(pcalParams);
        ass.ass = new ArrayList<>();
        ass.line = ast.line;
        ass.col = ast.col;
        AST.SingleAssign sass = new AST.SingleAssign(pcalParams);
        sass.line = ast.line;
        sass.col = ast.col;
        sass.lhs.var = "stack";
        sass.lhs.sub = MakeExpr(new ArrayList<>());
        final TLAExpr expr = new TLAExpr();
        expr.addLine();
        expr.addToken(BuiltInToken("<<"));
        expr.addToken(BuiltInToken("["));
        expr.addToken(IdentToken("procedure"));
        expr.addToken(BuiltInToken("|->"));
        expr.addToken(StringToken(ast.to));
        expr.addToken(BuiltInToken(","));
        expr.addLine();
        expr.addToken(IdentToken("pc"));
        expr.addToken(BuiltInToken("|->"));
        expr.addToken(StringToken(next));
        for (int i = 0; i < pe.decls.size(); i++) {
            final AST.PVarDecl decl =
                    pe.decls.get(i);
            expr.addToken(BuiltInToken(","));
            expr.addLine();
            expr.addToken(IdentToken(decl.var));
            expr.addToken(BuiltInToken("|->"));
            expr.addToken(IdentToken(decl.var));
        }
        for (int i = 0; i < pe.params.size(); i++) {
            final AST.PVarDecl decl =
                    pe.params.get(i);
            expr.addToken(BuiltInToken(","));
            expr.addLine();
            expr.addToken(IdentToken(decl.var));
            expr.addToken(BuiltInToken("|->"));
            expr.addToken(IdentToken(decl.var));
        }
        expr.addToken(BuiltInToken("]"));
        expr.addToken(BuiltInToken(">>"));
        expr.addLine();
        expr.addToken(BuiltInToken("\\o"));
        expr.addToken(AddedToken("stack"));
        MakeNewStackTopExprPretty(expr);
        expr.normalize();
        sass.rhs = expr;
        ass.ass.add(sass);
        /*********************************************************
         * for each parameter p of ast.to                        *
         *   p := matching expr in ast.arg                       *
         *********************************************************/
        /*******************************************************************
         * Assert changed to ReportErrorAt by LL on 30 Jan 2006.            *
         *******************************************************************/
        if (pe.params.size() != ast.args.size())
            throw new PcalTranslateException(
                    "Procedure " + ast.to +
                            " called with wrong number of arguments",
                    ast);
        /**
         * Set the origin of the AST.Assign object ass.origin to the region occupied
         * by the parameter declarations, and set the origin of each of its SingleAssign
         * subobjects that set the parameters to that parameter's declaration as a parameter
         * of the procedure.  (This code assumes that  the declarations appear in the params
         * list of an AST.Procedure in the order in which they appear in the PCal code.)
         * Since we're setting the origin to the entire declaration, if the declaration
         * specifies an initial value, then this will set the origin to the entire
         * declaration, rather than just the variable name.  This could be fixed easily,
         * but it's not worth the effort.
         */
        PCalLocation beginLoc = null;
        PCalLocation endLoc = null;
        for (int i = 0; i < pe.params.size(); i++) {
            final AST.PVarDecl decl =
                    pe.params.get(i);
            if (i == 0) {
                beginLoc = decl.getOrigin().getBegin();
            }
            if (i == pe.params.size() - 1) {
                endLoc = decl.getOrigin().getEnd();
            }
            sass = new AST.SingleAssign(pcalParams);
            sass.line = ast.line;
            sass.col = ast.col;
            sass.setOrigin(decl.getOrigin());
            sass.lhs.var = decl.var;
            sass.lhs.sub = MakeExpr(new ArrayList<>());
            sass.rhs = ast.args.get(i);
            ass.ass.add(sass);
        }
        if (beginLoc != null) {
            ass.setOrigin(new Region(beginLoc, endLoc));
        }
        result.add(ass);
        /*******************************************************************
         * Add a sequence of assignment statements to initialize each       *
         * procedure variable v of ast.to with                              *
         *   v := initial value                                             *
         *******************************************************************/
        for (int i = 0; i < pe.decls.size(); i++) {
            ass = new AST.Assign(pcalParams);
            ass.ass = new ArrayList<>();
            ass.line = ast.line;
            ass.col = ast.col;
            final AST.PVarDecl decl =
                    pe.decls.get(i);
            sass = new AST.SingleAssign(pcalParams);
            sass.line = ast.line;
            sass.col = ast.col;
            sass.setOrigin(decl.getOrigin());
            sass.lhs.var = decl.var;
            sass.lhs.sub = MakeExpr(new ArrayList<>());
            sass.rhs = decl.val;
            ass.setOrigin(decl.getOrigin());
            ass.ass.add(sass);
            result.add(ass);
        }

        /*******************************************************************
         * Add assignment to set pc:                                        *
         *   pc := entry point of ast.to                                    *
         *******************************************************************/
        // Note: omitPC must be false if there's a call statement (and hence
        // a procedure being called).
        result.add(UpdatePC(pe.iPC));
        return result;
    }

    /***********************************************************************
     * Modified by LL on 2 Feb 2006 to add line and column numbers to the   *
     * newly created statements for error reporting.
     **
     ***********************************************************************/
    private ArrayList<AST.Assign> ExplodeReturn(final AST.Return ast, final String next) throws PcalTranslateException {
        final ArrayList<AST.Assign> result = new ArrayList<>();
        /*******************************************************************
         * On 30 Mar 2006, added code to throw a PcalTranslateException     *
         * when ast.from equals null to raise an error if a return          *
         * statement appears outside a procedure.  That error was not       *
         * caught by the parsing phase for reasons explained in the         *
         * comments for ParseAlgorithm.GetReturn.                           *
         *                                                                  *
         * Unfortunately, that test raised an error if the return actually  *
         * was inside a procedure but was generated by macro expansion.     *
         * To allow that case, on 7 June 2010 LL added the                  *
         * currentProcedure field (see comments for that field) and         *
         * modified the test accordingly.  (This was after an incorrect     *
         * attempt to fix the problem on 6 June 2010.)                      *
         *******************************************************************/
        if (ast.from == null) {
            ast.from = currentProcedure;
        }
        if (ast.from == null) {
            throw new PcalTranslateException("`return' statement not in procedure", ast);
        }

        final int from = st.FindProc(ast.from);
        // The following added by LL on 13 Jan 2011.
        if (!(from < st.procs.size())) {
            throw new PcalTranslateException("Error in procedure (perhaps name used elsewhere)", ast);
        }
        final PcalSymTab.ProcedureEntry pe =
                st.procs.get(from);
        /*********************************************************
         * With h being the head of stack                        *
         *   pc := h.pc                                          *
         *   for each procedure variable v of ast.from v := h.v  *
         *   for each parameter p of ast.from p := h.p           *
         *********************************************************/
        AST.Assign ass = new AST.Assign(pcalParams);
        ass.line = ast.line;
        ass.col = ast.col;
        AST.SingleAssign sass = new AST.SingleAssign(pcalParams);
        sass.line = ast.line;
        sass.col = ast.col;
        TLAExpr expr = new TLAExpr();
        sass.lhs.var = "pc";
        sass.lhs.sub = new TLAExpr();
        expr.addLine();
        expr.addToken(IdentToken("Head"));
        expr.addToken(BuiltInToken("("));
        expr.addToken(AddedToken("stack"));
        expr.addToken(BuiltInToken(")"));
        expr.addToken(BuiltInToken("."));
        expr.addToken(IdentToken("pc"));
        expr.normalize();
        sass.rhs = expr;
        ass.ass = Singleton(sass);
        result.add(ass);
        for (int i = 0; i < pe.decls.size(); i++) {
            final AST.PVarDecl decl =
                    pe.decls.get(i);
            ass = new AST.Assign(pcalParams);
            ass.line = ast.line;
            ass.col = ast.col;
            sass = new AST.SingleAssign(pcalParams);
            sass.line = ast.line;
            sass.col = ast.col;
            expr = new TLAExpr();
            sass.lhs.var = decl.var;
            sass.lhs.sub = new TLAExpr();
            expr.addLine();
            expr.addToken(IdentToken("Head"));
            expr.addToken(BuiltInToken("("));
            expr.addToken(AddedToken("stack"));
            expr.addToken(BuiltInToken(")"));
            expr.addToken(BuiltInToken("."));
            expr.addToken(IdentToken(decl.var));
            expr.normalize();
            sass.rhs = expr;
            /**
             * For assignments that restore procedure variables, there's no
             * good origin.  I decided to set them to the origin of the return statement.
             */
            sass.setOrigin(ast.getOrigin());
            ass.setOrigin(ast.getOrigin());
            ass.ass = Singleton(sass);
            result.add(ass);
        }
        for (int i = 0; i < pe.params.size(); i++) {
            final AST.PVarDecl decl =
                    pe.params.get(i);
            ass = new AST.Assign(pcalParams);
            ass.line = ast.line;
            ass.col = ast.col;
            sass = new AST.SingleAssign(pcalParams);
            sass.line = ast.line;
            sass.col = ast.col;
            /** For assignments that restore procedure parameter values, there's no
             * good origin.  I decided to set them to the origin of the return statement.
             */
            sass.setOrigin(ast.getOrigin());
            ass.setOrigin(ast.getOrigin());
            expr = new TLAExpr();
            sass.lhs.var = decl.var;
            sass.lhs.sub = new TLAExpr();
            expr.addLine();
            expr.addToken(IdentToken("Head"));
            expr.addToken(BuiltInToken("("));
            expr.addToken(AddedToken("stack"));
            expr.addToken(BuiltInToken(")"));
            expr.addToken(BuiltInToken("."));
            expr.addToken(IdentToken(decl.var));
            expr.normalize();
            sass.rhs = expr;
            ass.ass = Singleton(sass);
            result.add(ass);
        }

        /*********************************************************
         * stack := Tail(stack)                                  *
         *********************************************************/
        ass = new AST.Assign(pcalParams);
        ass.line = ast.line;
        ass.col = ast.col;
        sass = new AST.SingleAssign(pcalParams);
        sass.setOrigin(ast.getOrigin());
        ass.setOrigin(ast.getOrigin());
        sass.line = ast.line;
        sass.col = ast.col;
        expr = new TLAExpr();
        sass.lhs.var = "stack";
        sass.lhs.sub = new TLAExpr();
        expr.addLine();
        expr.addToken(IdentToken("Tail"));
        expr.addToken(BuiltInToken("("));
        expr.addToken(AddedToken("stack"));
        expr.addToken(BuiltInToken(")"));
        expr.normalize();
        sass.rhs = expr;
        ass.ass = Singleton(sass);
        result.add(ass);
        return result;
    }

    /***********************************************************************
     * Generate sequence of statements corresponding to call followed by a  *
     * returen.                                                             *
     *                                                                      *
     * Modified 1 Feb 2006 by LL for the case of the calling and called     *
     * procedures being different to put the initialization of the          *
     * procedure's local variables as a sequence of separate assignment     *
     * statements, executed after the initialization of the formal          *
     * parameters.                                                          *
     *                                                                      *
     * Modified by LL on 2 Feb 2006 to add line and column numbers to the   *
     * newly created statements for error reporting.
     **
     ***********************************************************************/
    private ArrayList<AST.Assign> ExplodeCallReturn(final AST.CallReturn ast, final String next) throws PcalTranslateException {
        final ArrayList<AST.Assign> result = new ArrayList<>();
        /*******************************************************************
         * The following test for a return not in a procedure was added by  *
         * LL on 30 Mar 2006.  This error isn't caught by the parsing       *
         * phase for reasons explained in the comments for                  *
         * ParseAlgorithm.GetReturn.                                        *
         *******************************************************************/
        if (ast.from == null) {
            throw new PcalTranslateException(
                    "`return' statement following `call' at " +
                            ast.location() + " not in a procedure");
        }
        final int from = st.FindProc(ast.from);
        final PcalSymTab.ProcedureEntry peFrom =
                st.procs.get(from);
        final int to = st.FindProc(ast.to);
        /*******************************************************************
         * Assert changed to ReportErrorAt by LL on 30 Jan 2006, and moved  *
         * to where it belongs.                                             *
         *******************************************************************/
        if (to == st.procs.size()) {
            throw new PcalTranslateException("Call of non-existent procedure " + ast.to,
                    ast);
        }
        final PcalSymTab.ProcedureEntry peTo =
                st.procs.get(to);
        PcalDebug.Assert(from < st.procs.size());
        AST.Assign ass = new AST.Assign(pcalParams);
        ass.ass = new ArrayList<>();
        ass.line = ast.line;
        ass.col = ast.col;
        AST.SingleAssign sass;
        TLAExpr expr;
        /*******************************************************************
         * Add a single multiple assignment statement that                  *
         *   - restores the local variables of ast.from from the head of    *
         *     the stack.                                                   *
         *   - replaces the head of the stack with a record used to reset   *
         *     the local variables.                                         *
         *   - sets the parameters of ast.to.                               *
         *                                                                  *
         * First, with h being the head of the stack, restore each local    *
         * variable v of ast.from with v := h.v .                           *
         *******************************************************************/
        if (!ast.from.equals(ast.to)) {
            for (int i = 0; i < peFrom.decls.size(); i++) {
                final AST.PVarDecl decl =
                        peFrom.decls.get(i);
                sass = new AST.SingleAssign(pcalParams);
                sass.line = ast.line;
                sass.col = ast.col;
                expr = new TLAExpr();
                sass.lhs.var = decl.var;
                sass.lhs.sub = new TLAExpr();
                expr.addLine();
                expr.addToken(IdentToken("Head"));
                expr.addToken(BuiltInToken("("));
                expr.addToken(AddedToken("stack"));
                expr.addToken(BuiltInToken(")"));
                expr.addToken(BuiltInToken("."));
                expr.addToken(IdentToken(decl.var));
                expr.normalize();
                sass.rhs = expr;
                ass.ass.add(sass);
            }
            /********************************************************
             * Replace head of stack with record                    *
             *   procedure |-> ast.to                               *
             *   pc |-> h.pc (for current head h)                   *
             *   for each procedure variable v of ast.to v |-> v    *
             *   for each parameter variable p of ast.to p |-> p    *
             ********************************************************/
            sass = new AST.SingleAssign(pcalParams);
            sass.line = ast.line;
            sass.col = ast.col;
            sass.lhs.var = "stack";
            sass.lhs.sub = MakeExpr(new ArrayList<>());
            expr = new TLAExpr();
            expr.addLine();
            expr.addToken(BuiltInToken("<<"));
            expr.addToken(BuiltInToken("["));
            expr.addToken(IdentToken("procedure"));
            expr.addToken(BuiltInToken("|->"));
            expr.addToken(StringToken(ast.to));
            expr.addToken(BuiltInToken(","));
            expr.addLine();
            expr.addToken(IdentToken("pc"));
            expr.addToken(BuiltInToken("|->"));
            expr.addToken(IdentToken("Head"));
            expr.addToken(BuiltInToken("("));
            expr.addToken(AddedToken("stack"));
            expr.addToken(BuiltInToken(")"));
            expr.addToken(BuiltInToken("."));
            expr.addToken(IdentToken("pc"));
            for (int i = 0; i < peTo.decls.size(); i++) {
                final AST.PVarDecl decl =
                        peTo.decls.get(i);
                expr.addToken(BuiltInToken(","));
                expr.addLine();
                expr.addToken(IdentToken(decl.var));
                expr.addToken(BuiltInToken("|->"));
                expr.addToken(IdentToken(decl.var));
            }
            for (int i = 0; i < peTo.params.size(); i++) {
                final AST.PVarDecl decl =
                        peTo.params.get(i);
                expr.addToken(BuiltInToken(","));
                expr.addLine();
                expr.addToken(IdentToken(decl.var));
                expr.addToken(BuiltInToken("|->"));
                expr.addToken(IdentToken(decl.var));
            }
            expr.addToken(BuiltInToken("]"));
            expr.addToken(BuiltInToken(">>"));
            expr.addLine();
            expr.addToken(BuiltInToken("\\o"));
            expr.addToken(IdentToken("Tail"));
            expr.addToken(BuiltInToken("("));
            expr.addToken(AddedToken("stack"));
            expr.addToken(BuiltInToken(")"));
            MakeNewStackTopExprPretty(expr);
            expr.normalize();
            sass.rhs = expr;
            ass.ass.add(sass);
        }
        /*********************************************************
         * for each parameter p of ast.to                        *
         *   p := matching expr in ast.arg                       *
         *********************************************************/
        /*******************************************************************
         * Assert changed to ReportErrorAt by LL on 30 Jan 2006.            *
         *******************************************************************/
        if (peTo.params.size() != ast.args.size())
            throw new PcalTranslateException(
                    "Procedure " + ast.to +
                            " called with wrong number of arguments",
                    ast);
        /**
         * Setting of origins of created AST.Assign and AST.SingleAssign objects
         * essentialy the same as in ExplodeCall.
         */
        PCalLocation beginLoc = null;
        PCalLocation endLoc = null;
        for (int i = 0; i < peTo.params.size(); i++) {
            final AST.PVarDecl decl =
                    peTo.params.get(i);
            if (i == 0) {
                beginLoc = decl.getOrigin().getBegin();
            }
            if (i == peTo.params.size() - 1) {
                endLoc = decl.getOrigin().getEnd();
            }
            sass = new AST.SingleAssign(pcalParams);
            sass.line = ast.line;
            sass.col = ast.col;
            sass.lhs.var = decl.var;
            sass.lhs.sub = MakeExpr(new ArrayList<>());
            sass.rhs = ast.args.get(i);
            ass.ass.add(sass);
        }
        if (beginLoc != null) {
            ass.setOrigin(new Region(beginLoc, endLoc));
        }
        result.add(ass);
        /*******************************************************************
         * Add a sequence of assignment statements to initialize each       *
         * procedure variable v of ast.to with                              *
         *   v := initial value                                             *
         *******************************************************************/
        for (int i = 0; i < peTo.decls.size(); i++) {
            ass = new AST.Assign(pcalParams);
            ass.line = ast.line;
            ass.col = ast.col;
            ass.ass = new ArrayList<>();
            final AST.PVarDecl decl =
                    peTo.decls.get(i);
            sass = new AST.SingleAssign(pcalParams);
            sass.line = ast.line;
            sass.col = ast.col;
            sass.setOrigin(decl.getOrigin());
            sass.lhs.var = decl.var;
            sass.lhs.sub = MakeExpr(new ArrayList<>());
            sass.rhs = decl.val;
            ass.setOrigin(decl.getOrigin());
            ass.ass.add(sass);
            result.add(ass);
        }
        /*********************************************************
         * pc := entry point of ast.to                           *
         *********************************************************/
        result.add(UpdatePC(peTo.iPC));
        return result;
    }

    /***********************************************************************
     * Generate sequence of statements corresponding to call followed by a  *
     * goto.                                                                *
     ***********************************************************************/
    private ArrayList<AST.Assign> ExplodeCallGoto(final AST.CallGoto ast, final String next) throws PcalTranslateException {
        final AST.Call call = new AST.Call(pcalParams);
        call.to = ast.to;
        call.args = ast.args;
        call.line = ast.line;
        call.col = ast.col;
        call.setOrigin(ast.getOrigin());
        return ExplodeCall(call, ast.after);
    }

    public static class BoolObj {
        /*********************************************************************
         * We need to pass a boolean as an element of a triple.  But the      *
         * brain-damaged Java language makes that impossible.  While we can   *
         * put booleans in a vector, there's no way to get them out.  We can  *
         * only extract objects from a vector.  So we define an class         *
         * BoolObj of objects containing a boolean val field.  The default    *
         * object has val field equal to true.                                *
         *********************************************************************/
        boolean val = true;
    }
}
