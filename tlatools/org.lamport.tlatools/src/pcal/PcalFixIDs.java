/***************************************************************************
 * CLASS PcalFixIDs                                                         *
 * last modified on Wed 12 January 2011 at 18:33:34 PST by lamport          *
 *      modified on Tue 24 Jan 2006 at 13:21:20 PST by lamport              *
 *      modified on Tue 30 Aug 2005 at 19:30:45 UT by keith                 *
 *                                                                          *
 * Given an AST (not necessarily exploded), change the ids to their         *
 *   disambiguated values. There is one public method in this class:        *
 *                                                                          *
 *   void Fix (AST ast, PcalSymTab stab)                                    *
 *                                                                          *
 * This also fixes the tables st.procs and st.processes.                    *
 *                                                                          *
 * In Jan 2011, modified the FixProcedure and FixProcess methods as         *
 * part of the enhancement of Version 1.5 to allow fairness                 *
 * modifiers on labels.                                                     *
 ****************************************************************************/

package pcal;

import pcal.exception.PcalFixIDException;
import pcal.exception.TLAExprException;

import java.util.ArrayList;

public class PcalFixIDs {
    private static PcalSymTab st = null;

    public static void Fix(final AST ast, final PcalSymTab stab) throws PcalFixIDException {
        st = stab;
        FixSym(ast, "");
        // Fix entry point for uniprocess algorithm
        if (st.iPC != null)
            st.iPC = st.UseThis(PcalSymTab.LABEL, st.iPC, "");
    }

    private static void FixSym(final AST ast, final String context) throws PcalFixIDException {
        if (ast instanceof AST.Uniprocess obj)
            FixUniprocess(obj, context);
        else if (ast instanceof AST.Multiprocess obj)
            FixMultiprocess(obj, context);
        else if (ast instanceof AST.Procedure obj)
            FixProcedure(obj, context);
        else if (ast instanceof AST.Process obj)
            FixProcess(obj, context);
        else if (ast instanceof AST.LabeledStmt obj)
            FixLabeledStmt(obj, context);
        else if (ast instanceof AST.While obj)
            FixWhile(obj, context);
        else if (ast instanceof AST.Assign obj)
            FixAssign(obj, context);
        else if (ast instanceof AST.SingleAssign obj)
            FixSingleAssign(obj, context);
        else if (ast instanceof AST.Lhs obj)
            FixLhs(obj, context);
        else if (ast instanceof AST.If obj)
            FixIf(obj, context);
        else if (ast instanceof AST.With obj)
            FixWith(obj, context);
        else if (ast instanceof AST.When obj)
            FixWhen(obj, context);
        else if (ast instanceof AST.PrintS obj)
            FixPrintS(obj, context);
        else if (ast instanceof AST.Assert obj)
            FixAssert(obj, context);
        else if (ast instanceof AST.Skip obj)
            FixSkip(obj, context);
        else if (ast instanceof AST.LabelIf obj)
            FixLabelIf(obj, context);
        else if (ast instanceof AST.Call obj)
            FixCall(obj, context);
        else if (ast instanceof AST.Return obj)
            FixReturn(obj, context);
        else if (ast instanceof AST.CallReturn obj)
            FixCallReturn(obj, context);
        else if (ast instanceof AST.CallGoto obj)
            FixCallGoto(obj, context);
        else if (ast instanceof AST.Goto obj)
            FixGoto(obj, context);

        /*******************************************************************
         * Handling of Either and LabelEither added by LL on 24 Jan 2006.   *
         *******************************************************************/
        else if (ast instanceof AST.Either obj)
            FixEither(obj, context);
        else if (ast instanceof AST.LabelEither obj)
            FixLabelEither(obj, context);
        else PcalDebug.ReportBug("Unexpected AST type" + ast);
    }

    private static void FixUniprocess(final AST.Uniprocess ast, final String context) throws PcalFixIDException {
        for (int i = 0; i < ast.decls.size(); i++)
            FixVarDecl(ast.decls.get(i), "");
        for (int i = 0; i < ast.prcds.size(); i++)
            FixProcedure(ast.prcds.get(i), "");
        for (int i = 0; i < ast.body.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.body.get(i), "");
    }

    private static void FixMultiprocess(final AST.Multiprocess ast, final String context) throws PcalFixIDException {
        for (int i = 0; i < ast.decls.size(); i++)
            FixVarDecl(ast.decls.get(i), "");

        // procedureNames and proceduresCalled represents the mapping
        // from procedure Names to the set of names of procedures that
        // they call.
        final ArrayList<String> procedureNames = new ArrayList<>();   // ArrayList of Strings
        final ArrayList<ArrayList<String>> proceduresCalled = new ArrayList<>(); // ArrayList of Vectors of Strings
        for (int i = 0; i < ast.prcds.size(); i++) {
            final AST.Procedure prcd = ast.prcds.get(i);
            FixProcedure(prcd, "");
// System.out.println("Start\n" + prcd.toString());
            procedureNames.add(prcd.name);
            proceduresCalled.add(prcd.proceduresCalled);
        }
        // We now use the Floyd-Warshall algorithm to compute the transitive
        //  closure of the procedures' call graph, as represented by
        // the proceduresNames and proceduresCalled vectors.  This algorithm
        // is in the file FloydWarshall.tla, appended to the end of this
        // file.

        // We first initialize the algorithm's main variable, path, where
        // path[i][j] will be true iff the i-th procedure calls (perhaps
        // indirectly the j-th procedure.  (Java counting.)  
        //
        // On 2 April 2013, LL discovered that the initialization code actually
        // set path[i][j] true iff the j-th procedure calls the i-th procedure,
        // resulting in the proceduresCalled field of the AST.Procedure object
        // to list the procedures that call the given procedure.  He fixed this
        final int n = procedureNames.size();
        final boolean[][] path = new boolean[n][];
        for (int i = 0; i < n; i++) {
            path[i] = new boolean[n];
            // following commented out 2 Apr 2013
            // String nm = (String) procedureNames.get(i);
            for (int j = 0; j < n; j++) {
                // following commented out 2 Apr 2013
                // path[i][j] = (-1 != nameToNum(nm, (ArrayList) proceduresCalled.get(j)));

                // following added 2 Apr 2013
                final String nm = procedureNames.get(j);
                path[i][j] = (-1 != nameToNum(nm, proceduresCalled.get(i)));
            }
        }

        // Here is the main loop of the Floyd-Warshall algorithm.
        for (int k = 0; k < n; k++) {
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    path[i][j] = path[i][j] || (path[i][k] && path[k][j]);
                }
            }
        }

        // We now set the procedures' proceduresCalled fields to the
        // set of procedures called directly or indirectly.  This is
        // unnecessary, and should be commented out.
        for (int i = 0; i < ast.prcds.size(); i++) {
            final AST.Procedure prcd = ast.prcds.get(i);
            final ArrayList<String> pCalled = new ArrayList<>();
            for (int j = 0; j < n; j++) {
                if (path[i][j]) {
                    pCalled.add(procedureNames.get(j));
                }
            }
            prcd.proceduresCalled = pCalled;
// System.out.println(prcd.toString());            
        }

        for (int i = 0; i < ast.procs.size(); i++) {
            final AST.Process proc = ast.procs.get(i);
            FixProcess(proc, "");

            // We now fix proc.proceduresCalled by, for each procedure p in
            // it, we add all the procedures that p calls.
            final ArrayList<String> pCalled = proc.proceduresCalled;
            for (int j = 0; j < pCalled.size(); j++) {
                // Set idx to the value such that pCalled.get(j)
                // is the name of the idx-th element in procedureNames.
                final String pName = pCalled.get(j);
                final int pNum = nameToNum(pName, procedureNames);
                if (pNum == -1) {
                    // For some reason, this originally called PcalDebug.ReportBug.
                    // Since it can occur just because there is no procedure by that
                    // name in the code, it occurs on an error.  Fixed 31 May 2013 by LL.
                    // This fix caused the for loop that follows to throw an ArrayIndexOutOfBounds
                    // exception.  When run from the Toolbox, this caused the error message
                    // to be lost and the Translate command to fail with no message.
                    // It appears that it's not necessary to report the error here, because
                    // it will be caught later.  Moreover, when caught later, the location
                    // of the bad procedure name is indicated.  That location doesn't seem to
                    // available here.  However, I'm hesitant to remove the error report in case
                    // the error isn't caught later in all cases.  So I have added the return
                    // to avoid the exception.  Hopefully, no further exceptions can be caused
                    // by the error.  However, I don't know how to make sure that's the
                    // case without figuring out how the code works.
                    // I also removed an unhelpful part of the message.  LL 30 Aug 2015
                    PcalDebug.reportError(
                            "Could not find procedure name `" + pName + "'"
                            // + "' in method FixMultiprocess"
                    );
                    return; // Added 30 Aug 2015

                }
                // For each k such that path[pNum][k] is true
                // (meaning that procedure number pNum calls
                // procedure number k), add 
                // procedureNames.get(k) to proc.proceduresCalled
                // if it is not already in it.
                for (int k = 0; k < n; k++) {
                    if (path[pNum][k]) {
                        final String callee = procedureNames.get(k);
                        if (!InVector(callee, proc.proceduresCalled)) {
                            proc.proceduresCalled.add(callee);
                        }
                    }
                }
//          System.out.println(proc.toString());                
            }
        }
    }

    /**
     * If nm is the i-th element of names, then return i.  Otherwise,
     * return -1 if nm is not any element of names.
     */
    private static int nameToNum(final String nm, final ArrayList<String> names) {
        for (int i = 0; i < names.size(); i++) {
            if (names.get(i).equals(nm)) {
                return i;
            }
        }
        return -1;
    }

    /**
     * FixProcedure modified by LL on 12 January 2011 so it also fixes the
     * plusLabels and minusLabels entries.
     */
    private static void FixProcedure(final AST.Procedure ast, final String context) throws PcalFixIDException {
        for (int i = 0; i < ast.decls.size(); i++)
            FixPVarDecl(ast.decls.get(i), ast.name);
        for (int i = 0; i < ast.params.size(); i++)
            FixPVarDecl(ast.params.get(i), ast.name);
        for (int i = 0; i < ast.body.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.body.get(i), ast.name);
        final PcalSymTab.ProcedureEntry p =
                st.procs.get(st.FindProc(ast.name));
        ast.plusLabels.replaceAll(s -> st.UseThis(PcalSymTab.LABEL, s, ast.name));
        ast.minusLabels.replaceAll(s -> st.UseThis(PcalSymTab.LABEL, s, ast.name));
        p.iPC = st.UseThis(PcalSymTab.LABEL, p.iPC, ast.name);
        ast.name = st.UseThis(PcalSymTab.PROCEDURE, ast.name, "");
        p.name = ast.name;
    }

    /**
     * FixProcess modified by LL on 12 January 2011 so it also fixes the
     * plusLabels and minusLabels entries.
     */
    private static void FixProcess(final AST.Process ast, final String context) throws PcalFixIDException {
        for (int i = 0; i < ast.decls.size(); i++)
            FixVarDecl(ast.decls.get(i), ast.name);
        for (int i = 0; i < ast.body.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.body.get(i), ast.name);
        final PcalSymTab.ProcessEntry p =
                st.processes.get(st.FindProcess(ast.name));
        ast.plusLabels.replaceAll(s -> st.UseThis(PcalSymTab.LABEL, s, ast.name));
        ast.minusLabels.replaceAll(s -> st.UseThis(PcalSymTab.LABEL, s, ast.name));
        p.iPC = st.UseThis(PcalSymTab.LABEL, p.iPC, ast.name);
        ast.name = st.UseThis(PcalSymTab.PROCESS, ast.name, "");
        p.name = ast.name;
    }

    private static void FixVarDecl(final AST.VarDecl ast, final String context) throws PcalFixIDException {
        ast.var = st.UseThisVar(ast.var, context);
        FixExpr(ast.val, context);
    }

    private static void FixPVarDecl(final AST.PVarDecl ast, final String context) throws PcalFixIDException {
        ast.var = st.UseThisVar(ast.var, context);
        FixExpr(ast.val, context);
    }

    private static void FixLabeledStmt(final AST.LabeledStmt ast, final String context) throws PcalFixIDException {
        ast.label = st.UseThis(PcalSymTab.LABEL, ast.label, context);
        for (int i = 0; i < ast.stmts.size(); i++)
            FixSym(ast.stmts.get(i), context);
    }

    private static void FixWhile(final AST.While ast, final String context) throws PcalFixIDException {
        for (int i = 0; i < ast.unlabDo.size(); i++)
            FixSym(ast.unlabDo.get(i), context);
        for (int i = 0; i < ast.labDo.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.labDo.get(i), context);
        /*******************************************************************
         * The following statement added by LL on 24 Jan 2006.              *
         *******************************************************************/
        FixExpr(ast.test, context);
    }

    private static void FixAssign(final AST.Assign ast, final String context) throws PcalFixIDException {
        for (int i = 0; i < ast.ass.size(); i++)
            FixSingleAssign(ast.ass.get(i), context);
    }

    private static void FixSingleAssign(final AST.SingleAssign ast, final String context) throws PcalFixIDException {
        FixLhs(ast.lhs, context);
        FixExpr(ast.rhs, context);
    }

    private static void FixLhs(final AST.Lhs ast, final String context) throws PcalFixIDException {
        ast.var = st.UseThisVar(ast.var, context);
        FixExpr(ast.sub, context);
    }

    private static void FixIf(final AST.If ast, final String context) throws PcalFixIDException {
        for (int i = 0; i < ast.Then.size(); i++)
            FixSym(ast.Then.get(i), context);
        for (int i = 0; i < ast.Else.size(); i++)
            FixSym(ast.Else.get(i), context);
        FixExpr(ast.test, context);
    }

    private static void FixWith(final AST.With ast, final String context) throws PcalFixIDException {
        FixExpr(ast.exp, context);
        for (int i = 0; i < ast.Do.size(); i++)
            FixSym(ast.Do.get(i), context);
    }

    private static void FixWhen(final AST.When ast, final String context) throws PcalFixIDException {
        FixExpr(ast.exp, context);
    }

    private static void FixPrintS(final AST.PrintS ast, final String context) throws PcalFixIDException {
        FixExpr(ast.exp, context);
    }

    private static void FixAssert(final AST.Assert ast, final String context) throws PcalFixIDException {
        FixExpr(ast.exp, context);
    }

    private static void FixSkip(final AST.Skip ast, final String context) {
    }

    private static void FixLabelIf(final AST.LabelIf ast, final String context) throws PcalFixIDException {
        FixExpr(ast.test, context);
        for (int i = 0; i < ast.unlabThen.size(); i++)
            FixSym(ast.unlabThen.get(i), context);
        for (int i = 0; i < ast.labThen.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.labThen.get(i), context);
        for (int i = 0; i < ast.unlabElse.size(); i++)
            FixSym(ast.unlabElse.get(i), context);
        for (int i = 0; i < ast.labElse.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.labElse.get(i), context);
    }

    private static void FixCall(final AST.Call ast, final String context) throws PcalFixIDException {
        ast.returnTo = st.UseThis(PcalSymTab.PROCEDURE, ast.returnTo, context);
        ast.to = st.UseThis(PcalSymTab.PROCEDURE, ast.to, context);
        for (int i = 0; i < ast.args.size(); i++)
            FixExpr(ast.args.get(i), context);
    }

    private static void FixReturn(final AST.Return ast, final String context) {
        ast.from = st.UseThis(PcalSymTab.PROCEDURE, ast.from, context);
    }

    private static void FixCallReturn(final AST.CallReturn ast, final String context) throws PcalFixIDException {
        ast.from = st.UseThis(PcalSymTab.PROCEDURE, ast.from, context);
        ast.to = st.UseThis(PcalSymTab.PROCEDURE, ast.to, context);
        for (int i = 0; i < ast.args.size(); i++)
            FixExpr(ast.args.get(i), context);
    }

    private static void FixCallGoto(final AST.CallGoto ast, final String context) throws PcalFixIDException {
        ast.after = st.UseThis(PcalSymTab.PROCEDURE, ast.after, context);
        ast.to = st.UseThis(PcalSymTab.PROCEDURE, ast.to, context);
        for (int i = 0; i < ast.args.size(); i++)
            FixExpr(ast.args.get(i), context);
    }

    private static void FixGoto(final AST.Goto ast, final String context) throws PcalFixIDException {
        /*
         * Report an error if the goto destination is not a label.  This check
         * added by LL on 29 Dec 2011.
         */
        if (st.FindSym(PcalSymTab.LABEL, ast.to, context) == st.symtab.size()
                && !ast.to.equals("Done")) {
            throw new PcalFixIDException("goto to non-existent label `" + ast.to +
                    "' at line " + ast.line + ", column " + ast.col);
        }
        ast.to = st.UseThis(PcalSymTab.LABEL, ast.to, context);
    }

    /***********************************************************************
     * Handling of Either and LabelEither added by LL on 24 Jan 2006.
     * @throws PcalFixIDException *
     ***********************************************************************/
    @SuppressWarnings({"rawtypes", "unchecked"})
    private static void FixEither(final AST.Either ast, final String context) throws PcalFixIDException {
        for (int i = 0; i < ast.ors.size(); i++) {
            final ArrayList<AST> orClause = (ArrayList) ast.ors.get(i);
            for (AST value : orClause) FixSym(value, context);
        }
    }

    private static void FixLabelEither(final AST.LabelEither ast, final String context) throws PcalFixIDException {
        for (int i = 0; i < ast.clauses.size(); i++) {
            final AST.Clause orClause = ast.clauses.get(i);
            for (int j = 0; j < orClause.unlabOr.size(); j++)
                FixSym(orClause.unlabOr.get(j), context);
            for (int j = 0; j < orClause.labOr.size(); j++)
                FixLabeledStmt((AST.LabeledStmt)
                                orClause.labOr.get(j),
                        context);
        }

    }

    private static void FixExpr(final TLAExpr expr, final String context) throws PcalFixIDException {
        /**
         * Set stringVec to the vector of identifiers (strings) that come from IDENT tokens
         * in expr, and set exprVect to the vector of expressions, each of which
         * contains a single token whose string is the identifier substituted for the
         * corresponding identifier of stringVec.
         */
        final ArrayList<TLAExpr> exprVec = new ArrayList<>();   // the substituting exprs
        final ArrayList<String> stringVec = new ArrayList<>(); // the substituted  ids
        for (int i = 0; i < expr.tokens.size(); i++) {
            final ArrayList<TLAToken> tv = expr.tokens.get(i);
            String useMe;
            for (final TLAToken tok : tv) {
                if (tok.type == TLAToken.IDENT) {
                    useMe = st.UseThisVar(tok.string, context);
                    if (InVector(tok.string, stringVec)
                            || useMe.equals(tok.string)) continue;
                    stringVec.add(tok.string);
                    final TLAExpr exp = new TLAExpr();
                    exp.addLine();
                    exp.addToken(new TLAToken(useMe, 0, TLAToken.IDENT));
                    exp.normalize();
                    exprVec.add(exp);
                }
            }
        }
        if (exprVec.size() > 0)
            try {
                expr.substituteForAll(exprVec, stringVec, false);
            } catch (final TLAExprException e) {
                throw new PcalFixIDException(e.getMessage());
            }
    }

    /****************************************************************/
    /* Returns whether the string is present in a vector of string. */

    /****************************************************************/
    private static boolean InVector(final String var, final ArrayList<String> v) {
        for (String s : v) if (var.equals(s)) return true;
        return false;
    }

}

/***************************  the file FloydWarshall *************************************

 --------------------------- MODULE FloydWarshall ---------------------------
 (***************************************************************************)
 (*                                                                         *)
 (* The following is the Floyd-Warshall algorithm for computing the path    *)
 (* with the smallest total weight of all paths between any two nodes in a  *)
 (* completely connected graph, where edgeCost(i,j) is the weight on the    *)
 (* edge from i to j.  At the end of the computation, path[i][j] is the     *)
 (* minimum path weight of all paths from i to j.  It assumes that the      *)
 (* nodes are numbers in 1..n.  This algorith comes from Wikipedia          *)
 (*                                                                         *)
 (*   1 (* Assume a function edgeCost(i,j) which returns the cost           *)
 (*   2    of the edge from i to j (infinity if there is none).             *)
 (*   3    Also assume that n is the number of vertices and                 *)
 (*   4    edgeCost(i,i) = 0 *)                                             *)
 (*   5                                                                     *)
 (*   6 int path[][];                                                       *)
 (*   7 (* A 2-dimensional matrix. At each step in the algorithm,           *)
 (*   8    path[i][j] is the shortest path from i to j using intermediate   *)
 (*   9    vertices (1..k-1).  Each path[i][j] is initialized to            *)
 (*  10    edgeCost(i,j). *)                                                *)
 (*  11                                                                     *)
 (*  12 procedure FloydWarshall ()                                          *)
 (*  13    for k := 1 to n                                                  *)
 (*  14       for i := 1 to n                                               *)
 (*  15          for j := 1 to n                                            *)
 (*  16             path[i][j] = min ( path[i][j], path[i][k]+path[k][j] ); *)
 (*                                                                         *)
 (* We use modify it to an algorithm for computing connectivity in a        *)
 (* directed graph.  As observed in the Wikipedia page, we just replace     *)
 (* weights by Booleans, where FALSE is equivalent to a weight of infinity  *)
 (* (not connected) and TRUE is equivalent to a weight of zero (connected). *)
 (* Then min becomes disjunction and + becomes conjunction                  *)
 (***************************************************************************)
 EXTENDS Naturals, Sequences, TLC
 (***************************************************************************)
 (* We let 1..n be the set of nodes, and Nbrs be a function such that       *)
 (* Nbrs[i] is the set of neighbors of node i, which is the set of nodes j  *)
 (* such that there is an edge from i to j.                                 *)
 (***************************************************************************)
 CONSTANT n, Nbrs

 ASSUME /\ n \in Nat
 /\ Nbrs \in [1..n -> SUBSET (1..n)]

 (***************************************************************************)
 (* To be able to express correctness, we define Connected(i, j) to be true *)
 (* for nodes i and j if there is a path from i to j.  Correctness of the   *)
 (* algorithm then means that it terminates with                            *)
 (*                                                                         *)
 (*    path[i][j] = Connected(i, j)                                         *)
 (*                                                                         *)
 (* for all nodes i and j.                                                  *)
 (*                                                                         *)
 (* To define Connected, we observe that for a directed graph with n nodes, *)
 (* there is a path from node i to node j iff there is a path from i to j   *)
 (* of length at most n.  (A path of length k is a sequence of k+1 nodes,   *)
 (* each of which has an edge from it to the next one.) We therefore define *)
 (* Paths to be the set of all paths of length between 1 and n.  (In the    *)
 (* definition, P(m) is the set of all paths with m nodes, and hence of     *)
 (* length m-1.) We then define Connected in terms of Paths.                *)
 (***************************************************************************)
 Paths == LET P(m) == { f \in [1..m -> 1..n] :
 \A q \in 1..(m-1) : f[q+1] \in Nbrs[f[q]] }
 IN  UNION {P(m) : m \in 2..(n+1)}

 Connected(i, j) ==  \E p \in Paths : p[1] = i /\ p[Len(p)] = j

 (***********************************
 options (termination)
 --algorithm FloydWarshall {
 variables path = [a \in 1..n |->
 [b \in 1..n |-> b \in Nbrs[a]]],
 i, j, k;
 { k := 1;
 while (k =< n) {
 i := 1 ;
 while (i =< n) {
 j := 1;
 while (j =< n) {
 path[i][j] := path[i][j] \/ (path[i][k] /\ path[k][j]);
 j := j+1;
 } ;
 i := i+1;
 } ;
 k := k+1
 } ;
 assert \A a, b \in 1..n : path[a][b] = Connected(a, b)
 }
 }
 ***********************************)
 \* BEGIN TRANSLATION
 \* END TRANSLATION
 =============================================================================
 \* Modification History
 \* Last modified Thu Jan 20 08:48:36 PST 2011 by lamport
 \* Created Wed Jan 19 10:05:18 PST 2011 by lamport
 *****************************************************************************************/


