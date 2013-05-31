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

import java.util.Vector;

import pcal.exception.PcalFixIDException;
import pcal.exception.TLAExprException;

public class PcalFixIDs {
    private static PcalSymTab st = null;

    public static void Fix(AST ast, PcalSymTab stab) throws PcalFixIDException {
        st = stab;
        FixSym(ast, "");
        // Fix entry point for uniprocess algorithm
        if (st.iPC != null)
            st.iPC = st.UseThis(PcalSymTab.LABEL, st.iPC, "");
    }

    private static void FixSym (AST ast, String context) throws PcalFixIDException {
        if (ast.getClass().equals(AST.UniprocessObj.getClass()))
            FixUniprocess((AST.Uniprocess) ast, context);
        else if (ast.getClass().equals(AST.MultiprocessObj.getClass()))
            FixMultiprocess((AST.Multiprocess) ast, context);
        else if (ast.getClass().equals(AST.ProcedureObj.getClass()))
            FixProcedure((AST.Procedure) ast, context);
        else if (ast.getClass().equals(AST.ProcessObj.getClass()))
            FixProcess((AST.Process) ast, context);
        else if (ast.getClass().equals(AST.LabeledStmtObj.getClass()))
            FixLabeledStmt((AST.LabeledStmt) ast, context);
        else if (ast.getClass().equals(AST.WhileObj.getClass()))
            FixWhile((AST.While) ast, context);
        else if (ast.getClass().equals(AST.AssignObj.getClass()))
            FixAssign((AST.Assign) ast, context);
        else if (ast.getClass().equals(AST.SingleAssignObj.getClass()))
            FixSingleAssign((AST.SingleAssign) ast, context);
        else if (ast.getClass().equals(AST.LhsObj.getClass()))
            FixLhs((AST.Lhs) ast, context);
        else if (ast.getClass().equals(AST.IfObj.getClass()))
            FixIf((AST.If) ast, context);
        else if (ast.getClass().equals(AST.WithObj.getClass()))
            FixWith((AST.With) ast, context);
        else if (ast.getClass().equals(AST.WhenObj.getClass()))
            FixWhen((AST.When) ast, context);
        else if (ast.getClass().equals(AST.PrintSObj.getClass()))
            FixPrintS((AST.PrintS) ast, context);
        else if (ast.getClass().equals(AST.AssertObj.getClass()))
            FixAssert((AST.Assert) ast, context);
        else if (ast.getClass().equals(AST.SkipObj.getClass()))
            FixSkip((AST.Skip) ast, context);
        else if (ast.getClass().equals(AST.LabelIfObj.getClass()))
            FixLabelIf((AST.LabelIf) ast, context);
        else if (ast.getClass().equals(AST.CallObj.getClass()))
            FixCall((AST.Call) ast, context);
        else if (ast.getClass().equals(AST.ReturnObj.getClass()))
            FixReturn((AST.Return) ast, context);
        else if (ast.getClass().equals(AST.CallReturnObj.getClass()))
            FixCallReturn((AST.CallReturn) ast, context);
        else if (ast.getClass().equals(AST.GotoObj.getClass()))
            FixGoto((AST.Goto) ast, context);

        /*******************************************************************
        * Handling of Either and LabelEither added by LL on 24 Jan 2006.   *
        *******************************************************************/
        else if (ast.getClass().equals(AST.EitherObj.getClass()))
            FixEither((AST.Either) ast, context);
        else if (ast.getClass().equals(AST.LabelEitherObj.getClass()))
            FixLabelEither((AST.LabelEither) ast, context);
        else PcalDebug.ReportBug("Unexpected AST type" + ast.toString());
    }

    private static void FixUniprocess (AST.Uniprocess ast, String context) throws PcalFixIDException {
        for (int i = 0; i < ast.decls.size(); i++)
            FixVarDecl((AST.VarDecl) ast.decls.elementAt(i), "");
        for (int i = 0; i < ast.prcds.size(); i++)
            FixProcedure((AST.Procedure) ast.prcds.elementAt(i), "");
        for (int i =0; i < ast.body.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.body.elementAt(i), "");
    }
        
    private static void FixMultiprocess (AST.Multiprocess ast, String context) throws PcalFixIDException {
        for (int i = 0; i < ast.decls.size(); i++)
            FixVarDecl((AST.VarDecl) ast.decls.elementAt(i), "");
        
        // procedureNames and proceduresCalled represents the mapping
        // from procedure Names to the set of names of procedures that
        // they call.
        Vector  procedureNames = new Vector();   // Vector of Strings
        Vector  proceduresCalled = new Vector(); // Vector of Vectors of Strings
        for (int i = 0; i < ast.prcds.size(); i++) {
            AST.Procedure prcd = (AST.Procedure) ast.prcds.elementAt(i);
            FixProcedure(prcd, "");
// System.out.println("Start\n" + prcd.toString());
            procedureNames.addElement(prcd.name);
            proceduresCalled.addElement(prcd.proceduresCalled);
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
        int n = procedureNames.size();
        boolean path[][] = new boolean[n][] ;
        for (int i=0; i < n; i++) {
            path[i] = new boolean[n];
            // following commented out 2 Apr 2013
            // String nm = (String) procedureNames.elementAt(i);
            for (int j = 0; j < n; j++) {
                // following commented out 2 Apr 2013
                // path[i][j] = (-1 != nameToNum(nm, (Vector) proceduresCalled.elementAt(j)));
                
                // following added 2 Apr 2013
                String nm = (String) procedureNames.elementAt(j);
                path[i][j] = (-1 != nameToNum(nm, (Vector) proceduresCalled.elementAt(i)));
            }
        }
        
        // Here is the main loop of the Floyd-Warshall algorithm.
        for (int k=0 ; k < n; k++) {
            for (int i = 0; i < n ; i++) {
                for (int j = 0; j < n; j++) {
                    path[i][j] = path[i][j] || (path[i][k] && path[k][j]); 
                }
            }
        }
        
        // We now set the procedures' proceduresCalled fields to the
        // set of procedures called directly or indirectly.  This is
        // unnecessary, and should be commented out.
        for (int i = 0; i < ast.prcds.size(); i++) {
            AST.Procedure prcd = (AST.Procedure) ast.prcds.elementAt(i);
            Vector pCalled = new Vector();
            for (int j = 0; j < n; j++) {
                if (path[i][j]) {
                    pCalled.addElement(procedureNames.elementAt(j));
                }
            }
            prcd.proceduresCalled = pCalled;
// System.out.println(prcd.toString());            
        }
        
        for (int i = 0; i < ast.procs.size(); i++) {
            AST.Process proc = (AST.Process) ast.procs.elementAt(i);
            FixProcess(proc, "");
            
            // We now fix proc.proceduresCalled by, for each procedure p in
            // it, we add all the procedures that p calls.
            Vector pCalled = proc.proceduresCalled;
            for (int j = 0; j < pCalled.size(); j++) {
                // Set idx to the value such that pCalled.elementAt(j)
                // is the name of the idx-th element in procedureNames.
                String pName = (String) pCalled.elementAt(j);
                int pNum = nameToNum(pName, procedureNames);
                if (pNum == -1) {
                	// For some reason, this originally called PcalDebug.ReportBug.
                	// Since it can occur just because there is no procedure by that
                	// name in the code, it occurs on an error.  Fixed 31 May 2013 by LL.
                    PcalDebug.reportError(
                     "Could not find procedure name `" + pName +
                     "' in method FixMultiprocess");
                }
                // For each k such that path[pNum][k] is true
                // (meaning that procedure number pNum calls
                // procedure number k), add 
                // procedureNames.elementAt(k) to proc.proceduresCalled
                // if it is not already in it.
                for (int k = 0; k < n; k++) {
                  if (path[pNum][k]) {
                      String callee = (String) procedureNames.elementAt(k);
                      if (! InVector(callee, proc.proceduresCalled)) {
                          proc.proceduresCalled.addElement(callee); 
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
     * @return
     */
    private static int nameToNum(String nm, Vector names) {
        for (int i = 0; i < names.size(); i++) {
            if (names.elementAt(i).equals(nm)) {
                return i;
            }
        }
        return -1;
    }
    /**
     * FixProcedure modified by LL on 12 January 2011 so it also fixes the
     * plusLabels and minusLabels entries.
     * 
     * @param ast
     * @param context
     * @throws PcalFixIDException
     */
    private static void FixProcedure (AST.Procedure ast, String context) throws PcalFixIDException {
        for (int i = 0; i < ast.decls.size(); i++)
            FixPVarDecl((AST.PVarDecl) ast.decls.elementAt(i), ast.name);
        for (int i = 0; i < ast.params.size(); i++)
            FixPVarDecl((AST.PVarDecl) ast.params.elementAt(i), ast.name);
        for (int i = 0; i < ast.body.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.body.elementAt(i), ast.name);
        PcalSymTab.ProcedureEntry p = 
            (PcalSymTab.ProcedureEntry)
            st.procs.elementAt(st.FindProc(ast.name));
        for (int i = 0; i < ast.plusLabels.size(); i++) {
        	String lbl = (String) ast.plusLabels.elementAt(i);
        	String newLbl = st.UseThis(PcalSymTab.LABEL, lbl, ast.name);
        	ast.plusLabels.setElementAt(newLbl, i) ;
        }
       for (int i = 0; i < ast.minusLabels.size(); i++) {
	       String lbl = (String) ast.minusLabels.elementAt(i);
	       String newLbl = st.UseThis(PcalSymTab.LABEL, lbl, ast.name);
	       ast.minusLabels.setElementAt(newLbl, i) ;
         }
        p.iPC = st.UseThis(PcalSymTab.LABEL, p.iPC, ast.name);
        ast.name = st.UseThis(PcalSymTab.PROCEDURE, ast.name, "");
        p.name = ast.name;
    }
        
    /**
     * FixProcess modified by LL on 12 January 2011 so it also fixes the
     * plusLabels and minusLabels entries.
     * @param ast
     * @param context
     * @throws PcalFixIDException
     */
    private static void FixProcess(AST.Process ast, String context) throws PcalFixIDException {
        for (int i = 0; i < ast.decls.size(); i++)
            FixVarDecl((AST.VarDecl) ast.decls.elementAt(i), ast.name);
        for (int i = 0; i < ast.body.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.body.elementAt(i), ast.name);
        PcalSymTab.ProcessEntry p = 
            (PcalSymTab.ProcessEntry)
            st.processes.elementAt(st.FindProcess(ast.name));
        for (int i = 0; i < ast.plusLabels.size(); i++) {
        	String lbl = (String) ast.plusLabels.elementAt(i);
        	String newLbl = st.UseThis(PcalSymTab.LABEL, lbl, ast.name);
        	ast.plusLabels.setElementAt(newLbl, i) ;
        }
       for (int i = 0; i < ast.minusLabels.size(); i++) {
         String lbl = (String) ast.minusLabels.elementAt(i);
         String newLbl = st.UseThis(PcalSymTab.LABEL, lbl, ast.name);
         ast.minusLabels.setElementAt(newLbl, i) ;
         }
        p.iPC = st.UseThis(PcalSymTab.LABEL, p.iPC, ast.name);
        ast.name = st.UseThis(PcalSymTab.PROCESS, ast.name, "");
        p.name = ast.name;
   }

    private static void FixVarDecl(AST.VarDecl ast, String context) throws PcalFixIDException {
        ast.var = st.UseThisVar(ast.var, context);
        FixExpr(ast.val, context);
    }

    private static void FixPVarDecl(AST.PVarDecl ast, String context) throws PcalFixIDException {
        ast.var = st.UseThisVar(ast.var, context);
        FixExpr(ast.val, context);
    }

    private static void FixLabeledStmt(AST.LabeledStmt ast, String context) throws PcalFixIDException {
        ast.label = st.UseThis(PcalSymTab.LABEL, ast.label, context);
        for (int i = 0; i < ast.stmts.size(); i++)
            FixSym((AST) ast.stmts.elementAt(i), context);
    }

    private static void FixWhile(AST.While ast, String context) throws PcalFixIDException {
        for (int i = 0; i < ast.unlabDo.size(); i++)
            FixSym((AST) ast.unlabDo.elementAt(i), context);
        for (int i = 0; i < ast.labDo.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.labDo.elementAt(i), context);
        /*******************************************************************
        * The following statement added by LL on 24 Jan 2006.              *
        *******************************************************************/
        FixExpr((TLAExpr) ast.test, context);
    }

    private static void FixAssign(AST.Assign ast, String context) throws PcalFixIDException {
        for (int i = 0; i < ast.ass.size(); i++)
            FixSingleAssign((AST.SingleAssign) ast.ass.elementAt(i), context);
    }

    private static void FixSingleAssign(AST.SingleAssign ast, String context) throws PcalFixIDException {
        FixLhs(ast.lhs, context);
        FixExpr(ast.rhs, context);
    }

    private static void FixLhs(AST.Lhs ast, String context) throws PcalFixIDException {
        ast.var = st.UseThisVar(ast.var, context);
        FixExpr(ast.sub, context);
    }

    private static void FixIf(AST.If ast, String context) throws PcalFixIDException {
        for (int i = 0; i < ast.Then.size(); i++)
            FixSym((AST) ast.Then.elementAt(i), context);
        for (int i = 0; i < ast.Else.size(); i++)
            FixSym((AST) ast.Else.elementAt(i), context);
        FixExpr((TLAExpr) ast.test, context);
   }

    private static void FixWith(AST.With ast, String context) throws PcalFixIDException {
        FixExpr(ast.exp, context);
        for (int i = 0; i < ast.Do.size(); i++)
            FixSym((AST) ast.Do.elementAt(i), context);
    }

    private static void FixWhen(AST.When ast, String context) throws PcalFixIDException {
        FixExpr(ast.exp, context);
   }

    private static void FixPrintS(AST.PrintS ast, String context) throws PcalFixIDException {
        FixExpr(ast.exp, context);
    }

    private static void FixAssert(AST.Assert ast, String context) throws PcalFixIDException {
        FixExpr(ast.exp, context);
   }

    private static void FixSkip(AST.Skip ast, String context) {
    }

    private static void FixLabelIf(AST.LabelIf ast, String context) throws PcalFixIDException {
        FixExpr(ast.test, context);
        for (int i = 0 ; i < ast.unlabThen.size(); i++)
            FixSym((AST) ast.unlabThen.elementAt(i), context);
        for (int i = 0; i < ast.labThen.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.labThen.elementAt(i), context);
        for (int i = 0; i < ast.unlabElse.size(); i++)
            FixSym((AST) ast.unlabElse.elementAt(i), context);
        for (int i = 0;  i < ast.labElse.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.labElse.elementAt(i), context);
    }

    private static void FixCall(AST.Call ast, String context) throws PcalFixIDException {
        ast.returnTo = st.UseThis(PcalSymTab.PROCEDURE, ast.returnTo, context);
        ast.to = st.UseThis(PcalSymTab.PROCEDURE, ast.to, context);
        for (int i = 0; i < ast.args.size(); i++)
            FixExpr((TLAExpr) ast.args.elementAt(i), context);
    }

    private static void FixReturn(AST.Return ast, String context) {
        ast.from = st.UseThis(PcalSymTab.PROCEDURE, ast.from, context);
    }

    private static void FixCallReturn(AST.CallReturn ast, String context) throws PcalFixIDException {
        ast.from = st.UseThis(PcalSymTab.PROCEDURE, ast.from, context);
        ast.to = st.UseThis(PcalSymTab.PROCEDURE, ast.to, context);
        for (int i = 0; i < ast.args.size(); i++)
            FixExpr((TLAExpr) ast.args.elementAt(i), context);
    }

    private static void FixGoto(AST.Goto ast, String context) throws PcalFixIDException {
        /*
         * Report an error if the goto destination is not a label.  This check
         * added by LL on 29 Dec 2011.
         */
        if (st.FindSym(PcalSymTab.LABEL, ast.to, context) == st.symtab.size()
              && ! ast.to.equals("Done")) {
            throw new PcalFixIDException("goto to non-existent label `" + ast.to + 
                    "' at line " + ast.line + ", column " + ast.col);
        }
        ast.to = st.UseThis(PcalSymTab.LABEL, ast.to, context);
    }

    /***********************************************************************
    * Handling of Either and LabelEither added by LL on 24 Jan 2006.       
     * @throws PcalFixIDException *
    ***********************************************************************/
    private static void FixEither(AST.Either ast, String context) throws PcalFixIDException {
        for (int i = 0; i < ast.ors.size(); i++)
              { Vector orClause = (Vector) ast.ors.elementAt(i) ;
                for (int j = 0; j < orClause.size(); j++)
                  FixSym((AST) orClause.elementAt(j), context);
               } ;
    }

    private static void FixLabelEither(AST.LabelEither ast, String context) throws PcalFixIDException {
        for (int i = 0; i < ast.clauses.size(); i++)
              { AST.Clause orClause = (AST.Clause) ast.clauses.elementAt(i) ;
                for (int j = 0; j < orClause.unlabOr.size(); j++)
                  FixSym((AST) orClause.unlabOr.elementAt(j), context);
                for (int j = 0; j < orClause.labOr.size(); j++)
                  FixLabeledStmt((AST.LabeledStmt) 
                                   orClause.labOr.elementAt(j), 
                                  context);
               } ;

    }

    private static void FixExpr(TLAExpr expr, String context) throws PcalFixIDException {
        /**
         * Set stringVec to the vector of identifiers (strings) that come from IDENT tokens
         * in expr, and set exprVect to the vector of expressions, each of which
         * contains a single token whose string is the identifier substituted for the
         * corresponding identifier of stringVec.
        */
        Vector exprVec = new Vector();   // the substituting exprs
        Vector stringVec = new Vector(); // the substituted  ids
        Vector tokenVec = new Vector();  // the 

        for (int i = 0; i < expr.tokens.size(); i++) {
            Vector tv = (Vector) expr.tokens.elementAt(i);
            String useMe = null;
            for (int j = 0; j < tv.size(); j++) {
                int shift = 0;
                TLAToken tok = (TLAToken) tv.elementAt(j);
                tok.column = tok.column + shift;
                if (tok.type == TLAToken.IDENT) {
                    useMe = st.UseThisVar(tok.string, context);
                    if (InVector(tok.string, stringVec)
                        || useMe.equals(tok.string)) continue;
                    stringVec.addElement(tok.string);
                    TLAExpr exp = new TLAExpr();
                    exp.addLine();
                    exp.addToken(new TLAToken(useMe, 0, TLAToken.IDENT));
                    exp.normalize();
                    exprVec.addElement(exp);
                }
            }
        }
        if (exprVec.size() > 0)
            try
            {
                expr.substituteForAll(exprVec,  stringVec, false);
            } catch (TLAExprException e)
            {
                throw new PcalFixIDException(e.getMessage());
            }
    }

    /****************************************************************/
    /* Returns whether the string is present in a vector of string. */
    /****************************************************************/
    private static boolean InVector(String var, Vector v) {
        for (int i = 0; i < v.size(); i++)
            if (var.equals((String) v.elementAt(i))) return true;
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


