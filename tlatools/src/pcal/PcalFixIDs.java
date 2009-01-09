/***************************************************************************
* CLASS PcalFixIDs                                                         *
* last modified on Tue 24 Jan 2006 at 13:21:20 PST by lamport               *
*      modified on Tue 30 Aug 2005 at 19:30:45 UT by keith                 *
*                                                                          *
* Given an AST (not necessarily exploded), change the ids to ther          *
*   disambiguated values. There is one public method in this class:        *
*                                                                          *
*   void Fix (AST ast, PcalSymTab stab)                                    *
*                                                                          *
* This also fixes the tables st.procs and st.processes.                    *
*                                                                          *
****************************************************************************/

package pcal;

import java.util.Vector;

public class PcalFixIDs {
    private static PcalSymTab st = null;

    public static void Fix(AST ast, PcalSymTab stab) {
        st = stab;
        FixSym(ast, "");
        // Fix entry point for uniprocess algorithm
        if (st.iPC != null)
            st.iPC = st.UseThis(PcalSymTab.LABEL, st.iPC, "");
    }

    private static void FixSym (AST ast, String context) {
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

    private static void FixUniprocess (AST.Uniprocess ast, String context) {
        for (int i = 0; i < ast.decls.size(); i++)
            FixVarDecl((AST.VarDecl) ast.decls.elementAt(i), "");
        for (int i = 0; i < ast.prcds.size(); i++)
            FixProcedure((AST.Procedure) ast.prcds.elementAt(i), "");
        for (int i =0; i < ast.body.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.body.elementAt(i), "");
    }
        
    private static void FixMultiprocess (AST.Multiprocess ast, String context) {
        for (int i = 0; i < ast.decls.size(); i++)
            FixVarDecl((AST.VarDecl) ast.decls.elementAt(i), "");
        for (int i = 0; i < ast.prcds.size(); i++)
            FixProcedure((AST.Procedure) ast.prcds.elementAt(i), "");
        for (int i = 0; i < ast.procs.size(); i++)
            FixProcess((AST.Process) ast.procs.elementAt(i), "");
    }

    private static void FixProcedure (AST.Procedure ast, String context) {
        for (int i = 0; i < ast.decls.size(); i++)
            FixPVarDecl((AST.PVarDecl) ast.decls.elementAt(i), ast.name);
        for (int i = 0; i < ast.params.size(); i++)
            FixPVarDecl((AST.PVarDecl) ast.params.elementAt(i), ast.name);
        for (int i = 0; i < ast.body.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.body.elementAt(i), ast.name);
        PcalSymTab.ProcedureEntry p = 
            (PcalSymTab.ProcedureEntry)
            st.procs.elementAt(st.FindProc(ast.name));
        p.iPC = st.UseThis(PcalSymTab.LABEL, p.iPC, ast.name);
        ast.name = st.UseThis(PcalSymTab.PROCEDURE, ast.name, "");
        p.name = ast.name;
    }
        
    private static void FixProcess(AST.Process ast, String context) {
        for (int i = 0; i < ast.decls.size(); i++)
            FixVarDecl((AST.VarDecl) ast.decls.elementAt(i), ast.name);
        for (int i = 0; i < ast.body.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.body.elementAt(i), ast.name);
        PcalSymTab.ProcessEntry p = 
            (PcalSymTab.ProcessEntry)
            st.processes.elementAt(st.FindProcess(ast.name));
        p.iPC = st.UseThis(PcalSymTab.LABEL, p.iPC, ast.name);
        ast.name = st.UseThis(PcalSymTab.PROCESS, ast.name, "");
        p.name = ast.name;
   }

    private static void FixVarDecl(AST.VarDecl ast, String context) {
        ast.var = st.UseThisVar(ast.var, context);
        FixExpr(ast.val, context);
    }

    private static void FixPVarDecl(AST.PVarDecl ast, String context) {
        ast.var = st.UseThisVar(ast.var, context);
        FixExpr(ast.val, context);
    }

    private static void FixLabeledStmt(AST.LabeledStmt ast, String context) {
        ast.label = st.UseThis(PcalSymTab.LABEL, ast.label, context);
        for (int i = 0; i < ast.stmts.size(); i++)
            FixSym((AST) ast.stmts.elementAt(i), context);
    }

    private static void FixWhile(AST.While ast, String context) {
        for (int i = 0; i < ast.unlabDo.size(); i++)
            FixSym((AST) ast.unlabDo.elementAt(i), context);
        for (int i = 0; i < ast.labDo.size(); i++)
            FixLabeledStmt((AST.LabeledStmt) ast.labDo.elementAt(i), context);
        /*******************************************************************
        * The following statement added by LL on 24 Jan 2006.              *
        *******************************************************************/
        FixExpr((TLAExpr) ast.test, context);
    }

    private static void FixAssign(AST.Assign ast, String context) {
        for (int i = 0; i < ast.ass.size(); i++)
            FixSingleAssign((AST.SingleAssign) ast.ass.elementAt(i), context);
    }

    private static void FixSingleAssign(AST.SingleAssign ast, String context) {
        FixLhs(ast.lhs, context);
        FixExpr(ast.rhs, context);
    }

    private static void FixLhs(AST.Lhs ast, String context) {
        ast.var = st.UseThisVar(ast.var, context);
        FixExpr(ast.sub, context);
    }

    private static void FixIf(AST.If ast, String context) {
        for (int i = 0; i < ast.Then.size(); i++)
            FixSym((AST) ast.Then.elementAt(i), context);
        for (int i = 0; i < ast.Else.size(); i++)
            FixSym((AST) ast.Else.elementAt(i), context);
        FixExpr((TLAExpr) ast.test, context);
   }

    private static void FixWith(AST.With ast, String context) {
        FixExpr(ast.exp, context);
        for (int i = 0; i < ast.Do.size(); i++)
            FixSym((AST) ast.Do.elementAt(i), context);
    }

    private static void FixWhen(AST.When ast, String context) {
        FixExpr(ast.exp, context);
   }

    private static void FixPrintS(AST.PrintS ast, String context) {
        FixExpr(ast.exp, context);
    }

    private static void FixAssert(AST.Assert ast, String context) {
        FixExpr(ast.exp, context);
   }

    private static void FixSkip(AST.Skip ast, String context) {
    }

    private static void FixLabelIf(AST.LabelIf ast, String context) {
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

    private static void FixCall(AST.Call ast, String context) {
        ast.returnTo = st.UseThis(PcalSymTab.PROCEDURE, ast.returnTo, context);
        ast.to = st.UseThis(PcalSymTab.PROCEDURE, ast.to, context);
        for (int i = 0; i < ast.args.size(); i++)
            FixExpr((TLAExpr) ast.args.elementAt(i), context);
    }

    private static void FixReturn(AST.Return ast, String context) {
        ast.from = st.UseThis(PcalSymTab.PROCEDURE, ast.from, context);
    }

    private static void FixCallReturn(AST.CallReturn ast, String context) {
        ast.from = st.UseThis(PcalSymTab.PROCEDURE, ast.from, context);
        ast.to = st.UseThis(PcalSymTab.PROCEDURE, ast.to, context);
        for (int i = 0; i < ast.args.size(); i++)
            FixExpr((TLAExpr) ast.args.elementAt(i), context);
    }

    private static void FixGoto(AST.Goto ast, String context) {
        ast.to = st.UseThis(PcalSymTab.LABEL, ast.to, context);
    }

    /***********************************************************************
    * Handling of Either and LabelEither added by LL on 24 Jan 2006.       *
    ***********************************************************************/
    private static void FixEither(AST.Either ast, String context) {
        for (int i = 0; i < ast.ors.size(); i++)
              { Vector orClause = (Vector) ast.ors.elementAt(i) ;
                for (int j = 0; j < orClause.size(); j++)
                  FixSym((AST) orClause.elementAt(j), context);
               } ;
    }

    private static void FixLabelEither(AST.LabelEither ast, String context) {
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

    private static void FixExpr(TLAExpr expr, String context) {
        Vector exprVec = new Vector();   // the substituting exprs
        Vector stringVec = new Vector(); // the substituted  ids

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
            expr.substituteForAll(exprVec,  stringVec, false);
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

