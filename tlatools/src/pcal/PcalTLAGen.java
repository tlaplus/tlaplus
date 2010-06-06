package pcal;

import java.util.Vector;

import pcal.exception.PcalTLAGenException;
import pcal.exception.TLAExprException;

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
public class PcalTLAGen
{
    // Constants that control formatting
    public final static boolean boxUnderCASE = true; /* else [] at end of line  */

    // The following two variables made non-final on 9 Dec 2009 so they can
    // be set by options.  They are initialized in PcalParams.resetParams().
    public static int wrapColumn ; 
       /* If the line width will be greater than this, then try to wrap */
    public static int ssWrapColumn ; 
       // I think that this is used as follows: 
       //    when translating an assignment statement (or multiassignment?)
       //    to  var' = [var EXCEPT ...],  it begins the ... on a new line
       //    iff  the ... would begin in a column > ssWrapColumn.
       // For the time being, it is set to wrapColumn - 33.  We may want
       // to do something cleverer or else make it a user option.

    // Private class variables
    private Vector tlacode = new Vector(); /* of lines */
    private String self = null; /* for current process */
    private Vector vars = new Vector(); /* list of disamb. vars */
    private Vector pcV = new Vector(); /* list of proc vars, params */
    private Vector psV = new Vector(); /* list of process set vars */
    private PcalSymTab st = null; /* symbol table */
    private boolean mp = false; /* true if multiprocess, else unip */
    private Vector nextStep = new Vector(); /* unparam actions */
    private Vector nextStepSelf = new Vector(); /* param actions */

    /**
     * The public method: generate TLA+ as a vector of strings. 
     * @param ast the AST of the PCal
     * @param symtab the symbol table
     * @return the vector of strings with TLA+ code
     * @throws PcalTLAGenException on any unrecoverable methods
     */
    public Vector generate(AST ast, PcalSymTab symtab) throws PcalTLAGenException
    {
        st = symtab;
        GenSym(ast, "");
        return tlacode;
    }

    /****************************************************************/
    /* Returns whether the string is present in a vector of string. */
    /****************************************************************/
    private static boolean InVector(String var, Vector v)
    {
        for (int i = 0; i < v.size(); i++)
            if (var.equals((String) v.elementAt(i)))
                return true;
        return false;
    }

    /******************************************************/
    /* True if var is in the list of procedure variables. */
    /******************************************************/
    private boolean IsProcedureVar(String var)
    {
        return InVector(var, pcV);
    }

    /****************************************************/
    /* True if var is in the list of process variables. */
    /****************************************************/
    private boolean IsProcessSetVar(String var)
    {
        return InVector(var, psV);
    }

    /**********************************************/
    /* Returns a string of length n of all spaces */
    /**********************************************/
    private static String NSpaces(int n)
    {
        StringBuffer sb = new StringBuffer();
        AddSpaces(sb, n);
        return sb.toString();
    }

    /*********************************************/
    /* Appends n spaces to the string buffer sb. */
    /*********************************************/
    private static void AddSpaces(StringBuffer sb, int num)
    {
        for (int i = 0; i < num; i++)
            sb.append(" ");
    }

    /****************************************/
    /* True if expr is an empty expression. */
    /****************************************/
    private static boolean EmptyExpr(TLAExpr expr)
    {
        if (expr == null)
            return true;
        if (expr.tokens == null || expr.tokens.size() == 0)
            return true;
        return false;
    }

    /*****************************************************************/
    /* Top level routines. Context is "", "procedure", or "process". */
    /**
     ****************************************************************/
    private void GenSym(AST ast, String context) throws PcalTLAGenException
    {
        if (ast.getClass().equals(AST.UniprocessObj.getClass()))
            GenUniprocess((AST.Uniprocess) ast, context);
        else if (ast.getClass().equals(AST.MultiprocessObj.getClass()))
            GenMultiprocess((AST.Multiprocess) ast, context);
        else if (ast.getClass().equals(AST.ProcedureObj.getClass()))
            GenProcedure((AST.Procedure) ast, context);
        else if (ast.getClass().equals(AST.ProcessObj.getClass()))
            GenProcess((AST.Process) ast, context);
        else if (ast.getClass().equals(AST.LabeledStmtObj.getClass()))
            GenLabeledStmt((AST.LabeledStmt) ast, context);
    }

    private void GenUniprocess(AST.Uniprocess ast, String context) throws PcalTLAGenException
    {
        mp = false;
        GenVarsAndDefs(ast.decls, ast.prcds, null, ast.defs);
        GenInit(ast.decls, ast.prcds, null);
        for (int i = 0; i < ast.prcds.size(); i++)
            GenProcedure((AST.Procedure) ast.prcds.elementAt(i), "");
        for (int i = 0; i < ast.body.size(); i++)
        {
            AST.LabeledStmt ls = (AST.LabeledStmt) ast.body.elementAt(i);
            /* Add this step to the disjunct of steps */
            nextStep.addElement(ls.label);
            GenLabeledStmt(ls, "");
        }
        GenNext();
        GenSpec();
        GenTermination();
    }

    private void GenMultiprocess(AST.Multiprocess ast, String context) throws PcalTLAGenException
    {
        mp = true;
        GenVarsAndDefs(ast.decls, ast.prcds, ast.procs, ast.defs);
        GenProcSet();
        GenInit(ast.decls, ast.prcds, ast.procs);
        for (int i = 0; i < ast.prcds.size(); i++)
            GenProcedure((AST.Procedure) ast.prcds.elementAt(i), "");
        for (int i = 0; i < ast.procs.size(); i++)
            GenProcess((AST.Process) ast.procs.elementAt(i), "");
        GenNext();
        GenSpec();
        GenTermination();
    }

    private void GenProcedure(AST.Procedure ast, String context) throws PcalTLAGenException
    {
        /* ns accumulates the disjunt of the steps of the procedure */
        StringBuffer ns = new StringBuffer();
        Vector nsV = new Vector();
        int nsC = ast.name.length() + ((mp) ? "(self)".length() : 0) + " == ".length();
        if (mp)
        {
            self = "self"; // subscript for variables is "self"
            /* Add this step to the disjunct of steps with (self) */
            nextStepSelf.addElement(ast.name + "(self)");
        } else
        {
            /* Add this step to the disjunct of steps */
            nextStep.addElement(ast.name);
        }
        for (int i = 0; i < ast.body.size(); i++)
        {
            AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.elementAt(i);
            if ((ns.length() + stmt.label.length() + " \\/ ".length() + ((mp) ? "(self)".length() : 0)) > wrapColumn
                    - nsC - " \\/ ".length())
            {
                nsV.addElement(ns.toString());
                ns = new StringBuffer();
            }
            if (ns.length() > 0)
                ns.append(" \\/ ");
            ns.append(stmt.label);
            if (mp)
                ns.append("(self)");
            GenLabeledStmt(stmt, "procedure");
        }
        nsV.addElement(ns.toString());
        // Generate definition of procedure steps
        ns = new StringBuffer();
        ns.append(ast.name);
        if (mp)
            ns.append("(self)");
        ns.append(" == ");
        ns.append((String) nsV.elementAt(0));
        tlacode.addElement(ns.toString());
        for (int i = 1; i < nsV.size(); i++)
        {
            ns = new StringBuffer(NSpaces(nsC + 2));
            ns.append(" \\/ ");
            ns.append((String) nsV.elementAt(i));
            tlacode.addElement(ns.toString());
        }
        tlacode.addElement("");
    }

    private void GenProcess(AST.Process ast, String context) throws PcalTLAGenException
    {
        /* ns accumulates the disjunt of the steps of the process */
        StringBuffer ns = new StringBuffer();
        Vector nsV = new Vector();
        boolean isSet = true;
        /************************************************************/
        /* Decide if it is a process set or not. If so, set self to */
        /* the string "self"; otherwise set self to the process id. */
        /************************************************************/
        if (ast.isEq)
        {
            self = "";
            Vector sv = ast.id.toStringVector();
            for (int v = 0; v < sv.size(); v++)
                self = self + ((String) sv.elementAt(v));
            isSet = false;
        } else
            self = "self";
        int nsC = ast.name.length() + ((isSet) ? "(self)".length() : 0) + " == ".length();
        if (isSet)
        {
            nextStepSelf.addElement(ast.name + "(self)");
        } else
            nextStep.addElement(ast.name);
        for (int i = 0; i < ast.body.size(); i++)
        {
            AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.elementAt(i);
            if ((ns.length() + stmt.label.length() + " \\/ ".length() + ((isSet) ? "(self)".length() : 0)) > wrapColumn
                    - nsC - " \\/ ".length())
            {
                nsV.addElement(ns.toString());
                ns = new StringBuffer();
            }
            if (ns.length() > 0)
                ns.append(" \\/ ");
            ns.append(stmt.label);
            if (isSet)
                ns.append("(self)");
            GenLabeledStmt(stmt, "process");
        }
        nsV.addElement(ns.toString());
        // Generate definition of process steps
        ns = new StringBuffer();
        ns.append(ast.name);
        if (isSet)
            ns.append("(self)");
        ns.append(" == ");
        ns.append((String) nsV.elementAt(0));
        tlacode.addElement(ns.toString());
        for (int i = 1; i < nsV.size(); i++)
        {
            ns = new StringBuffer(NSpaces(nsC + 2));
            ns.append(" \\/ ");
            ns.append((String) nsV.elementAt(i));
            tlacode.addElement(ns.toString());
        }
        tlacode.addElement("");
    }

    /*****************************************************/
    /* Generates an action with name equal to the label. */
    /**
     ****************************************************/
    private void GenLabeledStmt(AST.LabeledStmt ast, String context) throws PcalTLAGenException
    {
        StringBuffer sb = new StringBuffer(ast.label);
        /* c is used to determine which vars are in UNCHANGED. */
        Changed c = new Changed(vars);
        if (mp && (context.equals("procedure") || self.equals("self")))
            sb.append("(self)");
        sb.append(" == ");
        int col = sb.length();
        if (ast.stmts.size() > 1)
            sb.append("/\\ ");
        for (int i = 0; i < ast.stmts.size(); i++)
        {
            GenStmt((AST) ast.stmts.elementAt(i), c, context, sb.toString(), sb.length());
            sb = new StringBuffer(NSpaces(col));
            sb.append("/\\ ");
        }
        Vector unc = c.Unchanged(wrapColumn - col - "/\\ UNCHANGED << ".length());
        if (c.NumUnchanged() > 1)
        {
            sb = new StringBuffer(NSpaces(col));
            sb.append("/\\ UNCHANGED << ");
            int here = sb.length();
            sb.append((String) unc.elementAt(0));
            for (int i = 1; i < unc.size(); i++)
            {
                tlacode.addElement(sb.toString());
                sb = new StringBuffer(NSpaces(here));
                sb.append((String) unc.elementAt(i));
            }
            sb.append(" >>");
            tlacode.addElement(sb.toString());
        } else if (c.NumUnchanged() == 1)
            tlacode.addElement(NSpaces(col) + "/\\ UNCHANGED " + c.Unchanged());
        tlacode.addElement("");
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
    /**
     ****************************************************************/
    private void GenStmt(AST ast, Changed c, String context, String prefix, int col) throws PcalTLAGenException
    {
        if (ast.getClass().equals(AST.AssignObj.getClass()))
            GenAssign((AST.Assign) ast, c, context, prefix, col);
        else if (ast.getClass().equals(AST.IfObj.getClass()))
            GenIf((AST.If) ast, c, context, prefix, col);
        // Either case added by LL on 27 Jan 2006
        else if (ast.getClass().equals(AST.EitherObj.getClass()))
            GenEither((AST.Either) ast, c, context, prefix, col);
        else if (ast.getClass().equals(AST.WithObj.getClass()))
            GenWith((AST.With) ast, c, context, prefix, col);
        else if (ast.getClass().equals(AST.WhenObj.getClass()))
            GenWhen((AST.When) ast, c, context, prefix, col);
        else if (ast.getClass().equals(AST.PrintSObj.getClass()))
            GenPrintS((AST.PrintS) ast, c, context, prefix, col);
        else if (ast.getClass().equals(AST.AssertObj.getClass()))
            GenAssert((AST.Assert) ast, c, context, prefix, col);
        else if (ast.getClass().equals(AST.SkipObj.getClass()))
            GenSkip((AST.Skip) ast, c, context, prefix, col);
        else
            PcalDebug.ReportBug("Unexpected AST type " + ast.toString());
    }

    /*****************************************************************/
    /* Generates a sequence of single assigns. Since all of them are */
    /* executed "at the same time", we accumulate the changes in a   */
    /* separate Changed cThis, and use c to determine which vars in  */
    /* the right hand side are primed.                               */
    /**
     * ***************************************************************/
    private void GenAssign(AST.Assign ast, Changed c, String context, String prefix, int col)
            throws PcalTLAGenException
    {
        Changed cThis = new Changed(c);
        StringBuffer sb = new StringBuffer();
        Vector vlines = new Vector();
        ast.ass = SortSass(ast.ass);
        int i = 0;
        int numAssigns = 0;
        while (i < ast.ass.size())
        {
            int iFirst = i;
            AST.SingleAssign sF = (AST.SingleAssign) ast.ass.elementAt(i);
            int iLast = i;
            AST.SingleAssign sL = (AST.SingleAssign) ast.ass.elementAt(i);
            while (iLast < ast.ass.size() && sF.lhs.var.equals(sL.lhs.var))
            {
                iLast = iLast + 1;
                if (iLast < ast.ass.size())
                    sL = (AST.SingleAssign) ast.ass.elementAt(iLast);
            }
            iLast = iLast - 1;
            // All statements from iFirst to iLast are to the same variable
            if (cThis.Set(sF.lhs.var) > 1 || (iLast - iFirst > 0 && EmptyExpr(sF.lhs.sub)))
                /***********************************************************
                * The following was changed by LL on 3 Mar 06 to use       *
                * AST.location to properly report the location of an       *
                * error in a line created by expanding a macro.            *
                ***********************************************************/
                throw new PcalTLAGenException("Multiple assignment to " + sF.lhs.var, ast /* sF */);
            numAssigns = numAssigns + 1;
            Vector lines = new Vector(); // For collecting generated lines

            if (iFirst == iLast)
            {
                AST.SingleAssign sass = sF;

                TLAExpr sub = AddSubscriptsToExpr(sass.lhs.sub, SubExpr(Self(context)), c);
                TLAExpr rhs = AddSubscriptsToExpr(sass.rhs, SubExpr(Self(context)), c);
                if (mp
                        && (sass.lhs.var.equals("pc") || IsProcedureVar(sass.lhs.var) || IsProcessSetVar(sass.lhs.var) || sass.lhs.var
                                .equals("stack")))
                {
                    /* Generate assignment to variable with self subscript */
                    sb.append(sass.lhs.var);
                    sb.append("' = [");
                    int wrapCol = sb.length() + 2;
                    sb.append(sass.lhs.var);
                    sb.append(" EXCEPT ");
                    if (sb.length() + prefix.length() > ssWrapColumn)
                    {
                        lines.addElement(sb.toString());
                        sb = new StringBuffer(NSpaces(wrapCol));
                    }
                    sb.append("![");
                    sb.append(self);
                    sb.append("]");
                    int here = sb.length();
                    Vector sv = sub.toStringVector();
                    /*****************************************************
                    * Was                                                *
                    *                                                    *
                    *       Vector sv = sass.lhs.sub.toStringVector();   *
                    *                                                    *
                    * Changed by Chi Ho on 3 Aug 2006 to add             *
                    * subscript.  See bug_06_08_03.                      *
                    *****************************************************/
                    if (sv.size() > 0)
                    {
                        sb.append((String) sv.elementAt(0));
                        for (int v = 1; v < sv.size(); v++)
                        {
                            lines.addElement(sb.toString());
                            sb = new StringBuffer(NSpaces(here));
                            sb.append((String) sv.elementAt(v));
                        }
                    }
                    sb.append(" = ");
                    here = sb.length();
                    sv = rhs.toStringVector();
                    sb.append((String) sv.elementAt(0));
                    for (int v = 1; v < sv.size(); v++)
                    {
                        lines.addElement(sb.toString());
                        sb = new StringBuffer(NSpaces(here));
                        sb.append((String) sv.elementAt(v));
                    }
                    sb.append("]");
                    lines.addElement(sb.toString());
                    sb = new StringBuffer();
                } else if (!EmptyExpr(sass.lhs.sub))
                {
                    /* Generate assignment to subscripted variable */
                    sb.append(sass.lhs.var);
                    sb.append("' = [");
                    sb.append(sass.lhs.var);
                    sb.append(" EXCEPT !");
                    int here = sb.length();
                    Vector sv = sub.toStringVector();
                    sb.append((String) sv.elementAt(0));
                    for (int v = 1; v < sv.size(); v++)
                    {
                        lines.addElement(sb.toString());
                        sb = new StringBuffer(NSpaces(here));
                        sb.append((String) sv.elementAt(v));
                    }
                    sb.append(" = ");
                    here = sb.length();
                    sv = rhs.toStringVector();
                    sb.append((String) sv.elementAt(0));
                    for (int v = 1; v < sv.size(); v++)
                    {
                        lines.addElement(sb.toString());
                        sb = new StringBuffer(NSpaces(here));
                        sb.append((String) sv.elementAt(v));
                    }
                    sb.append("]");
                    lines.addElement(sb.toString());
                    sb = new StringBuffer();
                } else
                {
                    /* Generate assignment to unsubscripted variable */
                    sb.append(sass.lhs.var);
                    sb.append("' = ");
                    int here = sb.length();
                    Vector sv = Parenthesize(rhs.toStringVector());
                    /*******************************************************
                    * Call of Parenthesize added by LL on 27 Feb 2008.     *
                    * See bug_08-02-18.                                    *
                    *******************************************************/
                    for (int v = 0; v < sv.size(); v++)
                    {
                        sb.append((String) sv.elementAt(v));
                        lines.addElement(sb.toString());
                        sb = new StringBuffer(NSpaces(here));
                    }
                    sb = new StringBuffer();
                }
            } else
            {
                // Multiple assignments to the same subscripted variable.
                AST.SingleAssign sass = sF;
                sb.append(sass.lhs.var);
                sb.append("' = [");
                sb.append(sass.lhs.var);
                sb.append(" EXCEPT ");
                int cc = sb.length();
                boolean subscript = (mp && (IsProcedureVar(sass.lhs.var) || IsProcessSetVar(sass.lhs.var)));
                while (iFirst <= iLast)
                {
                    sass = (AST.SingleAssign) ast.ass.elementAt(iFirst);
                    TLAExpr sub = AddSubscriptsToExpr(sass.lhs.sub, SubExpr(Self(context)), c);
                    TLAExpr rhs = AddSubscriptsToExpr(sass.rhs, SubExpr(Self(context)), c);
                    sb.append("!");
                    int here = sb.length();
                    if (subscript)
                        sb.append("[" + Self(context) + "]");
                    Vector sv = sub.toStringVector();
                    if (sv.size() > 0)
                    {
                        sb.append((String) sv.elementAt(0));
                        for (int v = 1; v < sv.size(); v++)
                        {
                            lines.addElement(sb.toString());
                            sb = new StringBuffer(NSpaces(here));
                            sb.append((String) sv.elementAt(v));
                        }
                    }
                    sb.append(" = ");
                    here = sb.length();
                    sv = rhs.toStringVector();
                    sb.append((String) sv.elementAt(0));
                    for (int v = 1; v < sv.size(); v++)
                    {
                        lines.addElement(sb.toString());
                        sb = new StringBuffer(NSpaces(here));
                        sb.append((String) sv.elementAt(v));
                    }
                    sb.append(((iFirst == iLast) ? "]" : ","));
                    lines.addElement(sb.toString());
                    sb = new StringBuffer();
                    if (iFirst < iLast)
                        AddSpaces(sb, cc);
                    iFirst = iFirst + 1;
                }
            }

            vlines.addElement(lines);
            i = iLast + 1;
        }
        c.Merge(cThis);
        // Append generated code to tlacode
        sb = new StringBuffer(prefix);
        col = sb.length();
        if (numAssigns > 1)
            sb.append("/\\ ");
        if (vlines.size() > 0)
        {
            for (int v1 = 0; v1 < vlines.size(); v1++)
            {
                Vector vl = (Vector) vlines.elementAt(v1);
                for (int v2 = 0; v2 < vl.size(); v2++)
                {
                    sb.append((String) vl.elementAt(v2));
                    tlacode.addElement(sb.toString());
                    sb = new StringBuffer(NSpaces(col));
                    if ((v1 > 0 || numAssigns > 1) && (v2 != vl.size() - 1))
                        sb.append("   ");
                }
                sb.append("/\\ ");
            }
        }
    }

    /***********************************************************/
    /* Generate TLA+ for if statement. Each branch has its own */
    /* UNCHANGED that lists variables that were changed in the */
    /* other branch. This is a little difficult since we don't */
    /* know the UNCHANGED for the Then branch until the code   */
    /* for the Else branch is generated. So, we fix the        */
    /* line in the Then branch after the Else branch is done.  */
    /**
     **********************************************************/
    private void GenIf(AST.If ast, Changed c, String context, String prefix, int col) throws PcalTLAGenException
    {
        Changed cThen = new Changed(c);
        Changed cElse = new Changed(c);
        int lineUncThen;
        StringBuffer sb = new StringBuffer(prefix);
        TLAExpr test = null;
        test = AddSubscriptsToExpr(ast.test, SubExpr(Self(context)), c);
        Vector sv = test.toStringVector();
        sb.append("IF ");
        int here = sb.length();
        /*************************************************************
        * LL removed a bogus "- 1" here on 31 Jan 2006.              *
        *************************************************************/
        sb.append((String) sv.elementAt(0));
        for (int v = 1; v < sv.size(); v++)
        {
            tlacode.addElement(sb.toString());
            sb = new StringBuffer(NSpaces(here));
            sb.append((String) sv.elementAt(v));
        }
        tlacode.addElement(sb.toString());
        sb = new StringBuffer(NSpaces(here));
        sb.append("THEN ");
        here = sb.length();

        sb.append("/\\ ");
        for (int i = 0; i < ast.Then.size(); i++)
        {
            GenStmt((AST) ast.Then.elementAt(i), cThen, context, sb.toString(),
            /*******************************************************************
            * LL added the +3 on 18 Feb 2006 to take account of the            *
            * indentation of the "IF ".                                        *
            *******************************************************************/
            here + 3);
            sb = new StringBuffer(NSpaces(here) + "/\\ ");
        }
        lineUncThen = tlacode.size();
        tlacode.addElement(sb.toString());
        sb = new StringBuffer(NSpaces(here - "THEN ".length()) + "ELSE ");
        here = sb.length();
        if (ast.Else.size() == 0)
        {
            sb.append("/\\ TRUE");
            tlacode.addElement(sb.toString());
            sb = new StringBuffer(NSpaces(here) + "/\\ ");
        } else
        {
            sb.append("/\\ ");
            for (int i = 0; i < ast.Else.size(); i++)
            {
                GenStmt((AST) ast.Else.elementAt(i), cElse, context, sb.toString(),
                /*******************************************************************
                * LL added the +3 on 18 Feb 2006 to take account of the            *
                * indentation of the "IF ".                                        *
                *******************************************************************/
                here + 3);
                sb = new StringBuffer(NSpaces(here) + "/\\ ");
            }
        }
        // Generate UNCHANGED for the ELSE branch
        if (cElse.NumUnchanged(cThen) > 1)
        {
            Vector uncElse = cElse.Unchanged(cThen, wrapColumn - sb.length() - "UNCHANGED << ".length());
            sb.append("UNCHANGED << ");
            int cc = sb.length();
            sb.append((String) uncElse.elementAt(0));
            for (int i = 1; i < uncElse.size(); i++)
            {
                tlacode.addElement(sb.toString());
                sb = new StringBuffer(NSpaces(cc));
                sb.append((String) uncElse.elementAt(i));
            }
            sb.append(" >>");
            tlacode.addElement(sb.toString());
        } else if (cElse.NumUnchanged(cThen) == 1)
        {
            sb.append("UNCHANGED " + cElse.Unchanged(cThen));
            tlacode.addElement(sb.toString());
        }

        // Patch up the UNCHANGED for the THEN branch
        sb = new StringBuffer((String) tlacode.elementAt(lineUncThen));
        tlacode.removeElementAt(lineUncThen);
        if (cThen.NumUnchanged(cElse) > 1)
        {
            Vector uncThen = cThen.Unchanged(cElse, wrapColumn - sb.length() - "UNCHANGED << ".length());
            sb.append("UNCHANGED << ");
            int cc = sb.length();
            sb.append((String) uncThen.elementAt(0));
            for (int i = 1; i < uncThen.size(); i++)
            {
                tlacode.insertElementAt(sb.toString(), lineUncThen);
                lineUncThen = lineUncThen + 1;
                sb = new StringBuffer(NSpaces(cc));
                sb.append((String) uncThen.elementAt(i));
            }
            sb.append(" >>");
            tlacode.insertElementAt(sb.toString(), lineUncThen);
        } else if (cThen.NumUnchanged(cElse) == 1)
        {
            sb.append("UNCHANGED ");
            sb.append(cThen.Unchanged(cElse));
            tlacode.insertElementAt(sb.toString(), lineUncThen);
        }

        // Merge the change lists together
        c.Merge(cThen);
        c.Merge(cElse);
    }

    /***********************************************************************
    * Added by LL on 30 Jan 2006.                                          *
    *                                                                      *
    * Generate TLA+ for the `either' statement.  This performs the same    *
    * sort of hackery as for the `if' statement, necessitated by the       *
    * design flaw commented on above.                                      
     **
    ***********************************************************************/
    private void GenEither(AST.Either ast, Changed c, String context, String prefix, int col)
            throws PcalTLAGenException
    {
        Changed allC = new Changed(c);
        /*******************************************************************
        * Accumulates the variable changes of all the clauses.             *
        *******************************************************************/
        Changed[] cOrs = new Changed[ast.ors.size()];
        /*******************************************************************
        * cOrs[i] is the Changed vector for the i-th `or' clause.          *
        *******************************************************************/
        int[] ucLocs = new int[ast.ors.size()]; // location of unchangeds.
        /******************************************************************
        * tlaout.elementAt(ucLocs[i]) is the UNCHANGED clause for the     *
        * i-th `or' clause.                                               *
        ******************************************************************/
        StringBuffer sb = new StringBuffer(prefix);
        int prefixIndent = sb.length();
        sb.append("\\/ ");
        int here = sb.length();
        /*******************************************************************
        * The number of columns to the left of the code generated for      *
        * each `or' clause.                                                *
        *******************************************************************/

        /*********************************************************************
        * Produce the output for the clauses, but with a dummy line in       *
        * place of the UNCHANGED clause, and compute allC, cOrs, and         *
        * ucLocs.                                                            *
        *********************************************************************/
        for (int i = 0; i < ast.ors.size(); i++)
        {
            if (i != 0)
            {
                sb = new StringBuffer(NSpaces(prefixIndent) + "\\/ ");
            }
            ;
            sb.append("/\\ ");
            Vector orClause = (Vector) ast.ors.elementAt(i);
            Changed cC = new Changed(c);
            for (int j = 0; j < orClause.size(); j++)
            {
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
                GenStmt((AST) orClause.elementAt(j), cC, context, sb.toString(), here + 3); 
                sb = new StringBuffer(NSpaces(here) + "/\\ ");
            }
            ;
            cOrs[i] = cC;
            allC.Merge(cC);
            ucLocs[i] = tlacode.size();
            tlacode.addElement("Replace by UNCHANGED"); // 
        }
        ; // End of for i

        /**********************************************************************
        * Insert real UNCHANGED clauses.  Note that we have to go through     *
        * loop backwards since we will remove a line of output for each `or'  *
        * clause that doesn't get an UNCHANGED.                               *
        **********************************************************************/
        int i = ast.ors.size();
        while (i > 0)
        {
            i = i - 1;
            tlacode.removeElementAt(ucLocs[i]);
            int numUnchanged = cOrs[i].NumUnchanged(allC);
            String NotChanged = cOrs[i].Unchanged(allC);
            if (numUnchanged > 1)
            {
                tlacode.insertElementAt(NSpaces(here) + "/\\ UNCHANGED <<" + NotChanged + ">>", ucLocs[i]);
            } else if (numUnchanged == 1)
            {
                tlacode.insertElementAt(NSpaces(here) + "/\\ UNCHANGED " + NotChanged, ucLocs[i]);
            }
        }
        ;
        /**********************************************************************
        * Add the statement's unchangeds to c.                                *
        **********************************************************************/
        c.Merge(allC);
    }

    private void GenWith(AST.With ast, Changed c, String context, String prefix, int col) throws PcalTLAGenException
    {
        StringBuffer sb = new StringBuffer(prefix);
        TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
        Vector sv = exp.toStringVector();
        if (ast.isEq)
        {
            /* generate LET statement */
            sb.append("LET ");
            sb.append(ast.var);
            sb.append(" == ");
            int here = sb.length();
            sb.append((String) sv.elementAt(0));
            for (int v = 1; v < sv.size(); v++)
            {
                tlacode.addElement(sb.toString());
                sb = new StringBuffer(NSpaces(here));
                sb.append((String) sv.elementAt(v));
            }
            sb.append(" IN");
            tlacode.addElement(sb.toString());
            sb = new StringBuffer(NSpaces(col + 2));
            /*************************************************************
            * LL changed "col + 4" to "col + 2" here to correct an       *
            * alignment problem on 31 Jan 2006.                          *
            *************************************************************/
            if (ast.Do.size() > 1)
                sb.append("/\\ ");
        } else
        {
            /* generate \E statement */
            sb.append("\\E ");
            sb.append(ast.var);
            sb.append(" \\in ");
            int here = sb.length();
            sb.append((String) sv.elementAt(0));
            for (int v = 1; v < sv.size(); v++)
            {
                tlacode.addElement(sb.toString());
                sb = new StringBuffer(NSpaces(here));
                sb.append((String) sv.elementAt(v));
            }
            sb.append(":");
            tlacode.addElement(sb.toString());
            sb = new StringBuffer(NSpaces(col + 2));
            if (ast.Do.size() > 1)
                sb.append("/\\ ");
        }
        for (int i = 0; i < ast.Do.size(); i++)
        {
            GenStmt((AST) ast.Do.elementAt(i), c, context, sb.toString(), sb.length());
            sb = new StringBuffer(NSpaces(col + 2) + "/\\ ");
        }
        // tlacode.addElement(NSpaces(col) + ")");
    }

    private void GenWhen(AST.When ast, Changed c, String context, String prefix, int col) throws PcalTLAGenException
    {
        StringBuffer sb = new StringBuffer(prefix);
        TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
        Vector sv = exp.toStringVector();
        sb.append((String) sv.elementAt(0));
        for (int v = 1; v < sv.size(); v++)
        {
            tlacode.addElement(sb.toString());
            sb = new StringBuffer(NSpaces(col));
            sb.append((String) sv.elementAt(v));
        }
        tlacode.addElement(sb.toString());
    }

    private void GenPrintS(AST.PrintS ast, Changed c, String context, String prefix, int col)
            throws PcalTLAGenException
    {
        StringBuffer sb = new StringBuffer(prefix);
        TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
        Vector sv = exp.toStringVector();
        // The following modified 19 Nov 05 by LL to use PrintT instead of Print
        sb.append("PrintT(");
        sb.append((String) sv.elementAt(0));
        for (int v = 1; v < sv.size(); v++)
        {
            tlacode.addElement(sb.toString());
            sb = new StringBuffer(NSpaces(col + "PrintT(".length()));
            sb.append((String) sv.elementAt(v));
        }
        sb.append(")");
        tlacode.addElement(sb.toString());
    }

    /********************************************************/
    /* Assert(ast.expr, "Failure of assertion at... ")      */
    /**
     *******************************************************/
    private void GenAssert(AST.Assert ast, Changed c, String context, String prefix, int col)
            throws PcalTLAGenException
    {
        StringBuffer sb = new StringBuffer(prefix);
        StringBuffer sc = new StringBuffer();
        TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
        Vector sv = exp.toStringVector();
        sb.append("Assert(");
        int here = sb.length();
        sb.append((String) sv.elementAt(0));
        for (int v = 1; v < sv.size(); v++)
        {
            tlacode.addElement(sb.toString());
            sb = new StringBuffer(NSpaces(col + "Assert(".length()));
            sb.append((String) sv.elementAt(v));
        }
        sb.append(", ");
        sc.append("\"Failure of assertion at ");
        sc.append(ast.location());
        // modified on 23 Mar 2006 by LL to use locatinn() instead of
        // ast.line and ast.col
        sc.append(".\")");
        if (sb.length() + sc.length() < wrapColumn)
            tlacode.addElement(sb.toString() + sc.toString());
        else
        {
            tlacode.addElement(sb.toString());
            tlacode.addElement(NSpaces(here) + sc.toString());
        }
    }

    /********************************************************/
    /* I generate a TRUE conjunct, which is useless, but so */
    /* is a skip statement.                                 */
    /********************************************************/
    private void GenSkip(AST.Skip ast, Changed c, String context, String prefix, int col)
    {
        tlacode.addElement(prefix + "TRUE");
    }

    /***********************************************************************
    * Generate the VARIABLES declaration(s), output the TLA+ "code" from   *
    * a `define' statement, if any, and generate the definition of         *
    * `vars'.                                                              *
    *                                                                      *
    * Method renamed from GenVars and given the defs argument by LL on     *
    * 25 Jan 2006 to handle the `define' statement.                        *
    ***********************************************************************/
    private void GenVarsAndDefs(Vector globals, Vector procs, Vector processes, TLAExpr defs)
    {
        /*******************************************************************
        * lVars and gVars are vectors of strings, each element being a     *
        * variable name.  They hold the local and global variables,        *
        * respectively.                                                    *
        *******************************************************************/
        Vector lVars = new Vector();
        Vector gVars = new Vector();

        /*******************************************************************
        * Set gVars to the global variables, including pc and `stack' if   *
        * there are procedures, and add these variables to vars.           *
        *******************************************************************/
        if (globals != null)
            for (int i = 0; i < globals.size(); i++)
            {
                AST.VarDecl decl = (AST.VarDecl) globals.elementAt(i);
                gVars.addElement(decl.var);
                vars.addElement(decl.var);
            }

        gVars.addElement("pc");
        vars.addElement("pc");
        if (procs != null && procs.size() > 0)
        {
            gVars.addElement("stack");
            vars.addElement("stack");
        }
        /*******************************************************************
        * Add local procedure variables to lVars, vars, and pcV.           *
        *******************************************************************/
        if (procs != null)
            for (int i = 0; i < procs.size(); i++)
            {
                AST.Procedure proc = (AST.Procedure) procs.elementAt(i);
                if (proc.params != null)
                    for (int p = 0; p < proc.params.size(); p++)
                    {
                        AST.PVarDecl decl = (AST.PVarDecl) proc.params.elementAt(p);
                        lVars.addElement(decl.var);
                        vars.addElement(decl.var);
                        pcV.addElement(decl.var);
                    }
                if (proc.decls != null)
                    for (int p = 0; p < proc.decls.size(); p++)
                    {
                        AST.PVarDecl decl = (AST.PVarDecl) proc.decls.elementAt(p);
                        lVars.addElement(decl.var);
                        vars.addElement(decl.var);
                        pcV.addElement(decl.var);
                    }
            }

        /*******************************************************************
        * Add local process variables to lVars, vars, and psV for          *
        * variables local to process sets.                                 *
        *******************************************************************/
        if (processes != null)
            for (int i = 0; i < processes.size(); i++)
            {
                AST.Process proc = (AST.Process) processes.elementAt(i);
                if (proc.decls != null)
                    for (int p = 0; p < proc.decls.size(); p++)
                    {
                        AST.VarDecl decl = (AST.VarDecl) proc.decls.elementAt(p);
                        lVars.addElement(decl.var);
                        vars.addElement(decl.var);
                        if (!proc.isEq)
                            psV.addElement(decl.var);
                    }
            }

        /********************************************************************
        * Add a declaration of the constant defaultInitValue if it is       *
        * used.  (Added by LL on 22 Aug 2007.)                              *
        ********************************************************************/
        if (ParseAlgorithm.hasDefaultInitialization)
        {
            tlacode.addElement("CONSTANT defaultInitValue");
        }
        ;

        if (EmptyExpr(defs))
        {
            /******************************************************************
            * There is no `define' statement.  In this case, generate a       *
            * single VARIABLES statement and set gVars to vector of all       *
            * variables.                                                      *
            ******************************************************************/
            gVars.addAll(lVars);
            GenVarDecl(gVars);
        } else
        {
            /******************************************************************
            * There is a `define' statement.  In this case, must declare      *
            * global and local variables separately.  Also, set gVars to      *
            * vector of all variables.                                        *
            ******************************************************************/
            GenVarDecl(gVars);
            tlacode.addElement("");
            tlacode.addElement("(* define statement *)");
            Vector sv = defs.toStringVector();
            for (int i = 0; i < sv.size(); i++)
            {
                tlacode.addElement((String) sv.elementAt(i));
            }
            ;
            tlacode.addElement("");
            GenVarDecl(lVars);
            gVars.addAll(lVars);
        }
        ;
        tlacode.addElement("");

        /*******************************************************************
        * Generate definition of vars.                                     *
        *******************************************************************/
        StringBuffer var = new StringBuffer("vars == << ");
        StringBuffer curLine = new StringBuffer("vars == << ");
        for (int i = 0; i < gVars.size(); i++)
        {
            if (i > 0)
            {
                var.append(", ");
                curLine.append(", ");
            }
            ;
            String vbl = (String) gVars.elementAt(i);
            if (curLine.length() + vbl.length() + 1 > wrapColumn)
            {
                curLine = new StringBuffer("vars == << ");
                var.append("\n" + NSpaces("vars == << ".length()));
            }
            ;
            var.append(vbl);
            curLine.append(vbl);
        }
        ;
        if (curLine.length() + " >>".length() + 1 > wrapColumn)
        {
            var.append("\n" + NSpaces("vars ==".length()));
        }
        ;
        var.append(" >>");
        tlacode.addElement(var.toString());
        tlacode.addElement("");
    }

    /***********************************************************************
    * Generate a VARIABLE(S) declarations.  The argument is a vector of    *
    * strings that are the variables to be declared.  It does nothing if   *
    * the vector has length 0.                                             *
    *                                                                      *
    * Method added by LL on 25 Jan 2006.                                   *
    ***********************************************************************/
    public void GenVarDecl(Vector varVec)
    {
        StringBuffer res = new StringBuffer();
        StringBuffer curLine = new StringBuffer("VARIABLES ");
        // for measuring length
        if (varVec.size() == 0)
        {
            return;
        }
        ;
        if (varVec.size() > 1)
        {
            res.append("VARIABLES ");
        } else
        {
            res.append("VARIABLE ");
        }
        ;
        for (int i = 0; i < varVec.size(); i++)
        {
            if (i > 0)
            {
                res.append(", ");
                curLine.append(", ");
            }
            ;
            String vbl = (String) varVec.elementAt(i);
            if (curLine.length() + vbl.length() + 1 > wrapColumn)
            {
                curLine = new StringBuffer("VARIABLES ");
                res.append("\n");
                if (varVec.size() > 1)
                {
                    res.append(NSpaces("VARIABLES ".length()));
                } else
                {
                    res.append(NSpaces("VARIABLE ".length()));
                }
                ;
            }
            ;
            res.append(vbl);
            curLine.append(vbl);
        }
        ;
        tlacode.addElement(res.toString());
    }

    /**************************************/
    /* Generate the ProcSet == statement. */
    /**************************************/
    public void GenProcSet()
    {
        StringBuffer ps = new StringBuffer();
        if (st.processes == null || st.processes.size() == 0)
            return;
        ps.append("ProcSet == ");
        for (int i = 0; i < st.processes.size(); i++)
        {
            PcalSymTab.ProcessEntry proc = (PcalSymTab.ProcessEntry) st.processes.elementAt(i);
            Vector sv = proc.id.toStringVector();
            if (i > 0)
                ps.append(" \\cup ");
            if (proc.isEq)
                ps.append("{");
            else
                ps.append("(");
            int col = ps.length();
            ps.append((String) sv.elementAt(0));
            for (int v = 1; v < sv.size(); v++)
            {
                tlacode.addElement(ps.toString());
                ps = new StringBuffer(NSpaces(col));
                ps.append((String) sv.elementAt(v));
            }
            if (proc.isEq)
                ps.append("}");
            else
                ps.append(")");
        }
        tlacode.addElement(ps.toString());
        tlacode.addElement("");
    }

    /***********************************/
    /* Generate the Init == statement. */
    /**
     **********************************/
    private void GenInit(Vector globals, Vector procs, Vector processes) throws PcalTLAGenException
    {
        int col = "Init == ".length();
        StringBuffer is = new StringBuffer();
        is.append("Init == ");
        /* Global variables */
        if (globals != null && globals.size() > 0)
        {
            is.append("(* Global variables *)");
            tlacode.addElement(is.toString());
            is = new StringBuffer(NSpaces(col));
            for (int i = 0; i < globals.size(); i++)
            {
                AST.VarDecl decl = (AST.VarDecl) globals.elementAt(i);
                is.append("/\\ ");
                is.append(decl.var);
                if (decl.isEq)
                    is.append(" = ");
                else
                    is.append(" \\in ");
                int col2 = is.length();
                Vector sv = Parenthesize(decl.val.toStringVector());
                /*********************************************************
                * Call to Parenthesize added by LL on 27 Feb 2008.       *
                * See bug_08-02-18.                                      *
                *********************************************************/
                is.append((String) sv.elementAt(0));
                for (int v = 1; v < sv.size(); v++)
                {
                    tlacode.addElement(is.toString());
                    is = new StringBuffer(NSpaces(col2));
                    is.append((String) sv.elementAt(v));
                }
                tlacode.addElement(is.toString());
                is = new StringBuffer(NSpaces(col));
            }
        }
        if (procs != null && procs.size() > 0)
        {
            /* Procedure variables and parameters */
            for (int i = 0; i < procs.size(); i++)
            {
                AST.Procedure proc = (AST.Procedure) procs.elementAt(i);
                if (proc.params.size() == 0 && proc.decls.size() == 0)
                    // No parameters or procedure variables in this procedure
                    continue;
                is.append("(* Procedure ");
                is.append(proc.name);
                is.append(" *)");
                tlacode.addElement(is.toString());
                is = new StringBuffer(NSpaces(col));
                for (int p = 0; p < proc.params.size(); p++)
                {
                    AST.PVarDecl decl = (AST.PVarDecl) proc.params.elementAt(p);
                    is.append("/\\ ");
                    is.append(decl.var);

                    /*******************************************************
                    * Modified on 31 Jan 2006 by LL to add subscripts to   *
                    * initialization expression if needed.  Also replaced  *
                    * test for "\\in" with assertion that it can't occur,  *
                    * since it's forbidden by the grammar.                 *
                    *******************************************************/
                    PcalDebug.Assert(decl.isEq);
                    is.append(" = ");
                    Vector sv;
                    if (mp)
                    {
                        sv = AddSubscriptsToExpr(decl.val, SubExpr(Self("procedure")), new Changed(new Vector()))
                                .toStringVector();
                    } else
                    {
                        sv = Parenthesize(decl.val.toStringVector());
                        /*************************************************
                        * Call to Parenthesize added by LL on 27 Feb 2008. *
                        * See bug_08-02-18.                              *
                        *************************************************/
                    }
                    ;
                    if (mp)
                    {
                        is.append("[ self \\in ProcSet |-> ");
                    }
                    int col2 = is.length();
                    is.append((String) sv.elementAt(0));
                    for (int v = 1; v < sv.size(); v++)
                    {
                        tlacode.addElement(is.toString());
                        is = new StringBuffer(NSpaces(col2));
                        is.append((String) sv.elementAt(v));
                    }
                    if (mp)
                        is.append("]");
                    tlacode.addElement(is.toString());
                    is = new StringBuffer(NSpaces(col));
                }
                for (int p = 0; p < proc.decls.size(); p++)
                {
                    AST.PVarDecl decl = (AST.PVarDecl) proc.decls.elementAt(p);
                    is.append("/\\ ");
                    is.append(decl.var);

                    /*******************************************************
                    * Modified on 31 Jan 2006 by LL to add subscripts to   *
                    * initialization expression if needed.  Also replaced  *
                    * test for "\\in" with assertion that it can't occur,  *
                    * since it's forbidden by the grammar.                 *
                    *******************************************************/
                    PcalDebug.Assert(decl.isEq);
                    is.append(" = ");
                    Vector sv;
                    if (mp)
                    {
                        sv = AddSubscriptsToExpr(decl.val, SubExpr(Self("procedure")), new Changed(new Vector()))
                                .toStringVector();
                    } else
                    {
                        sv = Parenthesize(decl.val.toStringVector());
                        /*************************************************
                        * Call to Parenthesize added by LL on            *
                        * 27 Feb 2008.  See bug_08-02-18.                *
                        *************************************************/
                    }
                    ;
                    if (mp)
                    {
                        is.append("[ self \\in ProcSet |-> ");
                    }
                    int col2 = is.length();
                    is.append((String) sv.elementAt(0));
                    for (int v = 1; v < sv.size(); v++)
                    {
                        tlacode.addElement(is.toString());
                        is = new StringBuffer(NSpaces(col2));
                        is.append((String) sv.elementAt(v));
                    }
                    if (mp)
                        is.append("]");
                    tlacode.addElement(is.toString());
                    is = new StringBuffer(NSpaces(col));
                }
            }
        }
        if (processes != null && processes.size() > 0)
        {
            /* Process variables */
            for (int i = 0; i < processes.size(); i++)
            {
                AST.Process proc = (AST.Process) processes.elementAt(i);
                if (proc.decls.size() == 0) // No variables in this procedure
                    continue;
                is.append("(* Process ");
                is.append(proc.name);
                is.append(" *)");
                tlacode.addElement(is.toString());
                is = new StringBuffer(NSpaces(col));
                for (int p = 0; p < proc.decls.size(); p++)
                {
                    AST.VarDecl decl = (AST.VarDecl) proc.decls.elementAt(p);
                    is.append("/\\ ");
                    is.append(decl.var);
                    if (decl.isEq)
                        is.append(" = ");
                    else
                        is.append(" \\in ");
                    /*******************************************************
                    * Modified on 31 Jan 2006 by LL to add subscripts to   *
                    * initialization expression for process set.  Note     *
                    * tricky subscript that is added in expr for           *
                    * declaration of form "v \in expr".                    *
                    *                                                      *
                    * Also modified the whole method of producing the      *
                    * variable declaration because the original destroyed  *
                    * the formatting of the expression proc.id, leading    *
                    * to bad or incorrect formatting if the process id     *
                    * set expression was not trivial.                      *
                    *******************************************************/
                    Vector sv;
                    TLAExpr sve;
                    if (proc.isEq)
                    {
                        /***************************************************
                        * No substitution unless it's a process set.       *
                        ***************************************************/
                        sve = decl.val; // .toStringVector();
                    } else
                    {
                        if (decl.isEq)
                        {
                            /***********************************************
                            * For declaration "v = ...", add subscript     *
                            * "[self]".                                    *
                            ***********************************************/
                            sve = AddSubscriptsToExpr(decl.val, SubExpr(Self("procedure")), new Changed(new Vector()));
                        } else
                        {
                            /***********************************************
                            * For declaration "v \in ...", add subscript   *
                            * "[CHOOSE self \in Process Id Set : TRUE]".   *
                            ***********************************************/
                            TLAExpr subexpr = proc.id.cloneAndNormalize();

                            TLAExpr expr = new TLAExpr();
                            expr.addLine();
                            expr.addToken(new TLAToken("[", 0, TLAToken.BUILTIN));
                            expr.addToken(new TLAToken("CHOOSE", 1, TLAToken.BUILTIN));
                            expr.addToken(new TLAToken("self", 8, TLAToken.IDENT));
                            expr.addToken(new TLAToken("\\in ", 13, TLAToken.BUILTIN));
                            expr.normalize();

                            try
                            {
                                subexpr.prepend(expr, 1);
                                expr = new TLAExpr();
                                expr.addLine();
                                expr.addToken(new TLAToken(":", 0, TLAToken.BUILTIN));
                                expr.addToken(new TLAToken("TRUE", 2, TLAToken.BUILTIN));
                                expr.addToken(new TLAToken("]", 6, TLAToken.BUILTIN));
                                expr.prepend(subexpr, 1);
                            } catch (TLAExprException e)
                            {
                                throw new PcalTLAGenException(e.getMessage());
                            }

                            sve = AddSubscriptsToExpr(decl.val, expr, new Changed(new Vector()));
                        }
                        ;
                    }
                    ;
                    TLAExpr expr = new TLAExpr();
                    expr.addLine();
                    if (!proc.isEq)
                    {
                        expr.addToken(new TLAToken("[", 0, TLAToken.BUILTIN));
                        if (decl.isEq)
                        {
                            expr.addToken(new TLAToken("self", 1, TLAToken.IDENT));
                            expr.addToken(new TLAToken("\\in ", 6, TLAToken.BUILTIN));
                        }
                        ;
                        expr.normalize();
                        TLAExpr expr2 = proc.id.cloneAndNormalize();
                        try
                        {
                            expr2.prepend(expr, 0);
                            expr = new TLAExpr();
                            expr.addLine();
                            if (decl.isEq)
                            {
                                expr.addToken(new TLAToken("|->", 0, TLAToken.BUILTIN));
                            } else
                            {
                                expr.addToken(new TLAToken("->", 0, TLAToken.BUILTIN));
                            }
                            ;
                            expr.prepend(expr2, 1);
                            sve.prepend(expr, 1);
                        } catch (TLAExprException e)
                        {
                            throw new PcalTLAGenException(e.getMessage());
                        }
                    }
                    ;
                    sv = sve.toStringVector();
                    if (proc.isEq)
                    {
                        sv = Parenthesize(sv);
                    }
                    ;
                    /*****************************************************
                    * Call to Parenthesize added by LL on 27 Feb 2008.   *
                    * See bug_08-02-18.                                  *
                    *****************************************************/
                    int col2 = is.length();
                    is.append((String) sv.elementAt(0));
                    for (int v = 1; v < sv.size(); v++)
                    {
                        tlacode.addElement(is.toString());
                        is = new StringBuffer(NSpaces(col2));
                        is.append((String) sv.elementAt(v));
                    }
                    if (!proc.isEq)
                        is.append("]");
                    tlacode.addElement(is.toString());
                    is = new StringBuffer(NSpaces(col));
                } // end of for p loop.
            }
        }
        /* stack initial value */
        if (procs != null && procs.size() > 0)
        {
            if (mp)
                is.append("/\\ stack = [self \\in ProcSet |-> << >>]");
            else
                is.append("/\\ stack = << >>");
            tlacode.addElement(is.toString());
            is = new StringBuffer(NSpaces(col));
        }
        /* pc initial value */
        if (mp)
        {
            is.append("/\\ pc = [self \\in ProcSet |-> CASE ");
            int colPC = is.length();
            if (boxUnderCASE)
                colPC = colPC - 3;
            for (int p = 0; p < st.processes.size(); p++)
            {
                PcalSymTab.ProcessEntry pe = (PcalSymTab.ProcessEntry) st.processes.elementAt(p);
                is.append("self ");
                if (pe.isEq)
                {
                    is.append("= ");
                    int colExpr = is.length();
                    Vector sv = pe.id.toStringVector();
                    is.append((String) sv.elementAt(0));
                    for (int v = 1; v < sv.size(); v++)
                    {
                        tlacode.addElement(is.toString());
                        is = new StringBuffer(NSpaces(colExpr));
                        is.append((String) sv.elementAt(v));
                    }
                } else
                {
                    is.append("\\in ");
                    int colExpr = is.length();
                    Vector sv = pe.id.toStringVector();
                    is.append((String) sv.elementAt(0));
                    for (int v = 1; v < sv.size(); v++)
                    {
                        tlacode.addElement(is.toString());
                        is = new StringBuffer(NSpaces(colExpr));
                        is.append((String) sv.elementAt(v));
                    }
                }
                is.append(" -> \"");
                is.append(pe.iPC);
                if (p == st.processes.size() - 1)
                    is.append("\"]");
                else if (!boxUnderCASE)
                    is.append("\" []");
                else
                    is.append("\"");
                tlacode.addElement(is.toString());
                is = new StringBuffer(NSpaces(colPC));
                if (boxUnderCASE && p < st.processes.size() - 1)
                    is.append("[] ");
            }
        } else
        {
            is.append("/\\ pc = \"" + st.iPC + "\"");
            tlacode.addElement(is.toString());
        }
        tlacode.addElement("");
    }

    /************************************/
    /* Generate the Next == definition. */
    /************************************/
    private void GenNext()
    {
        Vector nextS = new Vector();
        StringBuffer sb = new StringBuffer();
        int max, col;

        // Steps with no parameter
        max = wrapColumn - ("Next == \\/ ".length());
        for (int i = 0; i < nextStep.size(); i++)
        {
            String a = (String) nextStep.elementAt(i);
            if (a.length() + " \\/ ".length() + sb.length() > max)
            {
                nextS.addElement(sb.toString());
                sb = new StringBuffer();
            }
            if (sb.length() > 0)
                sb.append(" \\/ ");
            sb.append(a);
        }
        if (sb.length() > 0)
            nextS.addElement(sb.toString());

        // Steps with (self) from ProcSet
        // These are procedures in a multiprocess algorithm
        Vector nextSS = new Vector();
        String nextSSstart = "(\\E self \\in ProcSet: ";
        sb = new StringBuffer();
        max = wrapColumn - ("Next == \\/ (\\E self \\in ProcSet: \\/ ".length());
        if (mp && st.procs.size() > 0)
        {
            for (int i = 0; i < st.procs.size(); i++)
            {
                PcalSymTab.ProcedureEntry p = (PcalSymTab.ProcedureEntry) st.procs.elementAt(i);
                if ((p.name.length() + "(self) \\/ ".length() + sb.length()) > max)
                {
                    nextSS.addElement(sb.toString());
                    sb = new StringBuffer();
                }
                if (sb.length() > 0)
                    sb.append(" \\/ ");
                sb.append(p.name);
                sb.append("(self)");
            }
            if (sb.length() > 0)
                nextSS.addElement(sb.toString() + ")");
        }

        // Steps with (self) from a set
        // These are process sets
        Vector nextSSP = new Vector(); // of Vector
        if (mp && st.processes.size() > 0)
            for (int i = 0; i < st.processes.size(); i++)
            {
                PcalSymTab.ProcessEntry p = (PcalSymTab.ProcessEntry) st.processes.elementAt(i);
                if (p.isEq)
                    continue;
                Vector vec = new Vector();
                sb = new StringBuffer();
                sb.append("(\\E self \\in ");
                Vector sv = p.id.toStringVector();
                col = sb.length();
                sb.append((String) sv.elementAt(0));
                for (int j = 1; j < sv.size(); j++)
                {
                    vec.addElement(sb.toString());
                    sb = new StringBuffer(NSpaces(col));
                    sb.append((String) sv.elementAt(j));
                }
                sb.append(": ");
                sb.append(p.name);
                sb.append("(self))");
                vec.addElement(sb.toString());
                nextSSP.addElement(vec);
            }

        // assemble the line from the pieces
        sb = new StringBuffer("Next == ");
        col = sb.length() + 2;
        for (int i = 0; i < nextS.size(); i++)
        {
            sb.append((String) nextS.elementAt(i));
            tlacode.addElement(sb.toString());
            sb = new StringBuffer(NSpaces(col) + " \\/ ");
        }
        if (nextSS.size() > 0)
        {
            sb.append(nextSSstart);
            int col2 = sb.length();
            if (nextSS.size() > 1)
                sb.append(" \\/ ");
            for (int i = 0; i < nextSS.size(); i++)
            {
                sb.append((String) nextSS.elementAt(i));
                tlacode.addElement(sb.toString());
                sb = new StringBuffer(NSpaces(col2) + " \\/ ");
            }
            sb = new StringBuffer(NSpaces(col) + " \\/ ");
        }
        if (nextSSP.size() > 0)
            for (int i = 0; i < nextSSP.size(); i++)
            {
                Vector v = (Vector) nextSSP.elementAt(i);
                for (int j = 0; j < v.size(); j++)
                {
                    String line = (String) v.elementAt(j);
                    sb.append(line);
                    tlacode.addElement(sb.toString());
                    sb = new StringBuffer(NSpaces(col + 4));
                }
                sb = new StringBuffer(NSpaces(col) + " \\/ ");
            }
        sb.append("(* Disjunct to prevent deadlock on termination *)");
        tlacode.addElement(sb.toString());
        sb = new StringBuffer(NSpaces(col + 4));
        if (mp)
            /*****************************************************************
            * Bug fix by LL on 6 Sep 2007.  Added parentheses to change      *
            *                                                                *
            * (*)    \A self \in ProcSet: ... /\ UNCHANGED vars              *
            *                                                                *
            * to                                                             *
            *                                                                *
            * (**)   (\A self \in ProcSet: ...)  /\ UNCHANGED vars           *
            *                                                                *
            * thus moving the UNCHANGED vars outside the quantifier.         *
            * Since self does not appear in UNCHANGED vars, the two          *
            * expressions are equivalent except when ProcSet is the empty    *
            * set, in which case (*) equals TRUE and (**) equals             *
            * UNCHANGED vars.                                                *
            *****************************************************************/
            sb.append("((\\A self \\in ProcSet: pc[self] = \"Done\") /\\ " + "UNCHANGED vars)");
        else
            sb.append("(pc = \"Done\" /\\ UNCHANGED vars)");
        tlacode.addElement(sb.toString());
        tlacode.addElement("");
    }

    /****************************************/
    /* Generate the Spec == ... definition. */
    /****************************************/
    private void GenSpec()
    {
        StringBuffer sb = new StringBuffer("Spec == Init /\\ [][Next]_vars");
        // Generate the reqeusted fairness conjuncts
        if (PcalParams.FairnessOption.equals("wfNext") || (!mp && PcalParams.FairnessOption.equals("wf")))
        {
            // If uniprocess then wf is the same as wfNext
            sb.append(" /\\ WF_vars(Next)");
            tlacode.addElement(sb.toString());
        } else if (mp && (PcalParams.FairnessOption.equals("wf") || PcalParams.FairnessOption.equals("sf")))
        {
            // Fairness for each process
            String fairness = ((PcalParams.FairnessOption.equals("wf")) ? "WF" : "SF");
            Vector lines = new Vector(); // For procedures and processes
            Vector setLines = new Vector(); // For process sets
            // lines is a vector of strings
            // setLines is a vector of vectors of strings
            // Procedures
            for (int i = 0; i < st.procs.size(); i++)
            {
                PcalSymTab.ProcedureEntry p = (PcalSymTab.ProcedureEntry) st.procs.elementAt(i);
                StringBuffer sbl = new StringBuffer("\\A self \\in ProcSet: ");
                sbl.append(fairness);
                sbl.append("_vars(");
                sbl.append(p.name);
                sbl.append("(self))");
                lines.addElement(sbl.toString());
            }
            // Processes
            for (int i = 0; i < st.processes.size(); i++)
            {
                PcalSymTab.ProcessEntry p = (PcalSymTab.ProcessEntry) st.processes.elementAt(i);
                if (!p.isEq)
                    continue;
                StringBuffer sbl = new StringBuffer(fairness);
                sbl.append("_vars(");
                sbl.append(p.name);
                sbl.append(")");
                lines.addElement(sbl.toString());
            }
            // Process sets
            for (int i = 0; i < st.processes.size(); i++)
            {
                PcalSymTab.ProcessEntry p = (PcalSymTab.ProcessEntry) st.processes.elementAt(i);
                if (p.isEq)
                    continue;
                Vector v = new Vector();
                StringBuffer sbl = new StringBuffer("\\A self \\in ");
                Vector sv = p.id.toStringVector();
                int colV = sbl.length();
                sbl.append((String) sv.elementAt(0));
                for (int j = 1; j < sv.size(); j++)
                {
                    v.addElement(sbl.toString());
                    sbl = new StringBuffer(NSpaces(colV));
                    sbl.append((String) sv.elementAt(j));
                }
                sbl.append(": ");
                sbl.append(fairness);
                sbl.append("_vars(");
                sbl.append(p.name);
                sbl.append("(self))");
                v.addElement(sbl.toString());
                setLines.addElement(v);
            }
            // Put the generated code with proper indentation
            if (lines.size() + setLines.size() > 1)
                sb.append(" /\\");
            int col = sb.length();
            for (int i = 0; i < lines.size(); i++)
            {
                sb.append(" /\\ ");
                sb.append((String) lines.elementAt(i));
                tlacode.addElement(sb.toString());
                sb = new StringBuffer(NSpaces(col));
            }
            for (int i = 0; i < setLines.size(); i++)
            {
                sb.append(" /\\ ");
                int colV = sb.length();
                Vector v = (Vector) setLines.elementAt(i);
                for (int j = 0; j < v.size(); j++)
                {
                    sb.append((String) v.elementAt(j));
                    tlacode.addElement(sb.toString());
                    sb = new StringBuffer(NSpaces(colV));
                }
                sb = new StringBuffer(NSpaces(col));
            }
        } else
            tlacode.addElement(sb.toString());
        tlacode.addElement("");
    }

    /************************************/
    /* Generate the Termination ==      */
    /************************************/
    private void GenTermination()
    {
        StringBuffer sb = new StringBuffer();
        sb.append("Termination == <>(");
        if (mp)
            sb.append("\\A self \\in ProcSet: pc[self]");
        else
            sb.append("pc");
        sb.append(" = \"Done\")");
        tlacode.addElement(sb.toString());
        tlacode.addElement("");
    }

    /**********************************************************/
    /* For variables that need subscripts, add the subscript. */
    /* These are pc, stack, procedure variables, procedure    */
    /* parameters, and variables defined in process sets.     */
    /* Then, aded primes to variables that have been changed  */
    /* according to c.                                        */
    /**
     *********************************************************/
    private TLAExpr AddSubscriptsToExpr(TLAExpr exprn, TLAExpr sub, Changed c) throws PcalTLAGenException
    {

        Vector exprVec = new Vector(); // the substituting exprs
        Vector stringVec = new Vector(); // the substituted ids
        TLAExpr expr = exprn.cloneAndNormalize();

        for (int i = 0; i < expr.tokens.size(); i++)
        {
            Vector tv = (Vector) expr.tokens.elementAt(i);
            for (int j = 0; j < tv.size(); j++)
            {
                TLAToken tok = (TLAToken) tv.elementAt(j);
                boolean prime = ((tok.type == TLAToken.IDENT) && c.IsChanged(tok.string));
                boolean subr = (sub != null && (tok.type == TLAToken.ADDED || (mp && (tok.type == TLAToken.IDENT) && (IsProcedureVar(tok.string) || IsProcessSetVar(tok.string)))));
                if ((subr || prime) && !InVector(tok.string, stringVec))
                {
                    stringVec.addElement(tok.string);
                    TLAExpr exp = new TLAExpr();
                    exp.addLine();
                    exp.addToken(new TLAToken(tok.string, 0, TLAToken.IDENT));
                    if (prime)
                        /*****************************************************
                        * Modified by LL on 30 Aug 2007.  The following      *
                        * call to addTokenOffset was originally a call to    *
                        * addToken.  See the comments for                    *
                        * TLAExpr.addTokenOffset().                          *
                        *****************************************************/
                        exp.addTokenOffset(new TLAToken("'", 0, TLAToken.BUILTIN), 0);
                    if (subr)
                    {
                        TLAExpr subexp = sub.cloneAndNormalize();
                        exp.normalize();
                        try
                        {
                            subexp.prepend(exp, 0);
                        } catch (TLAExprException e)
                        {
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
                    exprVec.addElement(exp);
                }
            }
        }
        if (exprVec.size() > 0)
            try
            {
                expr.substituteForAll(exprVec, stringVec, false);
            } catch (TLAExprException e)
            {
                throw new PcalTLAGenException(e.getMessage());
            }
        return expr;
    }

    /**************************************************/
    /* Given a string, make it into a subscript expr. */
    /* If string is null, then returns null.          */
    /**************************************************/
    private static TLAExpr SubExpr(String sub)
    {
        TLAExpr expr = new TLAExpr();
        if (sub != null)
        {
            expr.addLine();
            expr.addToken(new TLAToken("[", 0, TLAToken.BUILTIN));
            /***************************************************************
            * Change made by LL 30 Aug 2007.  The following two calls to   *
            * addTokenOffset were originally calls to addToken.            *
            ***************************************************************/
            expr.addTokenOffset(new TLAToken(sub, 0, TLAToken.IDENT), 0);
            expr.addTokenOffset(new TLAToken("]", 0, TLAToken.BUILTIN), 0);
            /***************************************************************
            * Comment added by LL: The following call of MakeExprPretty    *
            * is harmless because SubExpr is called only with argument     *
            * Self(context), so it is a no-op.                             *
            ***************************************************************/
            MakeExprPretty(expr);
            expr.normalize();
            return expr;
        } else
            return null;
    }

    /*********************************************************/
    /* Gives the string to use when subscripting a variable. */
    /*********************************************************/
    // LL comment: This makes no sense to me, since why should one use
    // a null subscript for a variable in the context of a process?
    // What the ... is going on here?
    private String Self(String context)
    {
        String s = null;
        if (mp)
        {
            if (context.equals("procedure"))
                s = "self";
            else
                s = self;
        }
        return s;
    }

    /***********************************************************************
    * Comment added by LL: MakeExprPretty should never be called on an     *
    * expression any part of which was an expression in the input.         *
    * Fortunately, it is now called only for the expression "[self]", so   *
    * it is effectively a no-op.                                           *
    ***********************************************************************/
    public static void MakeExprPretty(TLAExpr expr)
    {
        /*********************************************************************
         * Sets columns so this expr looks nice and tight.                   *
         *********************************************************************/
        Vector line; /* Vector of TLAToken */
        boolean spread;
        int nextCol = 1;
        for (int i = 0; i < expr.tokens.size(); i++)
        {
            line = (Vector) expr.tokens.elementAt(i);
            for (int j = 0; j < line.size(); j++)
            {
                TLAToken tok = ((TLAToken) line.elementAt(j));
                spread = tok.string.equals("=");
                tok.column = nextCol + ((spread) ? 1 : 0);
                nextCol = nextCol + tok.getWidth() + ((spread) ? 2 : 0);
            }
        }
    }

    /***********************************************************/
    /* v is a sequence of SingleAssign. Return a vector of the */
    /* same SingleAssign, but sorted in terms of the lhs.var.  */
    /***********************************************************/
    private static Vector SortSass(Vector vec)
    {
        Vector v = (Vector) vec.clone();
        Vector r = new Vector(); // The sorted version of v.
        while (v.size() > 0)
        { // Good old n^2 insertion sort.
            AST.SingleAssign candidate = (AST.SingleAssign) v.elementAt(0);
            int indexC = 0;
            for (int i = 1; i < v.size(); i++)
            {
                AST.SingleAssign sass = (AST.SingleAssign) v.elementAt(i);
                if (candidate.lhs.var.compareTo(sass.lhs.var) > 0)
                {
                    indexC = i;
                    candidate = sass;
                }
            }
            r.addElement(candidate);
            v.remove(indexC);
        }
        return r;
    }

    /***********************************************************************
    * If vec is a StringVector representing an expression, then this       *
    * returns the StringVector obtained by parenthesizing the expression   *
    * if it may need parenthesizing.  This is used only to prevent         *
    * parsing errors when the expression appears immediately to the right  *
    * of an "=" in the spec.  This is a rare situation, so it would be     *
    * nice to add the parentheses are really needed.  For now, the         *
    * parentheses are added if one of the following tokens occur outside   *
    * parentheses and not inside a string:                                 *
    *                                                                      *
    *   =                                                                  *
    *   #                                                                  *
    *   <  not followed by <                                               *
    *   >  not followed by > or preceded by =                              *
    *   |  preceded or followed by -                                       *
    *   \  not followed by "o" or "X".                                     *
    *   /  followed by "\"                                                 *
    *                                                                      *
    * Left parentheses are                                                 *
    *                                                                      *
    *   (  [  {  <<                                                        *
    *                                                                      *
    * The handling of "\" is a simplifying hack.  Lots of operators        *
    * beginning with "\" like "\/", "\gg" and "\subseteq" have precedence  *
    * greater than or equal to "=".  The only commonly used ones with      *
    * precedence lower than "=" seem to be "\o" and "\X".  It doesn't      *
    * seem to be worth the bother of checking for the others just to       *
    * avoid unnecessarily adding the parentheses when those other rare     *
    * operators are used.                                                  *
    *                                                                      *
    * Perhaps the one improvement that might be worth making in this       *
    * procedure is to have it not add parentheses because of "dangerous"   *
    * operations in an IF clause--for example:                             *
    *                                                                      *
    *      IF x < 0 THEN ...                                               *
    *                                                                      *
    * This would require considering "IF" to be a left parenthesis and     *
    * "THEN" to be a right parenthesis.  However, that's not trivial to    *
    * implement because of unlikely things like                            *
    *                                                                      *
    *     IFx := 42 ;                                                      *
    *     x := IFx < THENx                                                 *
    ***********************************************************************/
    private static Vector Parenthesize(Vector vec)
    {

        if (vec.size() == 0)
        {
            return vec;
        }
        ;
        /*******************************************************************
        * vec shouldn't be empty, but let's not worry about what to do if  *
        * it is.                                                           *
        *******************************************************************/
        int curCharNum = 0;
        int curLineNum = 0;
        int parenDepth = 0;
        boolean inString = false;
        boolean needParen = false;
        while ((curLineNum < vec.size()) && (!needParen))
        {
            String curLine = (String) vec.elementAt(0);
            while ((curCharNum < curLine.length()) && (!needParen))
            {
                char curChar = curLine.charAt(curCharNum);

                if (inString)
                {
                    switch (curChar) {
                    case '\"':
                        inString = false;
                        break;
                    case '\\':
                        curCharNum++;
                        break;
                    }
                    ; // end switch
                } // end if (inString)
                else
                {
                    boolean leftParen = false;
                    boolean rightParen = false;
                    boolean mayNeedParen = false;
                    /***************************************************************
                    * Set nextChar to the next character on the line, or ' ' if    *
                    * there is none.                                               *
                    ***************************************************************/
                    char nextChar = ' ';
                    if (curCharNum < curLine.length() - 1)
                    {
                        nextChar = curLine.charAt(curCharNum + 1);
                    }
                    switch (curChar) {
                    case '\"':
                        inString = true;
                        break;
                    case '=':
                        mayNeedParen = true;
                        break;
                    case '#':
                        mayNeedParen = true;
                        break;
                    case '<':
                        if (nextChar == '<')
                        {
                            curCharNum++;
                            leftParen = true;
                        } else
                        {
                            mayNeedParen = true;
                        }
                        ;
                        break;
                    case '>':
                        if (nextChar == '>')
                        {
                            curCharNum++;
                            rightParen = true;
                        } else
                        {
                            mayNeedParen = true;
                        }
                        ;
                        break;
                    case '|':
                        if ((nextChar == '-') || ((curCharNum > 0) && (curLine.charAt(curCharNum - 1) == '-')))
                        {
                            mayNeedParen = true;
                        }
                        ;
                        break;
                    case '\\':
                        if (!((nextChar == ' ') || (nextChar == 'o') || (nextChar == 'X')))
                        {
                            mayNeedParen = true;
                        }
                        ;
                        break;
                    case '/':
                        if (nextChar == '\\')
                        {
                            mayNeedParen = true;
                        }
                        ;
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
                    ;
                    if (mayNeedParen && (parenDepth == 0))
                    {
                        needParen = true;
                    }
                    ;
                    if (leftParen)
                    {
                        parenDepth++;
                    }
                    ;
                    if (rightParen)
                    {
                        if (parenDepth == 0)
                        {
                            needParen = true;
                        }
                        ;
                        parenDepth--;
                    }
                }
                ; // end else ! inString
                curCharNum++;
            }
            ; // end while (curCharNum < curLine.length())

            if (inString)
            {
                needParen = true;
            }
            ;
            /*****************************************************************
            * If there is an unmatched quote, we might as well stop here.    *
            *****************************************************************/
            curLineNum++;
            curCharNum = 0;
        } // end while (curLineNum < vec.size())

        /*********************************************************************
        * Add the parentheses if necessary.                                  *
        *********************************************************************/
        if (needParen)
        {
            vec.setElementAt("(" + ((String) vec.elementAt(0)), 0);
            for (int i = 1; i < vec.size(); i++)
            {
                vec.setElementAt(" " + ((String) vec.elementAt(i)), i);
            }
            ;
            curLineNum = vec.size() - 1;
            vec.setElementAt(((String) vec.elementAt(curLineNum)) + ")", curLineNum);
        }
        ;
        return vec;
    }
}
