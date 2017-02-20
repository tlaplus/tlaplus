package pcal;

import java.util.Vector;

import pcal.AST.VarDecl;
import pcal.exception.PcalTLAGenException;
import pcal.exception.TLAExprException;
import tla2tex.Debug;

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
    /** The tlacode field accumulates the translation as it is constructed.  It 
     * should be a vector of separate lines.  Keiths original implementation put
     * multiple lines in a single element of tlacode in:
     *   
     *   GenVarsAndDefs
     *   GenVarDecl
     */
    private Vector tlacode = new Vector(); /* of lines */
    
    /**
     * The tlacodeNextLine field accumulates characters for the next
     * line of tlacode.  It is always a string.  It is assumed that
     * when it equals "", then a new line can be started without
     * adding the current string in tlacodeNextLine as a new line.
     */
    private String tlacodeNextLine = "" ;
    
    /**
     * mappingVector is a local pointer to {@link TLAtoPCalMapping#mappingVector},
     * which is used to accumulate the TLA+ to PlusCal mapping.  It approximately
     * reflects the TLA+ that has been inserted in the {@link PcalTLAGen#tlacode}  
     * vector.  It is set in the {@link TLAtoPCalMapping#generate} method.
     */
    private Vector mappingVector;
    
    /**
     * mappingVectorNextLine contains the sequence of MappingObject objects
     * that correspond to the strings added to tlacodeNextLine.
     */
    private Vector mappingVectorNextLine = new Vector() ;
    
    /**
     * The self field is set to "self" by GenProcess when called for a single process
     * (rather than a process set) and by GenProcedure for a multiprocess algorithm. 
     * It is set to the process id by GenProcess when called for a single process.
     * selfIsSelf is set to true when self is set to "self", and to false when self is
     * set to a process id.  The self field never seems to be reset to null.
     */
    private TLAExpr self = null; // changed by LL on 22 jan 2011 from: private String self = null; /* for current process */
    private boolean selfIsSelf = false; 
    
    private Vector vars = new Vector(); /* list of all disambiguated vars */
    private Vector pcV = new Vector(); /* sublist of vars of variables representing 
                                          procedure parameters and procedure variables */
    private Vector psV = new Vector(); /* sublist of vars local to a process set */
    private PcalSymTab st = null; /* symbol table */
    private boolean mp = false; /* true if multiprocess, else unip */
    private Vector nextStep = new Vector(); /* unparam actions */ // For multiprocess alg, these are the individual (=) processes
    private Vector nextStepSelf = new Vector(); /* param actions */ // These are process sets (\in processes) and procedures
    // Following added to keep track of the length of the "lbl... == /\ "
    // that precedes all the statements in the definition of a label's action
    // because Keith screwed up and handled the assignment to the pc different 
    // from that of all other variables, forgetting that the subscript exp
    // in pc[exp] := ... can be multi-line.
    private int kludgeToFixPCHandlingBug ;
    /**
     * The public method: generate TLA+ as a vector of strings. 
     * @param ast the AST of the PCal
     * @param symtab the symbol table
     * @return the vector of strings with TLA+ code
     * @throws PcalTLAGenException on any unrecoverable methods
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
    private String currentProcName ;
    
    /**
     * Generates the translation.
     * 
     * @param ast  The AST produced by parsing and exploding.
     * @param symtab The symbol table.
     * @param report  A vector of strings, containing the reports of renaming.
     * @return A vector of strings.
     * @throws PcalTLAGenException
     */
    public Vector generate(AST ast, PcalSymTab symtab, Vector report) throws PcalTLAGenException
    {
        TLAtoPCalMapping map = PcalParams.tlaPcalMapping;
        mappingVector = new Vector(50);
        /*
         * Add the reports of renaming to the output.
         */
        for (int i = 0; i < report.size(); i++) {
            addOneLineOfTLA((String) report.elementAt(i));
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
        PCalLocation ZeroLocation = new PCalLocation(0, 0);
        ((Vector) mappingVector.elementAt(0)).
             add(0, new MappingObject.LeftParen(ZeroLocation));
        Vector lastLine = (Vector) mappingVector.elementAt(mappingVector.size()-1);
        lastLine.add(lastLine.size(), new MappingObject.RightParen(ZeroLocation));

        /*
         * For testing, throw a null pointer exception if the parentheses are not
         * properly matching in mappingVector.
         */
        //int[] depths = new int[10000];
        
        int parenDepth = 0;
        for (int i = 0; i < mappingVector.size(); i++) {
            Vector line = (Vector) mappingVector.elementAt(i);
            for (int j = 0; j < line.size(); j++) {
                MappingObject obj = (MappingObject) line.elementAt(j);
                if (obj.getType() == MappingObject.LEFT_PAREN) {
                    parenDepth++;
                }
                else if (obj.getType() == MappingObject.RIGHT_PAREN) {
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
        Vector nonredundantMappingVector = 
            TLAtoPCalMapping.RemoveRedundantParens(mappingVector);
        map.makeMapping(nonredundantMappingVector);
        
//System.out.println("Original mappingvector:");
//MappingObject.printMappingVector(mappingVector);    
//System.out.println("RemoveRedundantParens(mappingVector)");
//MappingObject.printMappingVector(TLAtoPCalMapping.RemoveRedundantParens(mappingVector));
//System.out.println("Should be original mappingvector:");
//MappingObject.printMappingVector(mappingVector); 
// Debugging
//for (int i = 0; i < tlacode.size(); i++) {
//System.out.println("\nline " + i);
//System.out.println((String) tlacode.elementAt(i)) ;
//}
//MappingObject.printMappingVector(mappingVector);

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
        currentProcName = "Next";
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

    private void GenProcedure(AST.Procedure ast, String context) throws PcalTLAGenException {
        /*
         * First, generate the body's actions.  Must set self and selfIsSelf (?) for
         * use by GenLabeledStmt.
         */
        if (mp) {
      
            self = selfAsExpr(); // subscript for variables is "self"
            selfIsSelf = true;
//            /* Add this step to the disjunct of steps with (self) */
            nextStepSelf.addElement(ast.name + "(self)");
        } else
        {
            /* Add this step to the disjunct of steps */
            nextStep.addElement(ast.name);
        }
        for (int i = 0; i < ast.body.size(); i++) {
            AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.elementAt(i);
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
        String argument = (mp) ? "(self)" : "";
        StringBuffer buf = new StringBuffer(ast.name + argument + " == ");
        addOneTokenToTLA(buf.toString());
        String indentSpaces = NSpaces(buf.length() + 2);        
        for (int i = 0; i < ast.body.size(); i++) {
            AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.elementAt(i);
            String disjunct = stmt.label + argument;
            if (   i != 0 
                && tlacodeNextLine.length() +  7 /* the 7 was obtained empirically */
                    + disjunct.length() > wrapColumn) {
                endCurrentLineOfTLA();
            }
            if (i != 0) {
               addOneTokenToTLA(((tlacodeNextLine.length() == 0)? indentSpaces : "") + " \\/ "); 
            }
            addLeftParen(stmt.getOrigin());
            addOneTokenToTLA(disjunct);
            addRightParen(stmt.getOrigin());
        }
        addRightParen(ast.getOrigin());
        addOneLineOfTLA("");
        
// The previous version was very convoluted just to avoid having to go through the
// list of labeled statements twice.  It seemed easier to just reimplement from
// scratch.
//        /* ns and nsV accumulate the disjunct of the steps of the procedure, where
//         * ns contains the contents of the current line and nsV is the vector of
//         * already accumulated lines.
//         * 
//         */
//        StringBuffer ns = new StringBuffer();
//        Vector nsV = new Vector();
//        
//       int nsC = ast.name.length() + ((mp) ? "(self)".length() : 0) + " == ".length();
//        if (mp)
//        {
//            self = selfAsExpr(); // subscript for variables is "self"
//            selfIsSelf = true;
//            /* Add this step to the disjunct of steps with (self) */
//            nextStepSelf.addElement(ast.name + "(self)");
//        } else
//        {
//            /* Add this step to the disjunct of steps */
//            nextStep.addElement(ast.name);
//        }
//        for (int i = 0; i < ast.body.size(); i++)
//        {
//            AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.elementAt(i);
//            if ((ns.length() + stmt.label.length() + " \\/ ".length() + ((mp) ? "(self)".length() : 0)) > wrapColumn
//                    - nsC - " \\/ ".length())
//            {
//                nsV.addElement(ns.toString());
//                ns = new StringBuffer();
//            }
//            if (ns.length() > 0)
//                ns.append(" \\/ ");
//            ns.append(stmt.label);
//            if (mp)
//                ns.append("(self)");
//            GenLabeledStmt(stmt, "procedure");
//        }
//        nsV.addElement(ns.toString());
//        // Generate definition of procedure steps
//        ns = new StringBuffer();
//        ns.append(ast.name);
//        if (mp)
//            ns.append("(self)");
//        ns.append(" == ");
//        ns.append((String) nsV.elementAt(0));
//        tlacode.addElement(ns.toString());
//        for (int i = 1; i < nsV.size(); i++)
//        {
//            ns = new StringBuffer(NSpaces(nsC + 2));
//            ns.append(" \\/ ");
//            ns.append((String) nsV.elementAt(i));
//            tlacode.addElement(ns.toString());
//        }
//        tlacode.addElement("");
    }

    private void GenProcess(AST.Process ast, String context) throws PcalTLAGenException
    {
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
        if (ast.isEq)
        {
            self = ast.id ;
            selfIsSelf = false;
            isSet = false;
        } else {
            self = selfAsExpr();
            selfIsSelf = true;
        }

        if (isSet)
        {
            nextStepSelf.addElement(ast.name + "(self)");
        } else
            nextStep.addElement(ast.name);
        
        for (int i = 0; i < ast.body.size(); i++) {
            AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.elementAt(i);
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

      if (! ParseAlgorithm.omitPC) {
        addLeftParen(ast.getOrigin());
        String argument = (isSet) ? "(self)" : "";
        StringBuffer buf = new StringBuffer(ast.name + argument + " == ");
        addOneTokenToTLA(buf.toString());
        String indentSpaces = NSpaces(buf.length() + 2);        
        for (int i = 0; i < ast.body.size(); i++) {
            AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.elementAt(i);
            String disjunct = stmt.label + argument;
            if (   i != 0 
                && tlacodeNextLine.length() + 7 /* the 7 was obtained empirically */
                  + disjunct.length() > wrapColumn) {
                endCurrentLineOfTLA();
            }
            if (i != 0) {
               addOneTokenToTLA(((tlacodeNextLine.length() == 0)? indentSpaces : "") + " \\/ "); 
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
//        /* ns accumulates the disjunt of the steps of the process */
//        StringBuffer ns = new StringBuffer();
//        Vector nsV = new Vector();
//        boolean isSet = true;
//        /************************************************************/
//        /* Decide if it is a process set or not. If so, set self to */
//        /* the string "self"; otherwise set self to the process id. */
//        /************************************************************/
//        if (ast.isEq)
//        {
//            self = ast.id ;
//            selfIsSelf = false;
//            isSet = false;
//        } else {
//            self = selfAsExpr();
//            selfIsSelf = true;
//        }
//        
//        int nsC = ast.name.length() + ((isSet) ? "(self)".length() : 0) + " == ".length();
//        if (isSet)
//        {
//            nextStepSelf.addElement(ast.name + "(self)");
//        } else
//            nextStep.addElement(ast.name);
//        for (int i = 0; i < ast.body.size(); i++)
//        {
//            AST.LabeledStmt stmt = (AST.LabeledStmt) ast.body.elementAt(i);
//            if ((ns.length() + stmt.label.length() + " \\/ ".length() + ((isSet) ? "(self)".length() : 0)) > wrapColumn
//                    - nsC - " \\/ ".length())
//            {
//                nsV.addElement(ns.toString());
//                ns = new StringBuffer();
//            }
//            if (ns.length() > 0)
//                ns.append(" \\/ ");
//            ns.append(stmt.label);
//            if (isSet)
//                ns.append("(self)");
//            GenLabeledStmt(stmt, "process");
//        }
//        nsV.addElement(ns.toString());
//        // Generate definition of process steps
//        // This apparently defines the process name
//        // to equal the disjunction of all the individual
//        // label-named actions.  If we are omitting
//        // the pc, we have already defined the process name
//        // to equal the only label action, so we skip
//        // this.
//        if (! ParseAlgorithm.omitPC) {
//          ns = new StringBuffer();
//          ns.append(ast.name);
//          if (isSet)
//              ns.append("(self)");
//          ns.append(" == ");
//          ns.append((String) nsV.elementAt(0));
//          tlacode.addElement(ns.toString());
//          for (int i = 1; i < nsV.size(); i++)
//          {
//              ns = new StringBuffer(NSpaces(nsC + 2));
//              ns.append(" \\/ ");
//              ns.append((String) nsV.elementAt(i));
//              tlacode.addElement(ns.toString());
//          }
//        }
//        tlacode.addElement("");
    }

    /*****************************************************/
    /* Generates an action with name equal to the label. */
    /**
     ****************************************************/
    private void GenLabeledStmt(AST.LabeledStmt ast, String context) throws PcalTLAGenException
    {
        // Set actionName to the name of the action being defined.
        // This is the label, except when we are omitting the PC,
        // in which case it is "Next" for a uniprocess algorithm
        // and the process name for a multiprocess algorithm.
        String actionName = ast.label;
        if (ParseAlgorithm.omitPC) {
            actionName = currentProcName;
        }
        StringBuffer sb = new StringBuffer(actionName);
        /* c is used to determine which vars are in UNCHANGED. */
        Changed c = new Changed(vars);
        if (mp && (context.equals("procedure") || selfIsSelf)) { // self.equals("self")))
            sb.append("(self)");
        }   
        sb.append(" == ");
        int col = sb.length();
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
        // StringBuffer sb begin the next line added to tlacode.
        //
        /* if (ast.stmts.size() > 1) {  */
            sb.append("/\\ ");
            kludgeToFixPCHandlingBug = kludgeToFixPCHandlingBug + 3;
        /* } */
            
        // We set defStartLine to the index of the next line added to tlacode and
        // colAfterAnd to the column position in that line immediately following
        // the added "/\ ".  This gives us the information needed to remove the
        // "/\ " later from tlacode.
        int defStartLine = tlacode.size();
        int colAfterAnd = sb.length();
        
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
        for (int i = 0 ; i < ast.stmts.size(); i++) {
           AST stmt = (AST) ast.stmts.elementAt(i);
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
        for (int i = 0; i < ast.stmts.size(); i++)
        {
            GenStmt((AST) ast.stmts.elementAt(i), c, context, sb.toString(), sb.length());
            sb = new StringBuffer(NSpaces(col));
            sb.append("/\\ ");
        }
        
        /*
         * Since the UNCHANGED conjunct just consists of TLATokens, with no
         * SourceTokens, we can just use the old code, simply replacing each
         * tlacode.addElement call with a call of addOneLineOfTLA--except that
         * the last one is replaced with a call of addOneTokenToTLA so we can
         * put the RightParen object in mappingVector.
         */
        Vector unc = c.Unchanged(wrapColumn - col - "/\\ UNCHANGED << ".length());
        if (c.NumUnchanged() > 1)
        {
            sb = new StringBuffer(NSpaces(col));
            sb.append("/\\ UNCHANGED << ");
            int here = sb.length();
            sb.append((String) unc.elementAt(0));
            for (int i = 1; i < unc.size(); i++)
            {
//                tlacode.addElement(sb.toString());
                addOneLineOfTLA(sb.toString());
                sb = new StringBuffer(NSpaces(here));
                sb.append((String) unc.elementAt(i));
            }
            sb.append(" >>");
//            tlacode.addElement(sb.toString());
            addOneTokenToTLA(sb.toString());
        } else if (c.NumUnchanged() == 1) {
        	// Change made by LL on 16 Mar 2011 so that, if there is a single
        	// unchanged variable v, it produces v' = v if v is a short variable,
        	// otherwise it produces UNCHANGED v
        	if (c.Unchanged().length() > 5) {
//              tlacode.addElement(NSpaces(col) + "/\\ UNCHANGED " + c.Unchanged());
        	    addOneTokenToTLA(NSpaces(col) + "/\\ UNCHANGED " + c.Unchanged());
        	} else {
//        		tlacode.addElement(NSpaces(col) + "/\\ " + c.Unchanged() + "' = "
//        				+ c.Unchanged());
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
                  String line = (String) tlacode.elementAt(i);
                  if (i == defStartLine) {
                     // remove the "/\ " added                      
                     tlacode.setElementAt(line.substring(0, colAfterAnd-3) +
                                          line.substring(colAfterAnd, line.length()) , i);
                     shiftMappingVectorTokensLeft(i, colAfterAnd, 3);
                    
                  } else {
                     // Remove three blanks from any following lines.  We test the length 
                     // of the line just in case one or more short (hopefully blank) lines 
                     // have been added.
                      if (line.length() > 3) {
                          tlacode.setElementAt(line.substring(3, line.length()) , i);
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
//        tlacode.addElement("");
    }
    
    /**
     * Adjusts the objects in line lineNum of mappingVector so all column
     * numbers starting with startCol are decreased by `shift'.  If any Begin/EndTLAToken
     * pairs are changed to have a non-positive width, a bug is reported.
     * 
     * Note: It is assumed that there is no aliasing of MappingTokens in mappingVector.
     * That is, other than in transient local variables, the only pointer to a
     * MappingToken in mappingVector is the single one in its line of mappingVector.
     * I can't see how any aliasing of MappingTokens could arise.
     * 
     * This method is called only by GenLabeledStmts.
     * 
     * @param lineNum
     * @param startCol
     * @param shift
     */
    private void shiftMappingVectorTokensLeft(int lineNum, int startCol, int shift) {
        boolean lastWasBeginTLAToken = false;
        int lastBeginTLATokCol = -777; // to keep the compiler happy.
        Vector line = (Vector) mappingVector.elementAt(lineNum);
        for (int i = 0; i < line.size(); i++) {
            MappingObject obj = (MappingObject) line.elementAt(i);
            if (obj.getType() == MappingObject.BEGIN_TLATOKEN) {
               MappingObject.BeginTLAToken tobj = (MappingObject.BeginTLAToken) obj;
               int col = tobj.getColumn();
               if (col >= startCol) {
                   tobj.setColumn(col - shift);
               }
               lastWasBeginTLAToken = true;
               lastBeginTLATokCol = tobj.getColumn();
            }
            else {
                if (obj.getType() == MappingObject.END_TLATOKEN) {
                    MappingObject.EndTLAToken tobj = (MappingObject.EndTLAToken) obj;
                    int col = tobj.getColumn();
                    if (col >= startCol) {
                        tobj.setColumn(col - shift);
                    }
                    if (lastWasBeginTLAToken && tobj.getColumn() <= lastBeginTLATokCol) {
                        PcalDebug.ReportBug(
                         "PcalTLAGen.shiftMappingVectorTokensLeft created a null TLA Token");
                    }
                }
                else if (obj.getType() == MappingObject.SOURCE_TOKEN) {
                    MappingObject.SourceToken tobj = (MappingObject.SourceToken) obj;
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
    
    /**
     * @param ast
     * @param c
     * @param context
     * @param prefix
     * @param col
     * @throws PcalTLAGenException
     */
    private void GenAssign(AST.Assign ast, Changed c, String context, String prefix, int col)
            throws PcalTLAGenException
    {
        Changed cThis = new Changed(c);
        StringBuffer sb = new StringBuffer();
//        Vector vlines = new Vector();
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
        while (i < ast.ass.size())
        {
            int iFirst = i;
            AST.SingleAssign sF = (AST.SingleAssign) ast.ass.elementAt(i);
            int iLast = i;
            boolean hasAssignmentWithNoSubscript = false;
            boolean lastAssignmentHasNoSubscript = EmptyExpr(sF.lhs.sub);
            AST.SingleAssign sL = (AST.SingleAssign) ast.ass.elementAt(i);
            while (iLast < ast.ass.size() && sF.lhs.var.equals(sL.lhs.var))
            {
                if (lastAssignmentHasNoSubscript) {
                    hasAssignmentWithNoSubscript = true;
                }
                iLast = iLast + 1;
                if (iLast < ast.ass.size()) {
                    sL = (AST.SingleAssign) ast.ass.elementAt(iLast);
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
            Vector lines = new Vector(); // For collecting generated lines

            if (hasMultipleVars) {
                sb.append("/\\ ");
            }
            if (iFirst == iLast)
            {
                /*
                 * This is a single assignment to the variable.
                 */
                AST.SingleAssign sass = sF;

                addLeftParen(sass.getOrigin());
                TLAExpr sub = AddSubscriptsToExpr(sass.lhs.sub, SubExpr(Self(context)), c);
                TLAExpr rhs = AddSubscriptsToExpr(sass.rhs, SubExpr(Self(context)), c);
                if (mp
                        && (sass.lhs.var.equals("pc") || IsProcedureVar(sass.lhs.var) || IsProcessSetVar(sass.lhs.var) || sass.lhs.var
                                .equals("stack")))
                {
                    /* Generate single assignment to variable with self subscript */
                    sb.append(sass.lhs.var);
                    sb.append("' = [");
                    int wrapCol = sb.length() + 2;
                    sb.append(sass.lhs.var);
                    sb.append(" EXCEPT ");
                    
                    Vector selfAsSV = self.toStringVector();
                    
                    // The test for selfAsSV size added by LL on 22 Jan 2011
                    // because wrapping screws up the kludgeToFixPCHandlingBug
                    // hack.
                    if ( (sb.length() + prefix.length() > ssWrapColumn)
                         && (selfAsSV.size() == 0))
                    {
//                        lines.addElement(sb.toString());
                        addOneLineOfTLA(sb.toString());
                        sb = new StringBuffer(NSpaces(wrapCol));
                    }
                    sb.append("![");
                    addOneTokenToTLA(sb.toString());
                    addLeftParen(self.getOrigin());
                    addExprToTLA(self);
                    addRightParen(self.getOrigin());
                    
//                    
//                    // following code was modified by LL on 22 Jan 2011 as part of
//                    // fixing bug 11_01_13, which required modifications to handle
//                    // the case where self is a multi-line formula, which can happen
//                    // for a "process (P = exp)" when exp is multi-line.
//                    int here = sb.length();
//                    for (int idx = 0; idx < selfAsSV.size(); idx++) {
//                        if (idx > 0) {
//                            sb.append("\n");
//                            sb.append(NSpaces(here + kludgeToFixPCHandlingBug));
//                        }
//                        sb.append((String) selfAsSV.elementAt(idx)) ;
//                    }
////                    sb.append(self);
//                    sb.append("]");
//                    here = here + ((String) selfAsSV.elementAt(selfAsSV.size()-1)).length() + 1;
                      addOneTokenToTLA("]");
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
                        addLeftParen(sub.getOrigin());
                        addExprToTLA(sub);
                        addRightParen(sub.getOrigin());
                        
//                        sb.append((String) sv.elementAt(0));
//                        for (int v = 1; v < sv.size(); v++)
//                        {
//                            lines.addElement(sb.toString());
//                            sb = new StringBuffer(NSpaces(here));
//                            sb.append((String) sv.elementAt(v));
//                        }
                    }
                    addOneTokenToTLA(" = ");;
                    addLeftParen(rhs.getOrigin());
                    addExprToTLA(rhs);
                    addRightParen(rhs.getOrigin());
                    addOneTokenToTLA("]");
//                    sb.append(" = ");
//                    here = sb.length();
//                    sv = rhs.toStringVector();
//                    sb.append((String) sv.elementAt(0));
//                    for (int v = 1; v < sv.size(); v++)
//                    {
//                        lines.addElement(sb.toString());
//                        sb = new StringBuffer(NSpaces(here));
//                        sb.append((String) sv.elementAt(v));
//                    }
//                    sb.append("]");
//                    lines.addElement(sb.toString());
                    sb = new StringBuffer();
                } else if (!EmptyExpr(sass.lhs.sub))
                {
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
//                    
//                    int here = sb.length();
//                    Vector sv = sub.toStringVector();
//                    sb.append((String) sv.elementAt(0));
//                    for (int v = 1; v < sv.size(); v++)
//                    {
//                        lines.addElement(sb.toString());
//                        sb = new StringBuffer(NSpaces(here));
//                        sb.append((String) sv.elementAt(v));
//                    }
//                    sb.append(" = ");
//                    here = sb.length();
//                    sv = rhs.toStringVector();
//                    sb.append((String) sv.elementAt(0));
//                    for (int v = 1; v < sv.size(); v++)
//                    {
//                        lines.addElement(sb.toString());
//                        sb = new StringBuffer(NSpaces(here));
//                        sb.append((String) sv.elementAt(v));
//                    }
//                    sb.append("]");
//                    lines.addElement(sb.toString());
                    sb = new StringBuffer();
                } else
                {
                    /* 
                     * Generate assignment to a variable with no subscript at all.
                     */
                    sb.append(sass.lhs.var);
                    sb.append("' = ");
//                    int here = sb.length();
                    boolean needsParens = NeedsParentheses(rhs.toStringVector());
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
                    
//                    Vector sv = Parenthesize(rhs.toStringVector());
//                    /*******************************************************
//                    * Call of Parenthesize added by LL on 27 Feb 2008.     *
//                    * See bug_08-02-18.                                    *
//                    *******************************************************/
//                    for (int v = 0; v < sv.size(); v++)
//                    {
//                        sb.append((String) sv.elementAt(v));
//                        lines.addElement(sb.toString());
//                        sb = new StringBuffer(NSpaces(here));
//                    }
// Debugging
//Vector exprVec = rhs.toMappingVector();
//MappingObject.shiftMappingVector(exprVec, here);
//MappingObject.printMappingVector(exprVec);
//System.out.println("origin: " + rhs.getOrigin().toString() );
                    
                    sb = new StringBuffer();
                }
                addRightParen(sass.getOrigin());
            } else
            {
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
                boolean subscript = (mp && (IsProcedureVar(sass.lhs.var) || IsProcessSetVar(sass.lhs.var)));
                while (iFirst <= iLast)
                {
                    sass = (AST.SingleAssign) ast.ass.elementAt(iFirst);
                    TLAExpr sub = AddSubscriptsToExpr(sass.lhs.sub, SubExpr(Self(context)), c);
                    TLAExpr rhs = AddSubscriptsToExpr(sass.rhs, SubExpr(Self(context)), c);
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
                        TLAExpr self = Self(context);
                        addLeftParen(self.getOrigin());
                        addExprToTLA(self);
                        addOneTokenToTLA("]");
                        
//                        Vector selfAsSV = Self(context).toStringVector();
//                        for (int idx = 0; idx < selfAsSV.size(); idx++) {
//                          String start = " ";
//                          if (idx == 0) {
//                              sb.append("[");
//                          } else {
//                              sb.append("\n");
//                              sb.append(NSpaces(here + 1));
//                          }
//                          sb.append((String) selfAsSV.elementAt(idx));
//                        }
//                        sb.append("]");
//                        here = here + ((String) selfAsSV.elementAt(selfAsSV.size()-1)).length() + 2;
                    }
                    else {
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
//                    Vector sv = sub.toStringVector();
//                    if (sv.size() > 0)
//                    {
//                        sb.append((String) sv.elementAt(0));
//                        for (int v = 1; v < sv.size(); v++)
//                        {
//                            lines.addElement(sb.toString());
//                            sb = new StringBuffer(NSpaces(here));
//                            sb.append((String) sv.elementAt(v));
//                        }
//                    }
//                    sb.append(" = ");
//                    here = sb.length();
//                    sv = rhs.toStringVector();
//                    sb.append((String) sv.elementAt(0));
//                    for (int v = 1; v < sv.size(); v++)
//                    {
//                        lines.addElement(sb.toString());
//                        sb = new StringBuffer(NSpaces(here));
//                        sb.append((String) sv.elementAt(v));
//                    }
//                    sb.append(((iFirst == iLast) ? "]" : ","));
//                    lines.addElement(sb.toString());
                    sb = new StringBuffer();
                    if (iFirst < iLast) {
                        endCurrentLineOfTLA();
                        AddSpaces(sb, cc);
                    }
                    iFirst = iFirst + 1;
                }
            }

//            vlines.addElement(lines);
            i = iLast + 1;
            if (i <  ast.ass.size()) {
                endCurrentLineOfTLA();
                AddSpaces(sb, prefix.length());
            }
        }
        addRightParen(ast.getOrigin());
        endCurrentLineOfTLA();
        
        c.Merge(cThis);
        // Append generated code to tlacode
//        sb = new StringBuffer(prefix);
//        col = sb.length();
//        if (numAssigns > 1)
//            sb.append("/\\ ");
//        if (vlines.size() > 0)
//        {
//            for (int v1 = 0; v1 < vlines.size(); v1++)
//            {
//                Vector vl = (Vector) vlines.elementAt(v1);
//                for (int v2 = 0; v2 < vl.size(); v2++)
//                {
//                    sb.append((String) vl.elementAt(v2));
//                    tlacode.addElement(sb.toString());
//                    sb = new StringBuffer(NSpaces(col));
//                    if ((v1 > 0 || numAssigns > 1) && (v2 != vl.size() - 1))
//                        sb.append("   ");
//                }
//                sb.append("/\\ ");
//            }
//        }
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
    private void GenIf(AST.If ast, Changed c, String context, String prefix, int col) throws PcalTLAGenException
    {
        Changed cThen = new Changed(c);
        Changed cElse = new Changed(c);
        int lineUncThen;
        StringBuffer sb = new StringBuffer(prefix);
        TLAExpr test = null;
        test = AddSubscriptsToExpr(ast.test, SubExpr(Self(context)), c);
//        Vector sv = test.toStringVector();
        sb.append("IF ");
        int here = sb.length();
        /*************************************************************
        * LL removed a bogus "- 1" here on 31 Jan 2006.              *
        *************************************************************/
        addLeftParen(ast.getOrigin());
        addOneTokenToTLA(sb.toString());
        addExprToTLA(test);
        endCurrentLineOfTLA();
        
//        sb.append((String) sv.elementAt(0));
//        for (int v = 1; v < sv.size(); v++)
//        {
//            tlacode.addElement(sb.toString());
//            sb = new StringBuffer(NSpaces(here));
//            sb.append((String) sv.elementAt(v));
//        }
//        tlacode.addElement(sb.toString());
        
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
//        tlacode.addElement(sb.toString());
        addOneLineOfTLA(sb.toString());
        sb = new StringBuffer(NSpaces(here - "THEN ".length()) + "ELSE ");
        here = sb.length();
        if (ast.Else.size() == 0)
        {
            sb.append("/\\ TRUE");
//            tlacode.addElement(sb.toString());
            addOneLineOfTLA(sb.toString());
            
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
//                tlacode.addElement(sb.toString());
                addOneLineOfTLA(sb.toString());
                sb = new StringBuffer(NSpaces(cc));
                sb.append((String) uncElse.elementAt(i));
            }
            sb.append(" >>");
//            tlacode.addElement(sb.toString());
            addOneTokenToTLA(sb.toString());
            addRightParen(ast.getOrigin());
            endCurrentLineOfTLA();
        } else if (cElse.NumUnchanged(cThen) == 1)
        {   // Change made by LL on 16 Mar 2011 so that, if there is a single
        	// unchanged variable v, it produces v' = v if v is a short variable,
        	// otherwise it produces UNCHANGED v
        	//
            // sb.append("UNCHANGED " + cElse.Unchanged(cThen));
        	String uc = cElse.Unchanged(cThen);
        	if (uc.length() > 5) {
        		sb.append("UNCHANGED " + uc);
        	} else {
        		sb.append(uc + "' = " + uc);
        	}
//            tlacode.addElement(sb.toString());
            addOneTokenToTLA(sb.toString());
            addRightParen(ast.getOrigin());
            endCurrentLineOfTLA();
        } else 
        {
            /*
             * There is no UNCHANGED after the ELSE, so we have to put
             * the RightParen for the whole if statement at the end of
             * the last line already generated
             */
            ((Vector) mappingVector.elementAt(mappingVector.size()-1))
               .add(new MappingObject.RightParen(ast.getOrigin().getEnd()));
        }

        // Patch up the UNCHANGED for the THEN branch
        sb = new StringBuffer((String) tlacode.elementAt(lineUncThen));
        tlacode.removeElementAt(lineUncThen);
        mappingVector.removeElementAt(lineUncThen);
        if (cThen.NumUnchanged(cElse) > 1)
        {
            Vector uncThen = cThen.Unchanged(cElse, wrapColumn - sb.length() - "UNCHANGED << ".length());
            sb.append("UNCHANGED << ");
            int cc = sb.length();
            sb.append((String) uncThen.elementAt(0));
            for (int i = 1; i < uncThen.size(); i++)
            {
                tlacode.insertElementAt(sb.toString(), lineUncThen);

                 //set the mappingVector entry
                mappingVector.insertElementAt(stringToTLATokens(sb.toString()), lineUncThen);

                lineUncThen = lineUncThen + 1;
                sb = new StringBuffer(NSpaces(cc));
                sb.append((String) uncThen.elementAt(i));
            }
            sb.append(" >>");
            tlacode.insertElementAt(sb.toString(), lineUncThen);
            Vector vec =  stringToTLATokens(sb.toString());
            
            // The following is bogus because the RightParen for the
            // entire procedure is inserted after (or instead of) the
            // ELSE's UNCHANGED
            // vec.add(new MappingObject.RightParen(ast.getOrigin().getEnd()));
            
            mappingVector.insertElementAt(vec, lineUncThen);
                    
        } else if (cThen.NumUnchanged(cElse) == 1)
        {   // Change made by LL on 16 Mar 2011 so that, if there is a single
        	// unchanged variable v, it produces v' = v if v is a short variable,
        	// otherwise it produces UNCHANGED v
        	//
            // sb.append("UNCHANGED ");
            // sb.append(cThen.Unchanged(cElse));
        	String uc = cThen.Unchanged(cElse);
        	if (uc.length() > 5) {
        		sb.append("UNCHANGED " + uc);
        	} else {
        		sb.append(uc + "' = " + uc);
        	}
            tlacode.insertElementAt(sb.toString(), lineUncThen);
            Vector vec =  stringToTLATokens(sb.toString());
            // The following is bogus because the RightParen for the
            // entire procedure is inserted after (or instead of) the
            // ELSE's UNCHANGED
            // vec.add(new MappingObject.RightParen(ast.getOrigin().getEnd()));
            mappingVector.insertElementAt(vec, lineUncThen);
        }

        // Merge the change lists together
        c.Merge(cThen);
        c.Merge(cElse);
    }
    
    /**
     * Returns the vector of MappingObjects containing the BeginTLAToken and
     * EndTLAToken that are put in the mappingVector by a call of addOneLineOfTLA.
     * The code was essentially copied from addOneTokenToTLA.
     * 
     * @param token
     * @return
     */
    private Vector stringToTLATokens(String token) {
        Vector result = new Vector(3);
        
        String trimmedToken = token.trim() ;

        int numberOfLeftTrimmedTokens = 
                (trimmedToken.length() == 0) ? -1 :                   
                  token.indexOf(trimmedToken.charAt(0));
             
             /**
              * Handle a token of only space characters. 
              */
             if (numberOfLeftTrimmedTokens == -1) {
                 numberOfLeftTrimmedTokens = 0 ;
                 trimmedToken = token ;
             }
             
             int objBegin = numberOfLeftTrimmedTokens;
             result.addElement(new MappingObject.BeginTLAToken(objBegin));
             result.addElement(new MappingObject.EndTLAToken(objBegin + trimmedToken.length()));
             return result;
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

        /*
         * Add the left paren for the statement.
         */
        addLeftParen(ast.getOrigin());
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
//            tlacode.addElement("Replace by UNCHANGED"); // 
            addOneLineOfTLA("Replace by UNCHANGED");
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
            mappingVector.removeElementAt(ucLocs[i]);
            int numUnchanged = cOrs[i].NumUnchanged(allC);
            String NotChanged = cOrs[i].Unchanged(allC);
            if (numUnchanged > 1)
            {
                /*
                 * The line should be wrapped if it's too long.
                 */
                String line = NSpaces(here) + "/\\ UNCHANGED <<" + NotChanged + ">>";
                tlacode.insertElementAt(line, ucLocs[i]);
                mappingVector.insertElementAt(stringToTLATokens(line), ucLocs[i]);
            } else if (numUnchanged == 1)
            {   // Change made by LL on 16 Mar 2011 so that, if there is a single
            	// unchanged variable v, it produces v' = v if v is a short variable,
            	// otherwise it produces UNCHANGED v
            	//
                // tlacode.insertElementAt(NSpaces(here) + "/\\ UNCHANGED " + NotChanged, ucLocs[i]);
            	if (NotChanged.length() > 5) {
            	    String line = NSpaces(here) + "/\\ UNCHANGED " + NotChanged;
                    tlacode.insertElementAt(line, ucLocs[i]);
                    mappingVector.insertElementAt(stringToTLATokens(line), ucLocs[i]);
//                    tlacode.insertElementAt(NSpaces(here) + "/\\ UNCHANGED " + NotChanged, ucLocs[i]);
            	} else {
            	    String line = NSpaces(here) + "/\\ " + NotChanged + "' = " + NotChanged;
            	    tlacode.insertElementAt(line, ucLocs[i]);
                    mappingVector.insertElementAt(stringToTLATokens(line), ucLocs[i]);
//            		tlacode.insertElementAt(NSpaces(here) + "/\\ " + NotChanged + "' = "
//            				+ NotChanged, ucLocs[i]);
            	}
            } 
        }
        ;
        /*
         * Add the right paren for the entire statement.
         */
        ((Vector) mappingVector.elementAt(mappingVector.size()-1))
        .add(new MappingObject.RightParen(ast.getOrigin().getEnd()));
        /**********************************************************************
        * Add the statement's unchangeds to c.                                *
        **********************************************************************/
        c.Merge(allC);
    }

    private void GenWith(AST.With ast, Changed c, String context, String prefix, int col) throws PcalTLAGenException
    {
        addLeftParen(ast.getOrigin());
        StringBuffer sb = new StringBuffer(prefix);
        TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
//        Vector sv = exp.toStringVector();
        if (ast.isEq)
        {
            /* generate LET statement */
            sb.append("LET ");
            sb.append(ast.var);
            sb.append(" == ");
            addOneTokenToTLA(sb.toString());
            addLeftParen(exp.getOrigin());
            addExprToTLA(exp);
            addRightParen(exp.getOrigin());
//            int here = sb.length();
//            sb.append((String) sv.elementAt(0));
//            for (int v = 1; v < sv.size(); v++)
//            {
//                tlacode.addElement(sb.toString());
//                sb = new StringBuffer(NSpaces(here));
//                sb.append((String) sv.elementAt(v));
//            }
            addOneTokenToTLA(" IN");
            endCurrentLineOfTLA();
//            sb.append(" IN");
//            tlacode.addElement(sb.toString());
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
            addOneTokenToTLA(sb.toString());
            addLeftParen(exp.getOrigin());
            addExprToTLA(exp);
            addRightParen(exp.getOrigin());
//            int here = sb.le
            addOneTokenToTLA(":");
            endCurrentLineOfTLA();
//            sb.append(":");
//            tlacode.addElement(sb.toString());
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
        
        /*
         * Add the right paren for the entire statement.
         */
        ((Vector) mappingVector.elementAt(mappingVector.size()-1))
        .add(new MappingObject.RightParen(ast.getOrigin().getEnd()));
    }

    private void GenWhen(AST.When ast, Changed c, String context, String prefix, int col) throws PcalTLAGenException
    {
        addOneTokenToTLA(prefix);
        
//        StringBuffer sb = new StringBuffer(prefix);
        TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
        addLeftParen(exp.getOrigin());
        addExprToTLA(exp);
        addRightParen(exp.getOrigin());
        endCurrentLineOfTLA();
//        Vector sv = exp.toStringVector();
//        
//// Debugging
////Vector vec = exp.toMappingVector();
////System.out.println("Original vec:");
////MappingObject.printMappingVector(vec);    
////System.out.println("RemoveRedundantParens(vec)");
////MappingObject.printMappingVector(TLAtoPCalMapping.RemoveRedundantParens(vec));
////System.out.println("Should be original mappingvector:");
////MappingObject.printMappingVector(vec); 
//
//        sb.append((String) sv.elementAt(0));
//        for (int v = 1; v < sv.size(); v++)
//        {
//            tlacode.addElement(sb.toString());
//            sb = new StringBuffer(NSpaces(col));
//            sb.append((String) sv.elementAt(v));
//        }
//        tlacode.addElement(sb.toString());
    }

    private void GenPrintS(AST.PrintS ast, Changed c, String context, String prefix, int col)
            throws PcalTLAGenException
    {
        StringBuffer sb = new StringBuffer(prefix);
        TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
        addLeftParen(ast.getOrigin());
        addOneTokenToTLA(prefix + "PrintT(");
        addExprToTLA(exp);
        addOneTokenToTLA(")");
        addRightParen(ast.getOrigin());
        endCurrentLineOfTLA();
        
//        Vector sv = exp.toStringVector();
//        // The following modified 19 Nov 05 by LL to use PrintT instead of Print
//        sb.append("PrintT(");
//        sb.append((String) sv.elementAt(0));
//        for (int v = 1; v < sv.size(); v++)
//        {
//            tlacode.addElement(sb.toString());
//            sb = new StringBuffer(NSpaces(col + "PrintT(".length()));
//            sb.append((String) sv.elementAt(v));
//        }
//        sb.append(")");
//        tlacode.addElement(sb.toString());
    }

    /********************************************************/
    /* Assert(ast.expr, "Failure of assertion at... ")      */
    /**
     *******************************************************/
    private void GenAssert(AST.Assert ast, Changed c, String context, String prefix, int col)
            throws PcalTLAGenException
    {
        addLeftParen(ast.getOrigin());
        StringBuffer sb = new StringBuffer(prefix);
        StringBuffer sc = new StringBuffer();
        TLAExpr exp = AddSubscriptsToExpr(ast.exp, SubExpr(Self(context)), c);
//        Vector sv = exp.toStringVector();
        sb.append("Assert(");
        addOneTokenToTLA(sb.toString());
        addLeftParen(exp.getOrigin());
        addExprToTLA(exp);
        addRightParen(exp.getOrigin());
        int here = sb.length();
//        sb.append((String) sv.elementAt(0));
//        for (int v = 1; v < sv.size(); v++)
//        {
//            tlacode.addElement(sb.toString());
//            sb = new StringBuffer(NSpaces(col + "Assert(".length()));
//            sb.append((String) sv.elementAt(v));
//        }
//        sb.append(", ");
        sb = new StringBuffer(", ");
        sc.append("\"Failure of assertion at ");
        sc.append(ast.location());
        // modified on 23 Mar 2006 by LL to use location() instead of
        // ast.line and ast.col
        sc.append(".\")");
        if (tlacodeNextLine.length() + sb.length() + sc.length() < wrapColumn) {
            addOneTokenToTLA(sb.toString() + sc.toString());
        }
//        if (sb.length() + sc.length() < wrapColumn)
//            tlacode.addElement(sb.toString() + sc.toString());
        else
        {
            addOneTokenToTLA(sb.toString());
            endCurrentLineOfTLA();
            addOneTokenToTLA(NSpaces(here) + sc.toString());
//            tlacode.addElement(sb.toString());
//            tlacode.addElement(NSpaces(here) + sc.toString());
        }
        addRightParen(ast.getOrigin());
        endCurrentLineOfTLA();
    }

    /********************************************************/
    /* I generate a TRUE conjunct, which is useless, but so */
    /* is a skip statement.                                 */
    /********************************************************/
    private void GenSkip(AST.Skip ast, Changed c, String context, String prefix, int col)
    {
//        tlacode.addElement(prefix + "TRUE");
        addOneTokenToTLA(prefix);
        addLeftParen(ast.getOrigin());
        addOneTokenToTLA("TRUE");
        addRightParen(ast.getOrigin());
        endCurrentLineOfTLA();
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
      throws PcalTLAGenException
    {
        /*******************************************************************
        * lVars and gVars are vectors of strings, each element being a     *
        * variable name.  They hold the local and global variables,        *
        * respectively.                                                    *
        *******************************************************************/
        Vector lVars = new Vector();
        Vector gVars = new Vector();
        
        /**
         * lVarsSource and gVarsSource are vectors of AST.VarDecl objects that 
         * generated the elements of lVars and gVars, where PVarDecl objects
         * are converted to VarDecl objects.
         */
        Vector lVarsSource = new Vector();
        Vector gVarsSource = new Vector();

        /*******************************************************************
        * Set gVars to the global variables, including pc and `stack' if   *
        * there are procedures, and add these variables to vars.           *
        *******************************************************************/
        if (globals != null)
            for (int i = 0; i < globals.size(); i++)
            {
                AST.VarDecl decl = (AST.VarDecl) globals.elementAt(i);
                gVars.addElement(decl.var);
                gVarsSource.addElement(decl);
                vars.addElement(decl.var);
            }
        if (! ParseAlgorithm.omitPC) {
          gVars.addElement("pc");
          /**
           * For added variables, create a VarDecl with null origin.
           */
          AST.VarDecl pcVarDecl = new AST.VarDecl();
          pcVarDecl.var = "pc";
          gVarsSource.addElement(pcVarDecl);
          vars.addElement("pc");
        }
        if (procs != null && procs.size() > 0)
        {
            gVars.addElement("stack");
            /**
             * For added variables, create a VarDecl with null origin.
             */
            AST.VarDecl pcVarDecl = new AST.VarDecl();
            pcVarDecl.var = "stack";
            gVarsSource.addElement(pcVarDecl);
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
                        lVarsSource.addElement(decl.toVarDecl()) ;
                        vars.addElement(decl.var);
                        pcV.addElement(decl.var);
                    }
                if (proc.decls != null)
                    for (int p = 0; p < proc.decls.size(); p++)
                    {
                        AST.PVarDecl decl = (AST.PVarDecl) proc.decls.elementAt(p);
                        lVars.addElement(decl.var);
                        lVarsSource.addElement(decl.toVarDecl()) ;
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
                        lVarsSource.addElement(decl);
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
            addOneLineOfTLA("CONSTANT defaultInitValue");
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
            gVarsSource.addAll(lVarsSource) ;
            GenVarDecl(gVars, gVarsSource); 
        } else
        {
            /******************************************************************
            * There is a `define' statement.  In this case, must declare      *
            * global and local variables separately.  Also, set gVars to      *
            * vector of all variables.                                        *
            ******************************************************************/
            GenVarDecl(gVars, gVarsSource);
            addOneLineOfTLA("");
            addOneLineOfTLA("(* define statement *)");
            addExprToTLA(defs);
//            Vector sv = defs.toStringVector();
//            for (int i = 0; i < sv.size(); i++)
//            {
//                tlacode.addElement((String) sv.elementAt(i));
//            }
            ;
            addOneLineOfTLA("");
            GenVarDecl(lVars, lVarsSource); // to be fixed
            gVars.addAll(lVars);
            gVarsSource.addAll(lVarsSource);
        }
        ;
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
//        StringBuffer var = new StringBuffer("vars == << ");
//        StringBuffer curLine = new StringBuffer("vars == << ");
        addOneTokenToTLA("vars == << ") ;
        int indent = tlacodeNextLine.length();
        for (int i = 0; i < gVars.size(); i++)
        {
            if (i > 0)
            {
//                var.append(", ");
//                curLine.append(", ");
//                tlacodeNextLine = tlacodeNextLine + ", ";
                addOneTokenToTLA(", ");
            }
            ;
            String vbl = (String) gVars.elementAt(i);
            AST.VarDecl vblDecl = (AST.VarDecl) gVarsSource.elementAt(i);
            Region vblOrigin = vblDecl.getOrigin();
//            if (curLine.length() + vbl.length() + 1 > wrapColumn)
            if (tlacodeNextLine.length() + vbl.length() + 1 > wrapColumn)
            {
//                curLine = new StringBuffer("vars == << ");
//                var.append("\n" + NSpaces("vars == << ".length()));
                endCurrentLineOfTLA();
                tlacodeNextLine = NSpaces(indent);
            }
//            var.append(vbl);
//            curLine.append(vbl);
            addOneSourceTokenToTLA(vbl, vblOrigin);
        }
//        if (curLine.length() + " >>".length() + 1 > wrapColumn)
        if (tlacodeNextLine.length() + " >>".length() + 1 > wrapColumn)
        {
//            var.append("\n" + NSpaces("vars ==".length()));
            endCurrentLineOfTLA() ;
            tlacodeNextLine = NSpaces("vars ==".length());
        }
        ;
//        var.append(" >>");
//        tlacodeNextLine = tlacodeNextLine + " >>";
        addOneTokenToTLA(" >>");
//        tlacode.addElement(var.toString());
        addOneLineOfTLA("");
    }

    /**
     * Generate a VARIABLE(S) declarations.  The varVec argument is a vector of
     * strings that are the variables to be declared.  It does nothing if
     * the vector has length 0.  The varVecSource argument is a vector
     * of the same size as varVec that contains the AST.VarDecl objects.
     * <p>
     * Method added by LL on 25 Jan 2006.  
     * 
     * Modified 16 Dec 2011 to add varVecSource argument and generate TLA to 
     * PCal mapping.
     * 
     * @param varVec A vector of strings.
     * 
     * @param varVecSource A vector of AST.VarDecl objects.
     */
    public void GenVarDecl(Vector varVec, Vector varVecSource)
    {
//        StringBuffer res = new StringBuffer();
//        StringBuffer curLine = new StringBuffer("VARIABLES ");
        // for measuring length
        if (varVec.size() == 0)
        {
            return;
        }
        ;
        if (varVec.size() > 1)
        {
//            res.append("VARIABLES ");
            addOneTokenToTLA("VARIABLES ");
        } else
        {
//            res.append("VARIABLE ");
            addOneTokenToTLA("VARIABLE ");
        }
        ;
        for (int i = 0; i < varVec.size(); i++)
        {
            if (i > 0)
            {
//                res.append(", ");
//                curLine.append(", ");
                addOneTokenToTLA(", ");
            }
            ;
            String vbl = (String) varVec.elementAt(i);
            AST vblsource = (AST) varVecSource.elementAt(i);
//            if (curLine.length() + vbl.length() + 1 > wrapColumn)
            if (tlacodeNextLine.length() + vbl.length() + 1 > wrapColumn)
            {
//                curLine = new String
                endCurrentLineOfTLA();
                if (varVec.size() > 1)
                {
//                    res.append(NSpaces("VARIABLES ".length()));
                    tlacodeNextLine = tlacodeNextLine + NSpaces("VARIABLES ".length());
                } else
                {
//                    res.append(NSpaces("VARIABLE ".length()));
                    tlacodeNextLine = tlacodeNextLine + NSpaces("VARIABLE ".length());
                }
                ;
            }
            ;
//            res.append(vbl);
//            curLine.append(vbl);
            addOneSourceTokenToTLA(vbl, vblsource.getOrigin());
        }
        ;
//        tlacode.addElement(res.toString());
        endCurrentLineOfTLA();
    }

     /**
     * Generates the "ProcSet == ..." output.  It is just a union of all the
     * process sets, all on one line (except if a process set is a multi-line
     * expression).  It wouldn't be too hard to break long lines, but that
     * should be done later, if desired, after the TLA to PCal translation
     * is finished.  
     */
    public void GenProcSet()
    {
        StringBuffer ps = new StringBuffer();
        if (st.processes == null || st.processes.size() == 0)
            return;
//        ps.append("ProcSet == ");
        addOneTokenToTLA("ProcSet == ");
        for (int i = 0; i < st.processes.size(); i++)
        {
            PcalSymTab.ProcessEntry proc = (PcalSymTab.ProcessEntry) st.processes.elementAt(i);
//            Vector sv = proc.id.toStringVector();
            if (i > 0) {
//                ps.append(" \\cup ");
                addOneTokenToTLA(" \\cup ");
            }
            addLeftParen(proc.id.getOrigin());
            if (proc.isEq) {
//                ps.append("{");
                addOneTokenToTLA("{");
            }
            else {
//                ps.append("(");
                addOneTokenToTLA("(");
            }
            int col = ps.length();
//            ps.append((String) sv.elementAt(0));
//            for (int v = 1; v < sv.size(); v++)
//            {
//                tlacode.addElement(ps.toString());
//                ps = new StringBuffer(NSpaces(col));
//                ps.append((String) sv.elementAt(v));
//            }
            addExprToTLA(proc.id);
            if (proc.isEq) {
//                ps.append("}");
                addOneTokenToTLA("}");
            }
            else {
//                ps.append(")");
                addOneTokenToTLA(")");
            }
            addRightParen(proc.id.getOrigin());
        }
//        tlacode.addElement(ps.toString());
//        tlacode.addElement("");
        endCurrentLineOfTLA();
        addOneLineOfTLA("");
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
//            tlacode.addElement(is.toString());
            addOneLineOfTLA(is.toString()) ;
            is = new StringBuffer(NSpaces(col));
            for (int i = 0; i < globals.size(); i++)
            {
                AST.VarDecl decl = (AST.VarDecl) globals.elementAt(i);
                addVarDeclToTLA(decl, is);
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
//                tlacode.addElement(is.toString());
                addOneLineOfTLA(is.toString());
                is = new StringBuffer(NSpaces(col));
                for (int p = 0; p < proc.params.size(); p++)
                {
                    AST.PVarDecl decl = (AST.PVarDecl) proc.params.elementAt(p);
                    if (!mp) {
                        addVarDeclToTLA(decl.toVarDecl(), is);
                    }
                    else {
                        is.append("/\\ ");
                        addOneTokenToTLA(is.toString());
                        addLeftParen(decl.getOrigin());
//                    is.append(decl.var);
                        is = new StringBuffer(decl.var);
                    /*******************************************************
                    * Modified on 31 Jan 2006 by LL to add subscripts to   *
                    * initialization expression if needed.  Also replaced  *
                    * test for "\\in" with assertion that it can't occur,  *
                    * since it's forbidden by the grammar.                 *
                    *******************************************************/
                        PcalDebug.Assert(decl.isEq);
                        is.append(" = ");
                        
//                    Vector sv;
//                    if (mp)
//                    {
//                        sv = AddSubscriptsToExpr(decl.val, 
//                              SubExpr(Self("procedure")), new Changed(new Vector()))
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
                                              new Changed(new Vector())));
                        addRightParen(decl.val.getOrigin());
                        addOneTokenToTLA("]");
                        addRightParen(decl.getOrigin());
                        endCurrentLineOfTLA();
                        
//                    int col2 = is.length();
//                    is.append((String) sv.elementAt(0));
//                    for (int v = 1; v < sv.size(); v++)
//                    {
//                        tlacode.addElement(is.toString());
//                        is = new StringBuffer(NSpaces(col2));
//                        is.append((String) sv.elementAt(v));
//                    }
//                    if (mp)
//                        is.append("]");
//                    tlacode.addElement(is.toString());
                    }
                    is = new StringBuffer(NSpaces(col));
                }
                for (int p = 0; p < proc.decls.size(); p++)
                {
                    /*
                     * Note: the following code is identical to the for loop
                     * code above for procedure variables.  (Well done, Keith!)
                     * I realized this too late to feel like procedurizing it.
                     */
                    AST.PVarDecl decl = (AST.PVarDecl) proc.decls.elementAt(p);
                    if (!mp) {
                        addVarDeclToTLA(decl.toVarDecl(), is);
                    }
                    else {
                        is.append("/\\ ");
                        addOneTokenToTLA(is.toString());
                        addLeftParen(decl.getOrigin());
//                    is.append(decl.var);
                        is = new StringBuffer(decl.var);
//                    is.append("/\\ ");
//                    is.append(decl.var);

                    /*******************************************************
                    * Modified on 31 Jan 2006 by LL to add subscripts to   *
                    * initialization expression if needed.  Also replaced  *
                    * test for "\\in" with assertion that it can't occur,  *
                    * since it's forbidden by the grammar.                 *
                    *******************************************************/
                        PcalDebug.Assert(decl.isEq);
                        is.append(" = ");
//                    Vector sv;
//                    if (mp)
//                    {
//                        sv = AddSubscriptsToExpr(decl.val, SubExpr(Self("procedure")), new Changed(new Vector()))
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
                                        new Changed(new Vector())));
                        addRightParen(decl.val.getOrigin());
                        addOneTokenToTLA("]");
                        addRightParen(decl.getOrigin());
                        endCurrentLineOfTLA();

//                    int col2 = is.length();
//                    is.append((String) sv.elementAt(0));
//                    for (int v = 1; v < sv.size(); v++)
//                    {
//                        tlacode.addElement(is.toString());
//                        is = new StringBuffer(NSpaces(col2));
//                        is.append((String) sv.elementAt(v));
//                    }
//                    if (mp)
//                        is.append("]");
//                    tlacode.addElement(is.toString());
                    }
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
//                tlacode.addElement(is.toString());
                addOneLineOfTLA(is.toString());
                is = new StringBuffer(NSpaces(col));
                for (int p = 0; p < proc.decls.size(); p++)
                {
                    /*
                     * In the comments below, (( and )) represent
                     * MappingObject.LeftParen and MappingObject.RightParen
                     * objects.
                     */
                    AST.VarDecl decl = (AST.VarDecl) proc.decls.elementAt(p);
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
                        is = new StringBuffer(decl.var);
                        if (decl.isEq) {
                            is.append(" = ");
                        }
                        else {
                            is.append(" \\in ");
                        }
                        addOneTokenToTLA(is.toString()); 
                        addLeftParen(decl.val.getOrigin());
                        addExprToTLA(decl.val);
                        addRightParen(decl.val.getOrigin());
                    }
                    else {
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
                            is = new StringBuffer(decl.var);
                            is.append(" = [self \\in ");
                            addOneTokenToTLA(is.toString());
                            addLeftParen(proc.id.getOrigin());
                            addExprToTLA(proc.id);
                            addRightParen(proc.id.getOrigin());
                            addOneTokenToTLA(" |-> " );
                            addLeftParen(decl.val.getOrigin());
                            addExprToTLA(AddSubscriptsToExpr(
                                           decl.val,
                                           SubExpr(Self("procedure")), 
                                           new Changed(new Vector())));
                            addRightParen(decl.val.getOrigin());
                            addOneTokenToTLA("]");
                            
                        }
                        else {
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
                            TLAExpr subexpr = proc.id.cloneAndNormalize();
                            TLAExpr expr = new TLAExpr();
                            expr.addLine();
                            expr.addToken(new TLAToken("[", 0, TLAToken.BUILTIN));
                            expr.addToken(new TLAToken("CHOOSE", 1, TLAToken.BUILTIN));
                            expr.addToken(new TLAToken("self", 8, TLAToken.IDENT));
                            expr.addToken(new TLAToken("\\in ", 13, TLAToken.BUILTIN));
                            expr.normalize();
                            expr.setOrigin(subexpr.getOrigin()); // see what this does.
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

                            /*
                             * Now we output the TLA+ code.
                             */
                            is = new StringBuffer(decl.var);
                            is.append(" \\in [");
                            addOneTokenToTLA(is.toString());
                            addLeftParen(proc.id.getOrigin());
                            addExprToTLA(proc.id);
                            addRightParen(proc.id.getOrigin());
                            addOneTokenToTLA(" -> " );
                            addLeftParen(decl.val.getOrigin());
                            addExprToTLA(AddSubscriptsToExpr(
                                          decl.val, expr, new Changed(new Vector())) );
                            addRightParen(decl.val.getOrigin());
                            addOneTokenToTLA("]");
                        }
                    }
                    /*
                     * This adds the final )) .
                     */
                    addRightParen(decl.getOrigin());
                    endCurrentLineOfTLA();
                    is = new StringBuffer(NSpaces(col));
                    
// everything from here down to the end of the for p loop should be commented out                                       
//                    is.append(decl.var);
//                    is = new StringBuffer(decl.var);
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
//                    Vector sv;
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
//                            sve = AddSubscriptsToExpr(decl.val, SubExpr(Self("procedure")), new Changed(new Vector()));
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
//                            sve = AddSubscriptsToExpr(decl.val, expr, new Changed(new Vector()));
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
//                    is.append((String) sv.elementAt(0));
//                    for (int v = 1; v < sv.size(); v++)
//                    {
//                        tlacode.addElement(is.toString());
//                        is = new StringBuffer(NSpaces(col2));
//                        is.append((String) sv.elementAt(v));
//                    }
//                    if (!proc.isEq)
//                        is.append("]");
//                    tlacode.addElement(is.toString()); 
//                    is = new StringBuffer(NSpaces(col));
// end of section to be commented out 
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
//            tlacode.addElement(is.toString());
            addOneLineOfTLA(is.toString());
            is = new StringBuffer(NSpaces(col));
        }
        /* pc initial value */
        if (! ParseAlgorithm.omitPC) {
          if (mp)
          {
              // On 4 May 2012, LL added useCase flag to inhibit adding of CASE for
              // a single process or process set.
              boolean useCase = st.processes.size() != 1;
              if (useCase) {
                is.append("/\\ pc = [self \\in ProcSet |-> CASE ");
             } else {
                 is.append("/\\ pc = [self \\in ProcSet |-> ");
             }
              int colPC = is.length();
              if (boxUnderCASE)
                  colPC = colPC - 3;
              for (int p = 0; p < st.processes.size(); p++)
              {
                  PcalSymTab.ProcessEntry pe = (PcalSymTab.ProcessEntry) st.processes.elementAt(p);
                    if (useCase) {
                        is.append("self ");
                        if (pe.isEq) {
                            is.append("= ");
                            // int colExpr = is.length();
                            addOneTokenToTLA(is.toString());
                            addLeftParen(pe.id.getOrigin());
                            addExprToTLA(pe.id);
                            addRightParen(pe.id.getOrigin());

                            // Vector sv = pe.id.toStringVector();
                            // is.append((String) sv.elementAt(0));
                            // for (int v = 1; v < sv.size(); v++)
                            // {
                            // addOneLineOfTLA(is.toString());
                            // // tlacode.addElement(is.toString());
                            // is = new StringBuffer(NSpaces(colExpr));
                            // is.append((String) sv.elementAt(v));
                            // }
                        } else {
                            is.append("\\in ");
                            // int colExpr = is.length();
                            // Vector sv = pe.id.toStringVector();
                            // is.append((String) sv.elementAt(0));
                            // for (int v = 1; v < sv.size(); v++)
                            // {
                            // tlacode.addElement(is.toString());
                            // is = new StringBuffer(NSpaces(colExpr));
                            // is.append((String) sv.elementAt(v));
                            // }
                            addOneTokenToTLA(is.toString());
                            addLeftParen(pe.id.getOrigin());
                            addExprToTLA(pe.id);
                            addRightParen(pe.id.getOrigin());

                        }
                        // is.append(" -> \"");
                        is = new StringBuffer(" -> \"");
                        is.append(pe.iPC);
                        if (p == st.processes.size() - 1)
                            is.append("\"]");
                        else if (!boxUnderCASE)
                            is.append("\" []");
                        else
                            is.append("\"");
                    } // end if (useCase)
                    else {
                        is.append("\"" + pe.iPC + "\"]");
                    }
//                  tlacode.addElement(is.toString());
                  addOneTokenToTLA(is.toString());
                  endCurrentLineOfTLA();
                  is = new StringBuffer(NSpaces(colPC));
                  if (boxUnderCASE && p < st.processes.size() - 1)
                      is.append("[] ");
             }
          } else
          {
              is.append("/\\ pc = \"" + st.iPC + "\"");
//              tlacode.addElement(is.toString());
              addOneLineOfTLA(is.toString());
          }
        }
//        tlacode.addElement("");
        addOneLineOfTLA("");
    }

    /************************************/
    /* Generate the Next == definition. */
    /************************************/
    private void GenNext()
    {
        // It we are omitting pc and this is a uniprocess
        // algorithm, then the definition of Next has
        // already been added.
        if (ParseAlgorithm.omitPC && !mp) {
            return;
        }
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
            addOneLineOfTLA(sb.toString());
//            tlacode.addElement(sb.toString());
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
                addOneLineOfTLA(sb.toString());
//                tlacode.addElement(sb.toString());
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
                    addOneLineOfTLA(sb.toString());
//                    tlacode.addElement(sb.toString());
                    
                    // The following if case was added by LL on 22 Jan 2011
                    // to correct part 1 of bug bug_11_01_13.  This  bug occurs
                    // when an "\in" process's set is multi-line and that
                    // process's next-state action comes immediately after 
                    // the Next == ..., with no " \/ " preceding it.  To fix the
                    // problem, we must add 6 fewer spaces to all lines after
                    // the first in that process's set than in other such sets. 
                    if ((nextS.size() == 0) && (nextSS.size() == 0) && (i == 0)) {
                        sb = new StringBuffer(NSpaces(col - 2));
                    } else {
                        sb = new StringBuffer(NSpaces(col + 4));
                    }
                }
                sb = new StringBuffer(NSpaces(col) + " \\/ ");
            }
        if (! (PcalParams.NoDoneDisjunct || ParseAlgorithm.omitStutteringWhenDone))
         { sb.append("(* Disjunct to prevent deadlock on termination *)");
           addOneLineOfTLA(sb.toString());
//           tlacode.addElement(sb.toString());
           sb = new StringBuffer(NSpaces(col + 4));
           if (mp)
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
               sb.append("((\\A self \\in ProcSet: pc[self] = \"Done\") /\\ " + "UNCHANGED vars)");
           else
               sb.append("(pc = \"Done\" /\\ UNCHANGED vars)");
               addOneLineOfTLA(sb.toString());
//               tlacode.addElement(sb.toString());
         } ;
         addOneLineOfTLA("");
//        tlacode.addElement("");
    }

    /****************************************/
    /* Generate the Spec == ... definition. */
    /****************************************/
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
    private void GenSpec()
    {   String safetyFormula = "Init /\\ [][Next]_vars" ;
    	
        if (    PcalParams.FairnessOption.equals("nof")
             || (!mp && PcalParams.FairnessOption.equals(""))) {
            addOneLineOfTLA("Spec == " + safetyFormula);
            addOneLineOfTLA("");
//        	tlacode.addElement("Spec == " + safetyFormula );
//        	tlacode.addElement("");
        	return;
        }
//System.out.println("foo |-> " + st.UseThis(PcalSymTab.PROCEDURE, "foo", ""));
//int to = st.FindProc("foo");
//PcalSymTab.ProcedureEntry pe =
//    (PcalSymTab.ProcedureEntry) st.procs.elementAt(to);
//AST.Procedure procAst = pe.ast;

    	StringBuffer sb = new StringBuffer("Spec == ");
        // Generate the requested fairness conjuncts

    	// wfNextConj is either null or  " /\ WF_(Next)" 
    	String wfNextConj = null; 
    	if (   PcalParams.FairnessOption.equals("wfNext")
    	    || PcalParams.FairAlgorithm
        	|| (!mp && (   PcalParams.FairnessOption.equals("wf")
        			    || PcalParams.FairnessOption.equals("sf"))))
        {
            // If uniprocess then wf and sf are the same as wfNext
        	wfNextConj = " /\\ WF_vars(Next)";
        }         
    	
    	// Now compute procFairnessFormulas to equal the processes' fairness 
    	// formulas, which is never null but may have zero length.
    	Vector procFairnessFormulas = new Vector() ;
        if (mp) {
           for (int i = 0; i < st.processes.size(); i++) {
        	   PcalSymTab.ProcessEntry p = (PcalSymTab.ProcessEntry) st.processes.elementAt(i);
        	   AST.Process pAst = p.ast ;
        	   int fairness = pAst.fairness;
        	   if (fairness != AST.UNFAIR_PROC) {
        		   String xf = (fairness == AST.WF_PROC) ? "WF" : "SF";
        		   
                   Vector pSelf = p.id.toStringVector();
                   
                   // makeLetIn is true iff prefix will be LET self == ... IN
                   boolean makeLetIn = false ;
                   
                   String qSelf = "self";
                   if (p.isEq) {
                       if (pSelf.size() > 1) {
                           makeLetIn = true ;
                       } else {
                           qSelf = (String) pSelf.elementAt(0);
                       }  
                   }
                   
                   Vector prefix = new Vector();
        		   if (makeLetIn || !p.isEq) {
                       int prefixSize = pSelf.size();
                       String prefixBegin;
                       String prefixEnd;
                       if (p.isEq) {
                           prefixBegin = "LET self == ";
                           prefixEnd = "";
                       } else {
                           prefixBegin = "\\A self \\in ";
                           prefixEnd = " : ";
                       }
                       String padding = NSpaces(prefixBegin.length());
                       for (int j = 0; j < prefixSize; j++) {
                           String line = (String) pSelf.elementAt(j);
                           if (j == 0) {
                               line = prefixBegin + line;
                           } else {
                               line = padding + line;
                           }
                           if (j == prefixSize - 1) {
                               line = line + prefixEnd;
                           }
                           prefix.addElement(line);
                       }
                       if (makeLetIn) {
                           prefix.addElement("IN ");
                       }
        		   } // end if (makeLetIn || !p.isEq)
        		   
        		   StringBuffer wfSB = new StringBuffer(xf + "_vars(");
        		   if (pAst.minusLabels != null && pAst.minusLabels.size() > 0) {
        		       wfSB.append("(pc[");
        		       wfSB.append(qSelf);
        		       if (pAst.minusLabels.size() == 1) {
        		           wfSB.append("] # \"");
        		           wfSB.append(pAst.minusLabels.elementAt(0));
        		           wfSB.append("\"");
        		       } else {
        		           wfSB.append("] \\notin {\"");
        		           for (int j = 0; j < pAst.minusLabels.size(); j++) {
        		               wfSB.append(pAst.minusLabels.elementAt(j));
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
        		   
        		   StringBuffer sfSB = null ;
        		   if (    xf.equals("WF") 
        		       && (pAst.plusLabels != null) 
        		       && (pAst.plusLabels.size() != 0)) {
        		       sfSB = new StringBuffer() ;
        		       for (int j = 0; j < pAst.plusLabels.size(); j++) {
        		           if (j != 0) {
        		               sfSB.append(" /\\ ");
        		           }
        		           sfSB.append("SF_vars(");
        		           sfSB.append(pAst.plusLabels.elementAt(j));
        		           if (!p.isEq) {
        		               sfSB.append("(self)");
        		           }
        		           sfSB.append(")");
        		       }
        		   }
        	   
        	       Vector  prcdFormulas = new Vector();
        	       Vector  procedures = pAst.proceduresCalled;
                   for (int k = 0; k < procedures.size(); k++) {
                       String originalName = (String) procedures.elementAt(k);
                       String name = st.UseThis(PcalSymTab.PROCEDURE, originalName, "");
                       int procedureIndex = st.FindProc(name);
                       PcalSymTab.ProcedureEntry pe =
                          (PcalSymTab.ProcedureEntry) st.procs.elementAt(procedureIndex);
                       AST.Procedure prcAst = pe.ast;

                       StringBuffer wfPrcSB = new StringBuffer(xf + "_vars(");
                       if (prcAst.minusLabels != null && prcAst.minusLabels.size() > 0) {
                           wfPrcSB.append("(pc[");
                           wfPrcSB.append(qSelf);
                           if (prcAst.minusLabels.size() == 1) {
                               wfPrcSB.append("] # \"");
                               wfPrcSB.append(prcAst.minusLabels.elementAt(0));
                               wfPrcSB.append("\"");
                           } else {
                               wfPrcSB.append("] \\notin {\"");
                               for (int j = 0; j < prcAst.minusLabels.size(); j++) {
                                   wfPrcSB.append(prcAst.minusLabels.elementAt(j));
                                   if (j == prcAst.minusLabels.size() - 1) {
                                       wfPrcSB.append("\"}");
                                   } else {
                                       wfPrcSB.append("\", \"");
                                   }
                               }
                           }
                           wfPrcSB.append(") /\\ ");
                       }
    
                       String prcName = pe.name + "(" + qSelf + ")";
                       wfPrcSB.append(prcName);
                       wfPrcSB.append(")");
                                          
                       StringBuffer sfPrcSB = null;
                       if (    xf.equals("WF") 
                           && (prcAst.plusLabels != null) 
                           && (prcAst.plusLabels.size() != 0)) {
                           sfPrcSB = new StringBuffer() ;
                           for (int j = 0; j < prcAst.plusLabels.size(); j++) {
                               if (j != 0) {
                                   sfPrcSB.append(" /\\ ");
                               }
                               sfPrcSB.append("SF_vars(");
                               sfPrcSB.append(prcAst.plusLabels.elementAt(j));
                               sfPrcSB.append("(" + qSelf + ")") ;
                               sfPrcSB.append(")");
                           }
                       }
                       prcdFormulas.addElement(
                            new FormulaPair(
                                    wfPrcSB.toString(), 
                                    (sfPrcSB == null) ? null : sfPrcSB.toString())
                          ) ;
                     } // end construction of prcdFormulas
        	       
        	       procFairnessFormulas.addElement(
        	         new ProcessFairness(
        	                 xf, 
        	                 prefix, 
        	                 wfSB.toString(), 
        	                 (sfSB == null) ? null : sfSB.toString(), 
        	                 prcdFormulas)
        	              ) ;
               } // end if (fairness != AST.UNFAIR_PROC)
           } 	   
        } // ends construction of procFairnessFormulas
           
        if (wfNextConj == null && procFairnessFormulas.size() == 0) {
            addOneLineOfTLA("Spec == " + safetyFormula);
            addOneLineOfTLA("");
//            tlacode.addElement("Spec == " + safetyFormula);
//            tlacode.addElement("");
            return;
        }
        addOneLineOfTLA("Spec == /\\ " + safetyFormula);
//        tlacode.addElement("Spec == /\\ " + safetyFormula) ;
        int indent = "Spec == /\\ ".length();
        
        if (wfNextConj != null) {
            addOneLineOfTLA("        /\\ WF_vars(Next)");
//            tlacode.addElement("        /\\ WF_vars(Next)");
        }
        for (int i = 0; i < procFairnessFormulas.size(); i++) {
            /*
             * The original code called format on the fairness formula, which can
             * create a string with \n characters embedded.  I've just split the
             * string into its individual lines and added them to tlacode one at a time.
             * However, the current and original code can both produce very long lines 
             * that could be wrapped.  So if this change does make a difference, then 
             * it would be better to completely rewrite the format method (which is only 
             * called here).
             */
             String str = 
                  "        /\\ " + 
                  ((ProcessFairness) procFairnessFormulas.elementAt(i)).format(indent).toString();
             String [] splitStr = str.split("\n");
             for (int j = 0; j < splitStr.length; j++) {
                 addOneLineOfTLA(splitStr[j]);
             }

//            tlacode.addElement(
//                        "        /\\ " +
//                      ((ProcessFairness) procFairnessFormulas.elementAt(i)).format(indent)
//                         );
        }
        addOneLineOfTLA("");
//        tlacode.addElement("");
        return;
    }

    /************************************/
    /* Generate the Termination ==      */
    /************************************/
    private void GenTermination()
    {
        // if we're omitting the pc or omitting the stuttering-when-done
        // clause of the Next action, then we shouldn't
        // generate the Termination definition.
        // Check of omitStutteringWhenDone added by LL on 30 Mar 2012.
        if (ParseAlgorithm.omitPC || ParseAlgorithm.omitStutteringWhenDone) {
            return;
        }
        StringBuffer sb = new StringBuffer();
        sb.append("Termination == <>(");
        if (mp)
            sb.append("\\A self \\in ProcSet: pc[self]");
        else
            sb.append("pc");
        sb.append(" = \"Done\")");
        addOneLineOfTLA(sb.toString());
        addOneLineOfTLA("");
//        tlacode.addElement(sb.toString());
//        tlacode.addElement("");
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
    /**********************************************************/
    private TLAExpr AddSubscriptsToExpr(TLAExpr exprn, TLAExpr sub, Changed c) throws PcalTLAGenException
    {
        /*
         * For testing, throw a null pointer exception if the begin/end substitution
         * mapping vectors are not properly matching in the returned expression
         */
//        int[] depths = new int[1000];
        
        int parenDepth = 0;
        for (int i = 0; i < exprn.tokens.size(); i++) {
            Vector line = (Vector) exprn.tokens.elementAt(i);
            for (int j = 0; j < line.size(); j++) {
                TLAToken tok = (TLAToken) line.elementAt(j);
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
        Vector exprVec = new Vector(); // the substituting exprs
        Vector stringVec = new Vector(); // the substituted ids
        TLAExpr expr = exprn.cloneAndNormalize();  // the expression to be returned

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
                    /*
                     * 15 Dec 2011:  The following code added to replace the
                     *    
                     *    exp.addToken(new TLAToken(tok.string, 0, TLAToken.IDENT));
                     *    
                     * that is commented out.  Note that this change can add a token with
                     * type ADDED rather than IDENT.  I don't think this matters.
                     */
                    TLAToken newTok = tok.Clone() ;
                    /*
                     * The new token should inherit nothing from the baggage of tok, whose
                     * only function is to provide the name
                     */
                    newTok.setBeginSubst(new Vector(2));
                    newTok.setEndSubst(new Vector(2));
                    newTok.source = null;
                    newTok.column = 0;
                    exp.addToken(newTok) ;
                    // exp.addToken(new TLAToken(tok.string, 0, TLAToken.IDENT));
                    if (prime) {
                        /*****************************************************
                        * Modified by LL on 30 Aug 2007.  The following      *
                        * call to addTokenOffset was originally a call to    *
                        * addToken.  See the comments for                    *
                        * TLAExpr.addTokenOffset().                          *
                        *****************************************************/
                        TLAToken primeTok = new TLAToken("'", 0, TLAToken.BUILTIN, true);
                        // The following stuff added by LL in Dec 2011 is bogus.  The
                        // token tok is just the first one of many in the exprn with
                        // the same name for which we want to substitute.  The only
                        // useful data in the token tok is its string.
                        //
                        // if (tok.source != null) {
                        //   primeTok.source = 
                        //           new Region(tok.source.getEnd(), tok.source.getEnd());
                        // }
                        // if (!subr) {
                        //    primeTok.setEndSubst(tok.getEndSubst());
                        //   newTok.setEndSubst(new Vector(2));
                        // }
                        exp.addTokenOffset(primeTok, 0);
                    }
                    if (subr)
                    {
                        TLAExpr subexp = sub.cloneAndNormalize();
                        
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
                        //
                        // if (tok.source != null) {
                        //   PCalLocation endOfTok = tok.source.getEnd();
                        //  subexp.firstToken().getBeginSubst().add(endOfTok);
                        //  subexp.lastToken().getEndSubst().add(endOfTok);
                        // }
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
                        // newTok.getEndSubst().addAll(subexp.lastToken().getEndSubst());
                        // subexp.lastToken().setEndSubst(newTok.getEndSubst());
                        // newTok.setEndSubst(new Vector(2));
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
        /*
         * For testing, throw a null pointer exception if the begin/end substitution
         * mapping vectors are not properly matching in the returned expression
         */
//        depths = new int[1000];
        
        parenDepth = 0;
        for (int i = 0; i < expr.tokens.size(); i++) {
            Vector line = (Vector) expr.tokens.elementAt(i);
            for (int j = 0; j < line.size(); j++) {
                TLAToken tok = (TLAToken) line.elementAt(j);
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
    private static TLAExpr SubExpr(TLAExpr sub)
    {
        if (sub != null)
        { 
            TLAExpr expr = sub.cloneAndNormalize();
              // This preserves the origin of the expression
            for (int i = 0; i < expr.tokens.size(); i++) {
                Vector tokenVec = (Vector) expr.tokens.elementAt(i);
                for (int j = 0; j < tokenVec.size(); j++) {
                   TLAToken tok = (TLAToken) tokenVec.elementAt(j);
                   tok.column = tok.column + 1;
                }
                if (i == 0) {
                    /*
                     * Set isAppended field of the "[" and "]" to true iff the first
                     * token of sub has isAppended field true, which should be the
                     * case iff it is the "self" token.
                     */
                    tokenVec.insertElementAt(
                          new TLAToken("[", 0, TLAToken.BUILTIN, sub.firstToken().isAppended()),
                          0);
                }
            }
            expr.addTokenOffset(
                    new TLAToken("]", 0, TLAToken.BUILTIN, sub.firstToken().isAppended()), 0);
            return expr;
        } else {
            return null;
        }
    }

    /*********************************************************/
    /* Gives the string to use when subscripting a variable. */
    /*********************************************************/
    // LL comment: it appears that PcalTLAGen.self is the 
    // current process id if this is being called in the context
    // of a process declared with `process (P = id)'.
    private TLAExpr Self(String context)
    {
        TLAExpr s = null;
        if (mp)
        {
            if (context.equals("procedure"))
                s = selfAsExpr();
            else
                s = self;
        }
        return s;
    }

    private static TLAExpr  selfAsExpr() {
        /*
         * This is a token that does not correspond to anything in the
         * PCal code, so it should have a null source field.
         * It has a true isAppended field because it is always appended
         * as a subscript to a variable.
         */
        TLAToken selfToken = new TLAToken("self", 0, TLAToken.IDENT, true);
        Vector tokenVec = new Vector();
        tokenVec.addElement(selfToken);
        Vector tokens = new Vector();
        tokens.addElement(tokenVec);
        TLAExpr expr = new TLAExpr(tokens);
//        expr.anchorTokens = new TLAToken[1];
//        expr.anchorTokens[0] = selfToken;
//        expr.anchorTokCol = new int[1];
//        expr.anchorTokCol[0] = 0;
        expr.normalize();
        return expr ;
    }
    /***********************************************************************
    * Comment added by LL: MakeExprPretty should never be called on an     *
    * expression any part of which was an expression in the input.         *
    * Fortunately, it is now called only for the expression "[self]", so   *
    * it is effectively a no-op.                                           *
    * Comment added 15 Dec 2011: In fact, it's not called at all.          *
    ***********************************************************************/
    public static void ObsoleteMakeExprPretty(TLAExpr expr)
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
    * nice to add the parentheses only if really necessary.  For now, the  *
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
        /*********************************************************************
        * Add the parentheses if necessary.                                  *
        *********************************************************************/
        if (NeedsParentheses(vec))
        {
            vec.setElementAt("(" + ((String) vec.elementAt(0)), 0);
            for (int i = 1; i < vec.size(); i++)
            {
                vec.setElementAt(" " + ((String) vec.elementAt(i)), i);
            }
            ;
            int curLineNum = vec.size() - 1;
            vec.setElementAt(((String) vec.elementAt(curLineNum)) + ")", curLineNum);
        }
        ;
        return vec;
    }
    
    /**
     * As part of adding the TLA to PCal translation code, LL removedseparated 
     * the code that decides if parentheses are needed from the Parenthesize 
     * method and put it into this method.  The Parenthesize method itself
     * will not be needed.
     */
    public static boolean  NeedsParentheses(Vector vec) {
        if (vec.size() == 0)
        {
            return false;
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
        
        return needParen;
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
     * 
     * @param token
     */
    private void addOneTokenToTLA(String token) {
        String trimmedToken = token.trim() ;
        
        int numberOfLeftTrimmedTokens = 
           (trimmedToken.length() == 0) ? -1 :                   
             token.indexOf(trimmedToken.charAt(0));
        
        /**
         * Handle a token of only space characters. 
         */
        if (numberOfLeftTrimmedTokens == -1) {
            numberOfLeftTrimmedTokens = 0 ;
            trimmedToken = token ;
        }
        
        int objBegin = tlacodeNextLine.length() + numberOfLeftTrimmedTokens;
        mappingVectorNextLine.addElement(new MappingObject.BeginTLAToken(objBegin));
        mappingVectorNextLine.addElement(new MappingObject.EndTLAToken(objBegin + trimmedToken.length()));
        tlacodeNextLine = tlacodeNextLine + token;
    }
    
    /**
     * If region is non-null, then adds string str to the TLA output
     * as a SourceToken object with that region.  Otherwise, it adds
     * it as a TLAToken, with Begin/EndTLAToken objects.
     * 
     * @param str
     * @param region
     */
    private void addOneSourceTokenToTLA(String str, Region region) {
        if (region == null) {
            addOneTokenToTLA(str);
            return;
        }
        
        int beginCol = tlacodeNextLine.length();
        int endCol = beginCol + str.length();
        mappingVectorNextLine.addElement(
                new MappingObject.SourceToken(beginCol, endCol, region));
             tlacodeNextLine = tlacodeNextLine + str;
    }
    /**
     * Adds a complete line of TLA "code" that does not correspond to
     * any PlusCal code.  Adds Begin/EndTLAToken objects to the mapping
     * iff the line does not equal "".
     * 
     * @param line
     */
    private void addOneLineOfTLA(String line) {
// temporarily commented out.
        if(tlacode.size() != mappingVector.size()) {
            PcalDebug.ReportBug("tlacode and mappingVector have different lengths") ;
        }
// The following added during testing.
//if(tlacode.size() != mappingVector.size()) {
//   System.out.println("tlacode and mappingVector have different lengths");
//}
        endCurrentLineOfTLA();
        if (line.length() == 0) {
            mappingVector.addElement(new Vector(2));
            tlacode.addElement("");
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
            tlacode.addElement(tlacodeNextLine) ;
            mappingVector.addElement(mappingVectorNextLine) ;
            tlacodeNextLine = "";
            mappingVectorNextLine = new Vector() ;
        } 
        else {
            if (mappingVectorNextLine.size() != 0) {
                /*
                 * There's something to go in the mappingVector that doesn't
                 * accompany any text.  It should be one or more RightParen or
                 * LeftParen objects, (or perhaps, eventually a Break), in which 
                 * case they should be put at the end of the previous mappingVector 
                 * line.  Anything else is a mistake.
                 */
                Vector lastLine = (Vector) mappingVector.elementAt(mappingVector.size()-1);
                for (int i = 0; i < mappingVectorNextLine.size(); i++) {
                    MappingObject obj = (MappingObject) mappingVectorNextLine.elementAt(i);
                    if (obj.getType() == MappingObject.RIGHT_PAREN ||
                        obj.getType() == MappingObject.LEFT_PAREN||
                        obj.getType() == MappingObject.BREAK) {
                       lastLine.add(obj); 
                    }
                    else {
                        PcalDebug.ReportBug("PcalTLAGen.endCurrentLineOfTLA found problem.");
                    }
                    mappingVectorNextLine = new Vector() ;
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
     * @param expr
     */
    private void addExprToTLA(TLAExpr expr) {
        Vector sv = expr.toStringVector() ;
        Vector exprMapping = expr.toMappingVector() ;
        int indent = tlacodeNextLine.length() ; 
        int nextLine = 0 ; 
        if (indent != 0) {
            /*
             * Need to combine first line of expr with 
             * tlacodeNextLine.
             */
            MappingObject.shiftMappingVector(exprMapping, indent);
            tlacodeNextLine = tlacodeNextLine + ((String) sv.elementAt(0));
            mappingVectorNextLine.addAll((Vector) exprMapping.elementAt(0));
            nextLine = 1;
            if (sv.size() > 1) {
               endCurrentLineOfTLA();
            }
        }
        if (sv.size() > 1) {
            String spaces = NSpaces(indent);
            while (nextLine < sv.size()-1) {
                tlacode.addElement(spaces + ((String) sv.elementAt(nextLine)));
                mappingVector.addElement((Vector) exprMapping.elementAt(nextLine));
                nextLine++ ;
            }
            tlacodeNextLine = spaces + ((String) sv.elementAt(nextLine)) ;
            mappingVectorNextLine = (Vector) exprMapping.elementAt(nextLine);
        }
        else if (indent == 0){
            /*
             * If indent != 0, then we've already added the one-line expression.
             */
            tlacodeNextLine = tlacodeNextLine + ((String) sv.elementAt(0));
            mappingVectorNextLine.addAll((Vector) exprMapping.elementAt(0));
        }
    }
    
    /**
     * Subroutine of GenInit that adds to the TLA translation the Init conjunct 
     * corresponding to the VarDecl decl for a global variable and, in a uniprocess
     * algorithm for a procedure or process variable It is called with the 
     * StringBuffer `is' containing the text that precedes the "/\" of the 
     * conjunct, which will be "Init == " or just spaces.
     * 
     * @param decl
     * @param is
     */
    private void addVarDeclToTLA(VarDecl decl, StringBuffer is) {
        Region origin = decl.getOrigin();
        is.append("/\\ ");
        addOneTokenToTLA(is.toString());
        addLeftParen(decl.getOrigin());
//        is.append(decl.var);
        is = new StringBuffer(decl.var);
        if (decl.isEq)
            is.append(" = ");
        else
            is.append(" \\in ");
//        int col2 = is.length();
//        Vector sv = Parenthesize(decl.val.toStringVector());
//        /*********************************************************
//        * Call to Parenthesize added by LL on 27 Feb 2008.       *
//        * See bug_08-02-18.                                      *
//        *********************************************************/
//        is.append((String) sv.elementAt(0));
//        for (int v = 1; v < sv.size(); v++)
//        {
//            tlacode.addElement(is.toString());
//            is = new StringBuffer(NSpaces(col2));
//            is.append((String) sv.elementAt(v));
//        }
//        tlacode.addElement(is.toString());
        addOneTokenToTLA(is.toString());
        addLeftParen(decl.val.getOrigin());
        boolean needsParens = NeedsParentheses(decl.val.toStringVector());
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
     * @param region
     */
    private void addLeftParen(Region region) {
        if (region != null) {
          mappingVectorNextLine.addElement(
              new MappingObject.LeftParen(region.getBegin()));
        }
    }
    
    /**
     * Adds a MappingObject.LeftParen object to the mapping vector
     * for the beginning of the Region region, if it's not null.
     * @param region
     */
    private void addRightParen(Region region) {
        if (region != null) {
          mappingVectorNextLine.addElement(
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
     *  
     * @param ast
     */
    private void addLeftParenV(AST ast, PCalLocation loc) {
        if (ast.getOrigin() == null) {
            return;
        }
        if (loc != null) {
            mappingVectorNextLine.addElement(
                    new MappingObject.LeftParen(loc));
        }
        else {
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
     *  
     * @param ast
     */
    private void addRightParenV(AST ast, PCalLocation loc) {
        if (ast.getOrigin() == null) {
            return;
        }
        if (loc!= null) {
            mappingVectorNextLine.addElement(
                    new MappingObject.RightParen(loc));
        }
        else {
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
    	public String wf ;
    	public String sf ;
    	
    	public FormulaPair(String wfVal, String sfVal) {
    		this.wf = wfVal;
    		this.sf = sfVal;
    	}
    	
    	/**
    	 * The string  wf /\ sf , or just wf if sf is null.
    	 * @return
    	 */
    	public String singleLine() {
    		if (sf == null) {
    			return wf ;
    		} 
    		return wf + " /\\ " + sf ;
    	}
    	
    	/**
    	 * The width of the singleLine representation of the 
    	 * conjunction of the formlas.
    	 * 
    	 * @return
    	 */
    	public int singleLineWidth() {
    	    if (sf == null) {
                return wf.length() ;
            } 
            return wf.length() + " /\\ ".length() + sf.length() ;   		
    	}
    	
    	/**
    	 * The representation of the conjunction of the formulas with
    	 * prefix /\s, where the first /\ appears in column col (Java
    	 * numbering), witout any ending "\n"
    	 * 
    	 * @return
    	 */
    	public String multiLine(int col) {
    		String val = "/\\ " + wf ;
    		if (sf == null) {
    			return val;
    		}
    		return val + "\n" + NSpaces(col) + "/\\ " + sf;
    	}
    }
    
    /**
     * Describes a process fairness formula, as described in the comments
     * preceding the  GetSpec() method above.
     * @author lamport
     *
     */
    public static class ProcessFairness {
    	public String xf ; // either "WF" or "SF"
    	public Vector  prefix ; 
    	    // StringVector either "\A self \in exp : " or
    	    // "LET self == exp \n IN " (note the ending space) or ""
    	public FormulaPair bodyFormulas ; // fairness conditions for the proc's body
    	public Vector prcdFormulas ; // fairness conditions for the procedure

    	/** 
    	 * The constructor
    	 * @param xfVal
    	 * @param prefixVal
    	 * @param bodyWF : can be null if bodySF is also null
    	 * @param bodySF : can be null
    	 * @param prcdVal
    	 */
    	public ProcessFairness (String xfVal, Vector  prefixVal, String bodyWF,
    			                String bodySF, Vector  prcdVal) {
    		xf = xfVal;
    		prefix = prefixVal;
    		bodyFormulas = null ;
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
    	 * 
    	 * @return
    	 */
    	public int singleLineWidth() {
    	    // Set maxPrefixWidth to length of longest non-final
    	    // line of prefix, width to lenght of final line
    	    int maxPrefixWidth = 0 ;
    	    int width = 0  ;
    	    if (prefix != null && prefix.size() > 0) {
    	        for (int i = 0; i < prefix.size() - 1; i++) {
    	            String line =  (String) prefix.elementAt(i);
    	            if (line.length() > maxPrefixWidth) {
    	                maxPrefixWidth = line.length();
    	            }
    	            String lastLine = (String) prefix.elementAt(prefix.size()-1);
    	            width = lastLine.length();
    	        }
    	    }
    	    width = width + bodyFormulas.wf.length();
            if (bodyFormulas.sf != null) {
                 width = width + bodyFormulas.sf.length();
            } 
            if (prcdFormulas != null) {
                for (int i = 0 ; i < prcdFormulas.size(); i++) {
                    width = width + ((FormulaPair) prcdFormulas.elementAt(i)).singleLineWidth();
                }
            }
            if (maxPrefixWidth > width) {
                return maxPrefixWidth;
            }
            return width ;
    	}
    	
    	/**
    	 * Returns the prefix as a StringBuffer, assuming it starts
    	 * in column col.  That is, all but the first line is indented
    	 * with col spaces, and all but the last line is ended with
    	 * a \n .
    	 * 
    	 * @param col
    	 * @return
    	 */
    	private StringBuffer prefixAsStringBuffer(int col) {
    	    StringBuffer val = new StringBuffer();
            if (prefix != null && prefix.size() > 0) {
                for (int i = 0; i < prefix.size(); i++) {
                    String line =  (String) prefix.elementAt(i);
                    if (i != 0) {
                        val.append(NSpaces(col));
                    }
                    val.append(line) ;
                    if (i != prefix.size()-1) {
                        val.append("\n") ;
                    }                   
                }
            }
            return val;
    	}
    	/**
    	 * The process fairness condition written as a single-line formula,
    	 * starting in column col.
    	 * @return
    	 */
    	public StringBuffer singleLine(int col) {
    	    StringBuffer val = prefixAsStringBuffer(col);
    	    val.append(bodyFormulas.wf);
    		if (bodyFormulas.sf != null) {
    			val.append(" /\\ ");
    			val.append(bodyFormulas.sf);
    		} 
    		if (prcdFormulas != null) {
    			for (int i = 0 ; i < prcdFormulas.size(); i++) {
    			    val.append(" /\\ ");
    				val.append(((FormulaPair) prcdFormulas.elementAt(i)).singleLine());
    			}
    		}
    		return val ;
    	}
    	
    	/**
    	 * Returns true iff format(col) should return a single-line version
    	 * of the formula.
    	 * 
    	 * @param col
    	 * @return
    	 */
    	private boolean fitsAsSingleLine(int col) {
    	    return     (col + singleLineWidth() <= PcalTLAGen.wrapColumn)
                    || (bodyFormulas.sf == null 
                        && (prcdFormulas == null || prcdFormulas.size() == 0));
    	}
    	/**
    	 * The process fairness condition written as a formula that
    	 * begins in column col (Java numbering) and ends with "\n".
    	 * It is formatted to try to extend no further than column 
    	 * PcalTLAGen.wrapColumn, but no individual formula is split
    	 * across lines.
    	 * 
    	 * @param col
    	 * @return
    	 */
    	public StringBuffer format(int col) {
    		int singleLineWidth = this.singleLineWidth();
    		/*
    		 * Return the single-line form if either it fits on the
    		 * line or if it consists of only the wf formula (so it can't
    		 * be put on multiple lines).
    		 */
    		if (fitsAsSingleLine(col)) {
    		    return this.singleLine(col);
    		}
    		StringBuffer val = prefixAsStringBuffer(col);
    		int prefixWidth = 0;
    		if (prefix != null && prefix.size() > 0) {
    		    prefixWidth = ((String) prefix.elementAt(prefix.size()-1)).length();
    		}
    		int curCol = col + prefixWidth;
    		String line = this.bodyFormulas.singleLine();
    		if (curCol + line.length() + 3 <= PcalTLAGen.wrapColumn) {
    		   val.append("/\\ " + line);
    		} else {
    			val.append(this.bodyFormulas.multiLine(curCol));
    		}
    		if (prcdFormulas == null) {
    			return val;
    		}
    		for (int i = 0; i < this.prcdFormulas.size(); i++) {
    		    FormulaPair form = (FormulaPair) this.prcdFormulas.elementAt(i) ;
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
    		        val.append("\n") ;
    		    }
    		    val.append(NSpaces(curCol));
    		    if (curCol + line.length() + 3 <= PcalTLAGen.wrapColumn) {
    	    		   val.append("/\\ " + line + "\n");
    	    		} else {
    	    			val.append(form.multiLine(curCol));
    	    		}
    		}
    		return val;
    	}

    	
    }
}
