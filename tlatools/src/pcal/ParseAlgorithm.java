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
*    labThen and labElse fields (equal to an empty Vector), and an         *
*    "either" statement is represented by a LabelEither object whose       *
*    clauses contain empty labOr fields.  The AST node's lbl field         *
*    holds the label (the absence of a label represented by                *
*    a lbl field equal to the empty string "").  The only difference       *
*    from the simple grammar is that a <Call> followed by an unlabeled     *
*    <Return> is converted into a single AST.CallReturn object.  This      *
*    pass does not produce any AST.If or AST.Either objects, and any       *
*    AST.While object it produces has an empty labDo field.                *
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

import java.util.Hashtable;
import java.util.Vector;
import pcal.exception.ParseAlgorithmException;
import pcal.exception.TLAExprException;
import pcal.exception.TokenizerException;
import pcal.exception.UnrecoverableException;
import tla2sany.parser.ParseError;
import tla2tex.Debug;


public class ParseAlgorithm
{ 
    private static PcalCharReader charReader;
     /**********************************************************************
     * The charReader argument to the Parse method is put here so other    *
     * methods can access it.  This makes the class totally thread unsafe. *
     **********************************************************************/

   public static String currentProcedure;
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
   public static Vector plusLabels;
   
   public static Vector minusLabels;
   
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
   public static boolean gotoUsed;
   public static boolean gotoDoneUsed;
   public static boolean omitPC;
   public static boolean omitStutteringWhenDone;
   
   public static Vector proceduresCalled;
   
   public static boolean hasDefaultInitialization;
     /**********************************************************************
     * Set true if any variable has a default initialization.              *
     * (Added by LL on 22 Aug 2007.)                                       *
     **********************************************************************/
     
/***************************************************************************
*                           CONSTRUCTING THE AST                           *
*                                                                          *
* For most nonterminals <NonTerm> in the simple grammar, there is a        *
* method GetNonTerm() that processes the input from the current position   *
* and returns an AST.NonTerm object.  There may also be a method           *
* GetNonTermSeq() that parses a sequence of <NonTerm> nodes and returns a  *
* vector of AST.NonTerm objects.                                           *
***************************************************************************/

   public static boolean hasLabel;
     /**********************************************************************
     * This variable is set to true by GetStmtSeq whenever a label is      *
     * found.  It is used in deciding whether or not to add labels to a    *
     * uniprocess algorithm.                                               *
     **********************************************************************/

   public static Hashtable allLabels;
     /**********************************************************************
     * Set by GetStmtSeq to a table of String objects containing all the   *
     * algorithm's (user-typed) labels.  The strings are the keys, the     *
     * value of all entries is 0.  The value of                            *
     * allLabels.containsKey("foo") is true iff "foo" is a label of the    *
     * algorithm.                                                          *
     **********************************************************************/

   public static int nextLabelNum ;
     /**********************************************************************
     * The number to be appended to PcalParams.LabelRoot to form the next  *
     * label to be added.                                                  *
     **********************************************************************/
     
   /************************************************************************
   * As described above, the method AddLabelsToStmtSeq determines where    *
   * labels are to be added.  Added labels are reported as a bug if the    *
   * user doesn't want them, and are printed in the terminal output if     *
   * she does and has specified the -reportLabels option.  The i-th entry  *
   * of the vectors addedLabels and addedLabelsLocs records the name of    *
   * the i-th added label and the location of the statement to which it    *
   * was added.                                                            *
   ************************************************************************/
   public static Vector addedLabels;
   public static Vector addedLabelsLocs;

   /**********************************************************************
    * Is set to the sequence of procedures.  It's easier making this a    *
    * global variable than passing it as a parameter.                     *
    **********************************************************************/
   public static Vector procedures;

   /**********************************************************************
    * One of these booleans will be set true when we discover which       *
    * syntax is being used.                                               
    **********************************************************************/
   public static boolean pSyntax;
   public static boolean cSyntax;

   /**********************************************************************
    * This performs the initialization needed by the various Get...       *
    * methods, including setting charReader.  It is called only by        *
    * GetAlgorithm.  It's been made into a separate method for debugging, *
    * so the various Get methods can be tested without calling            *
    * GetAlgorithm.                                                       *
    **********************************************************************/
   public static void Init(PcalCharReader charR) 
   { 
    // initialization moved 
    addedLabels = new Vector(); 
    addedLabelsLocs = new Vector();
    nextLabelNum = 1;
    charReader = charR;
    allLabels = new Hashtable();       
    hasLabel = false;
    hasDefaultInitialization = false;
    currentProcedure = null;
    procedures = new Vector();
    
    pSyntax = false;
    cSyntax = false; 
    
    // The following initializations are redundant, but a little redundancy
    // never hurt.
    // The following initializations are redundant, but a little redundancy
    // never hurt.
    plusLabels = new Vector(0);
    minusLabels = new Vector(0);
    proceduresCalled = new Vector(0);
    
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
    if (PcalParams.inputVersionNumber < PcalParams.VersionToNumber("1.5")){
        omitPC = false; 
        omitStutteringWhenDone = false;
    }
    
   /******************************************************************
   * Initialize charReader.                                          *
   ******************************************************************/
    PcalBuiltInSymbols.Initialize();
  /*******************************************************************
  * Initializes the hash tables of class PcalBuiltInSymbols, which   *
  * is required before methods in the Tokenize class can be called.  *
      *******************************************************************/
    AST.ASTInit();
      /*******************************************************************
      * Performs the initialization method of the AST to create default  *
      * objects for each subclass.                                       *
      *******************************************************************/
   }

   
   public static AST getAlgorithm(PcalCharReader charR, boolean fairAlgorithm) throws ParseAlgorithmException
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
     { Init(charR) ;
       if (fairAlgorithm) {
    	   String nextToken = GetAlgToken() ;
    	   if (!nextToken.equals(PcalParams.BeginFairAlg2)) {
    		   ParsingError("`" + PcalParams.BeginFairAlg + "' not followed by `" 
    				   + PcalParams.BeginFairAlg2 + "'");
    	   }
    	   PcalParams.FairAlgorithm = true;    	   
       }
       String name = GetAlgToken() ;
       if (PeekAtAlgToken(1).equals("{"))
         { cSyntax = true ;
           MustGobbleThis("{") ; } 
       else {pSyntax = true ; } ;
       Vector vdecls = new Vector() ;
       if ( PeekAtAlgToken(1).equals("variable")
           || PeekAtAlgToken(1).equals("variables"))
         { vdecls = GetVarDecls() ; } ;
       TLAExpr defs = new TLAExpr() ;
       if (PeekAtAlgToken(1).equals("define"))
         { MustGobbleThis("define") ;
           if (cSyntax) {GobbleThis("{") ;} ;
           defs = GetExpr() ;
           if (pSyntax) 
             { GobbleThis("end") ;
               GobbleThis("define") ; }
           else
             { GobbleThis("}") ; } ;
           GobbleThis(";") ; 
         }
       Vector macros = new Vector() ;
       while (PeekAtAlgToken(1).equals("macro"))
         { macros.addElement(GetMacro(macros)) ; } ;
       while (PeekAtAlgToken(1).equals("procedure"))
         { procedures.addElement(GetProcedure()) ;
           // if there's a procedure, we assume that it's
           // called, so we must not omit the pc variable.
           omitPC = false;
         } ;
       if (     (   PeekAtAlgToken(1).equals("fair") 
                 && (   PeekAtAlgToken(2).equals("process")
                     || (   PeekAtAlgToken(2).equals("+")
                         && PeekAtAlgToken(3).equals("process")
                        )
                    )
                )
    		 || PeekAtAlgToken(1).equals("process")   )
         { AST.Multiprocess multiproc = new AST.Multiprocess() ;
           TLAtoPCalMapping map = PcalParams.tlaPcalMapping ;
           PCalLocation multiprocBegin = new PCalLocation(map.algLine, map.algColumn);
           multiproc.name   = name ;
           multiproc.decls  = vdecls ;
           multiproc.defs   = defs ;
           multiproc.macros = macros ;
           multiproc.prcds  = procedures ;
           multiproc.procs  = new Vector() ;
           while (PeekAtAlgToken(1).equals("fair") ||
        		   PeekAtAlgToken(1).equals("process"))
             { int fairness = AST.UNFAIR_PROC;
              if (PeekAtAlgToken(1).equals("fair")) {
        		   MustGobbleThis("fair");
        		   if (PeekAtAlgToken(1).equals("+")) {
        		       MustGobbleThis("+");
        		       fairness = AST.SF_PROC;
        		   } else {
        		   fairness = AST.WF_PROC;
        		   }
                } else 
                { if (PcalParams.FairnessOption.equals("wf")) {
                	fairness = AST.WF_PROC;
                    } else if (PcalParams.FairnessOption.equals("sf")) {
                    	fairness = AST.SF_PROC;
                    }
                };        	   
        	   AST.Process proc =  GetProcess() ;
        	   proc.fairness = fairness ;
        	   multiproc.procs.addElement(proc) ; 
             } ;
           if (pSyntax)
             { GobbleThis("end") ;
               GobbleThis("algorithm") ; }
           else { GobbleThis("}") ; } ;
           CheckForDuplicateMacros(multiproc.macros) ;
           int i = 0 ;
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
           while (i < multiproc.procs.size())
             { AST.Process proc = 
                   (AST.Process) multiproc.procs.elementAt(i);
               ExpandMacrosInStmtSeq(proc.body, multiproc.macros) ;
               AddLabelsToStmtSeq(proc.body) ;
               proc.body = MakeLabeledStmtSeq(proc.body);
               
               omitStutteringWhenDone = true;
               checkBody(proc.body);
               omitStutteringWhenDoneValue = 
                  omitStutteringWhenDoneValue || omitStutteringWhenDone;
               
               i = i + 1 ;
             } ;
           omitStutteringWhenDone = omitStutteringWhenDoneValue;
           i = 0 ;
           while (i < multiproc.prcds.size())
             { AST.Procedure prcd = 
                  (AST.Procedure) multiproc.prcds.elementAt(i) ;
               currentProcedure = prcd.name ;
               ExpandMacrosInStmtSeq(prcd.body, multiproc.macros);
               AddLabelsToStmtSeq(prcd.body);
               prcd.body = MakeLabeledStmtSeq(prcd.body);
               i = i + 1 ;
             }
           /****************************************************************
           * Check for added labels, report an error if there shouldn't    *
           * be any, and print them out if the -reportLabels was           *
           * specified.                                                    *
           ****************************************************************/
           if (addedLabels.size() > 0)
             { if (! PcalParams.LabelFlag) { AddedMessagesError() ; } ;
               if (PcalParams.ReportLabelsFlag) { ReportLabels() ; } 
               else
                   // SZ March 11, 2009: info reporting using PcalDebug added
                { PcalDebug.reportInfo("Labels added.") ; } ;
              } ;
           if (gotoDoneUsed) {
                  omitPC = false;
                  omitStutteringWhenDone = false;
              }
           if (gotoUsed) {
               omitPC = false;
           }
           multiproc.setOrigin(new Region(multiprocBegin, 
                   GetLastLocationEnd())) ;
           return multiproc ;
         }
       else
         { AST.Uniprocess uniproc = new AST.Uniprocess() ;
           TLAtoPCalMapping map = PcalParams.tlaPcalMapping ;
           PCalLocation uniprocBegin = new PCalLocation(map.algLine, map.algColumn);
           uniproc.name   = name ;
           uniproc.decls  = vdecls ;
           uniproc.defs  = defs ;
           uniproc.macros = macros ;
           uniproc.prcds  = procedures ;
           // Version 1.5 allowed "fair" to appear here
           // to specify fairness for a sequential algorithm
           if (PcalParams.inputVersionNumber == PcalParams.VersionToNumber("1.5")) {
        	   if (PeekAtAlgToken(1).equals("fair")) {
                   GobbleThis("fair");
                   if (PeekAtAlgToken(1).equals("+")) {
                       GobbleThis("+");
                   } 
                   PcalParams.FairnessOption = "wf";
                 }
           }
           
           // Following if statement added by LL on 5 Oct 2011
           // to fix bug in which --fair uniprocess algorithm
           // wasn't producing fairness condition.
           if (fairAlgorithm) {
        	   if (!PcalParams.FairnessOption.equals("") 
        		      && !PcalParams.FairnessOption.equals("wf")
        		      && !PcalParams.FairnessOption.equals("wfNext")) {
        		  PcalDebug.reportWarning("Option `" + PcalParams.FairnessOption + "' specified for --fair algorithm.");
        	   }
        	   PcalParams.FairnessOption = "wf";
           } ;
           
           GobbleBeginOrLeftBrace() ;
           uniproc.body = GetStmtSeq() ;
           CheckForDuplicateMacros(uniproc.macros) ;
           ExpandMacrosInStmtSeq(uniproc.body, uniproc.macros) ;
// LL comment added 11 Mar 2006.
// I moved the following to after processing the procedures
// so added labels are printed in correct order-- e.g., with 
// -reportLabels option 
//           AddLabelsToStmtSeq(uniproc.body) ;
//           uniproc.body = MakeLabeledStmtSeq(uniproc.body);
           int i = 0 ;
           while (i < uniproc.prcds.size())
             {  AST.Procedure prcd =
                  (AST.Procedure) uniproc.prcds.elementAt(i) ;
               currentProcedure = prcd.name ;
               ExpandMacrosInStmtSeq(prcd.body, uniproc.macros);
               AddLabelsToStmtSeq(prcd.body);
               prcd.body = MakeLabeledStmtSeq(prcd.body);
               i = i + 1 ;
             }
           if (cSyntax) 
             { GobbleThis("}") ; 
               GobbleThis("}") ; } 
           else 
             { GobbleThis("end") ;
               GobbleThis("algorithm") ;} ;
           AddLabelsToStmtSeq(uniproc.body) ;
           uniproc.body = MakeLabeledStmtSeq(uniproc.body);
           /****************************************************************
           * Check for added labels, report an error if there shouldn't    *
           * be any, and print them out if the -reportLabels was           *
           * specified.                                                    *
           ****************************************************************/
           if (addedLabels.size() > 0)
             { if (hasLabel && ! PcalParams.LabelFlag) 
                        { AddedMessagesError() ; } ;
               if (PcalParams.ReportLabelsFlag) { ReportLabels() ; } 
               else
                   // SZ March 11, 2009: info reporting using PcalDebug added
                { PcalDebug.reportInfo("Labels added.") ; } ;
              } ;
           
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
                             GetLastLocationEnd())) ;
           return uniproc ;
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
    * 
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
    * 
    * @param body
    */
   private static void checkBody(Vector body) {
       // The body should not be empty, so the following
       // test should be redundant.  But just in case the
       // error is being found elsewhere...
       if (body == null || (body.size() == 0)) {
           return;
       }
       if ((body.size() > 1) || 
               ! body.elementAt(0).getClass().equals(AST.LabeledStmtObj.getClass()) ){
           omitPC = false;
           omitStutteringWhenDone = false;
           return;
       } ;
       AST.LabeledStmt lblStmt = (AST.LabeledStmt) body.elementAt(0);
       if ( (lblStmt.stmts == null) || (lblStmt.stmts.size() == 0)) {
           // Again, this shouldn't happen.
           return;
       }
       if ((lblStmt.stmts.size() > 1) || 
               ! lblStmt.stmts.elementAt(0).getClass().equals(AST.WhileObj.getClass()) ){
           omitPC = false;
           omitStutteringWhenDone = false;
           return;
       } ;
       
       AST.While whileStmt = (AST.While) lblStmt.stmts.elementAt(0);
       Vector tokens = whileStmt.test.tokens;
       if (tokens.size() != 1) {
           omitPC = false;
           omitStutteringWhenDone = false;
           return;
       }
       Vector line = (Vector) tokens.elementAt(0);
       if (line.size() != 1) {
           omitPC = false;
           omitStutteringWhenDone = false;
           return;
       }
       TLAToken tok = (TLAToken) line.elementAt(0);
       if (! tok.string.equals("TRUE")) {
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
           Object obj = whileStmt.unlabDo.elementAt(i);
           // in the following test, I think the LabeledStmt test
           // is unnecessary, because there can only be a LabeledStmt
           // in a while statements unlabDo field if it is preceded by
           // a LabelIf or LabelEither
           if (obj.getClass().equals(AST.LabelIfObj.getClass()) ||
                   obj.getClass().equals(AST.LabelEitherObj.getClass()) ||
                   obj.getClass().equals(AST.LabeledStmtObj.getClass())                   
               ) {
               omitPC = false;
               return;
           }
       }
       return;
   }
   
   public static void AddedMessagesError() throws ParseAlgorithmException 
     { String msg = null ;
       if (addedLabels.size() > 1)
         {msg = "Missing labels at the following locations:" ;}
       else 
         {msg = "Missing label at the following location:" ;} ;
       int i = 0 ;
       while (i < addedLabels.size() )
        { msg = msg + "\n     " + ((String) addedLabelsLocs.elementAt(i)) ;
          i = i + 1 ;
        } ;
       throw new ParseAlgorithmException(msg) ;
       }

   public static void ReportLabels() 
   // SZ March 11, 2009: info reporting using PcalDebug added
     { if (addedLabels.size() > 1)
         {PcalDebug.reportInfo("The following labels were added:") ;}
       else          
         {PcalDebug.reportInfo("The following label was added:") ;} ;
       int i = 0 ;
       while (i < addedLabels.size() )
        { PcalDebug.reportInfo("  " 
              + ((String) addedLabels.elementAt(i)) 
              + " at "
              + ((String) addedLabelsLocs.elementAt(i)));
          i = i + 1 ;
        } ;
       return ; }

   public static AST.Procedure GetProcedure() throws ParseAlgorithmException
     { AST.Procedure result = new AST.Procedure() ;
       GobbleThis("procedure") ;
       PCalLocation beginLoc = GetLastLocationStart() ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       result.name = GetAlgToken() ;
       currentProcedure = result.name ;
       plusLabels = new Vector(0);
       minusLabels = new Vector(0);
       proceduresCalled = new Vector(0);
       GobbleThis("(") ;
       result.params = new Vector() ;
       boolean lookForComma = false ;
       while (! PeekAtAlgToken(1).equals(")"))
         { if (lookForComma)
             { GobbleThis(",") ; } ;
           result.params.addElement(GetPVarDecl()) ;
           lookForComma = true ;
         }
       MustGobbleThis(")") ;
       if (   PeekAtAlgToken(1).equals("begin")
           || PeekAtAlgToken(1).equals("{"))
         { result.decls = new Vector(1) ; }
       else
         { result.decls = GetPVarDecls() ; } ;
       GobbleBeginOrLeftBrace() ;
       result.body = GetStmtSeq() ;
       GobbleEndOrRightBrace("procedure") ;  
       PCalLocation endLoc = GetLastLocationEnd() ;
       if (PeekAtAlgToken(1).equals(";"))
         { String tok = GetAlgToken() ; } ;
//       CheckLabeledStmtSeq(result.body) ;
       currentProcedure = null ;
       result.plusLabels = plusLabels;
       result.minusLabels = minusLabels;
       result.proceduresCalled = proceduresCalled ;
       result.setOrigin(new Region(beginLoc, endLoc)) ;
       return result ;
     }

   public static AST.Process GetProcess() throws ParseAlgorithmException
     { AST.Process result = new AST.Process() ;
       GobbleThis("process") ;
       PCalLocation beginLoc = GetLastLocationStart() ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       if (cSyntax) { GobbleThis("(") ; } ;
       result.name = GetAlgToken() ;
       result.isEq = GobbleEqualOrIf() ;
       result.id   = GetExpr() ; 
       plusLabels = new Vector(0);
       minusLabels = new Vector(0);
       proceduresCalled = new Vector(0);
       if (cSyntax) { GobbleThis(")") ; } ;
       if (result.id.tokens.size()==0)
         { ParsingError("Empty process id at ") ;}
       if (   PeekAtAlgToken(1).equals("begin")
           || PeekAtAlgToken(1).equals("{"))
         { result.decls = new Vector(1) ; }
       else
         { result.decls = GetVarDecls() ; } ;
       GobbleBeginOrLeftBrace() ;
       result.body = GetStmtSeq() ;
       GobbleEndOrRightBrace("process") ;
       PCalLocation endLoc = GetLastLocationEnd() ;
       if (PeekAtAlgToken(1).equals(";"))
         { String tok = GetAlgToken() ; } ;
//       CheckLabeledStmtSeq(result.body) ;
       result.plusLabels = plusLabels;
       result.minusLabels = minusLabels;
       result.proceduresCalled = proceduresCalled;
       result.setOrigin(new Region(beginLoc, endLoc)) ;
       return result ;
     }

   public static Vector GetPVarDecls() throws ParseAlgorithmException
     /**********************************************************************
     * Parses a <PVarDecls> as a Vector of AST.PVarDecl objects.           *
     **********************************************************************/
     { String tok = PeekAtAlgToken(1) ;
       if ( tok.equals("variables"))
         { MustGobbleThis("variables") ; } 
       else 
         { GobbleThis("variable") ; } ;
       Vector result = new Vector() ;

       /********************************************************************
       * The <PVarDecls> nonterminal is terminated by a "begin"            *
       * (p-syntax) or "{" (c-syntax) for the procedure.                   *
       ********************************************************************/
       while (! (   PeekAtAlgToken(1).equals("begin")
                 || PeekAtAlgToken(1).equals("{") ) )
         { result.addElement(GetPVarDecl()) ;
           GobbleCommaOrSemicolon();
             /**************************************************************
             * Changed on 24 Mar 2006 from GobbleThis(";") to allow        *
             * declarations to be separated by commas.                     *
             **************************************************************/
          } ;
        return result ;
     }

   public static AST.PVarDecl GetPVarDecl() throws ParseAlgorithmException 
     { AST.PVarDecl pv = new AST.PVarDecl() ;
       pv.var = GetAlgToken() ;
       PCalLocation beginLoc = GetLastLocationStart() ;
       PCalLocation endLoc = GetLastLocationEnd() ;
       pv.col  = lastTokCol ;
       pv.line = lastTokLine ;
       if (PeekAtAlgToken(1).equals("="))       
         { GobbleThis("=") ;
           pv.val = GetExpr() ; 
           endLoc = pv.val.getOrigin().getEnd() ;
           if (pv.val.tokens.size()==0)
             { ParsingError("Missing expression at ") ;} ;
          } 
       else {hasDefaultInitialization = true ;} ; 
       pv.setOrigin(new Region(beginLoc, endLoc));
       return pv ;
     }

   public static Vector GetVarDecls() throws ParseAlgorithmException
     /**********************************************************************
     * Parses a <VarDecls> as a Vector of AST.VarDecl objects.             *
     **********************************************************************/
     { String tok = PeekAtAlgToken(1) ;
       if ( tok.equals("variables"))
         { MustGobbleThis("variables") ; } 
       else 
         { GobbleThis("variable") ; } ;
       Vector result = new Vector() ;

       /********************************************************************
       * The <VarDecls> nonterminal appears in two places:                 *
       *                                                                   *
       * - In a <Procedure> or <Process>, where it is terminated by        *
       *   a "begin" (p-syntax) or "{" (c-syntax).                         *
       *                                                                   *
       * - At the beginning of a <Algorithm>, where it is terminated by    *
       *   "define", "macro", "procedure", "begin" or "{", or "process" .  *
       ********************************************************************/
       while (! (   PeekAtAlgToken(1).equals("begin")
                 || PeekAtAlgToken(1).equals("{")
                 || PeekAtAlgToken(1).equals("procedure")
                 || PeekAtAlgToken(1).equals("process")  
                 || PeekAtAlgToken(1).equals("fair")  
                 || PeekAtAlgToken(1).equals("define")  
                 || PeekAtAlgToken(1).equals("macro")   ) )
         { result.addElement(GetVarDecl());
          } ;
        return result ;
     }

   public static AST.VarDecl GetVarDecl() throws ParseAlgorithmException 
     { AST.VarDecl pv = new AST.VarDecl() ;
       pv.var = GetAlgToken() ;
       PCalLocation beginLoc = GetLastLocationStart() ;
       PCalLocation endLoc = GetLastLocationEnd() ;
       pv.col  = lastTokCol ;
       pv.line = lastTokLine ;
       if (   PeekAtAlgToken(1).equals("=")
           || PeekAtAlgToken(1).equals("\\in"))
         { pv.isEq = GobbleEqualOrIf() ;
           pv.val = GetExpr() ; 
           endLoc = pv.val.getOrigin().getEnd() ;
           if (pv.val.tokens.size()==0)
             { ParsingError("Missing expression at ") ;} ;
         } 
       else {hasDefaultInitialization = true ;} ;

       GobbleCommaOrSemicolon();
         /******************************************************************
         * Changed on 24 Mar 2006 from GobbleThis(";") to allow            *
         * declarations to be separated by commas.                         *
         ******************************************************************/
       pv.setOrigin(new Region(beginLoc, endLoc));
       return pv ;
     }

   public static TLAExpr GetExpr() throws ParseAlgorithmException
     { if (LATsize != 0)
         {PcalDebug.ReportBug(
               "ParseAlgorithm: GetExpr called after lookahead");
         } ;
        TLAExpr result;
        try
        {
            result = Tokenize.TokenizeExpr(charReader);
        } catch (TokenizerException e)
        {
            throw new ParseAlgorithmException(e.getMessage());
        }
        LAT[LATsize] = Tokenize.Delimiter;
        curTokCol[LATsize]  = Tokenize.DelimiterCol;
        curTokLine[LATsize] = Tokenize.DelimiterLine;
        LATsize = LATsize + 1 ;
        
        /**
         * If the expression has any tokens, then set the origin to the
         * region comprising the tokens.  Otherwise, set the region to null.
         */
        if (result.tokens != null && result.tokens.size() != 0) {          
            PCalLocation begin = ((TLAToken) ((Vector)
                                result.tokens.elementAt(0))
                                .elementAt(0)).source.getBegin();
            Vector lastLineOfTokens = (Vector) result.tokens.elementAt(
                                           result.tokens.size()-1) ;
           if (lastLineOfTokens.size()==0) {
               Debug.ReportBug("Unexpected Event in ParseAlgorithm.GetExpr");
           }
 
           PCalLocation end =  ((TLAToken) lastLineOfTokens.elementAt(
                               lastLineOfTokens.size()-1)).source.getEnd();
           result.setOrigin(new Region(begin, end)) ;
        } else {
            result.setOrigin(null) ; 
        }
        return result ;
     }

   /* OBSOLETE */ public static Vector ObsoleteGetLabeledStmtSeq() throws ParseAlgorithmException
     /**********************************************************************
     * Returns a (possibly null) sequence of LabeledStmt elements.  This   *
     * is the obvious iterative call of GetLabeledStmt that stops when     *
     * it's not at a label.                                                *
     **********************************************************************/
     { Vector result = new Vector();
       while (IsLabelNext())
         { result.addElement(ObsoleteGetLabeledStmt()) ;
         } ;
       return result ; 
     }

   /* OBSOLETE */ public static AST.LabeledStmt ObsoleteGetLabeledStmt() throws ParseAlgorithmException
     { if (! IsLabelNext())
         { ParsingError("Was expecting a label"); 
         } ;
       AST.LabeledStmt result = new AST.LabeledStmt() ;
       result.label = GetAlgToken() ;
       if (result.label.equals("Done"))
         { ParsingError("Cannot use `Done' as a label.") ; } ;
       if (result.label.equals("Error"))
         { ParsingError("Cannot use `Error' as a label.") ; } ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       result.stmts = new Vector() ;
       GobbleThis(":") ;
       AST.While whileStmt = null ;
       if (PeekAtAlgToken(1).equals("while"))
         { result.stmts.addElement(GetWhile()) ; }
       Vector stmtSeq = GetStmtSeq() ;
       int i = 0 ;
       while (i < stmtSeq.size())
         { result.stmts.addElement(stmtSeq.elementAt(i)) ;
           i = i + 1;
         } ;
      if (result.stmts.size() == 0)
        { ParsingError("Label with no following statement") ; }
      return result ; 
     }


   public static AST.While GetWhile() throws ParseAlgorithmException
     { MustGobbleThis("while") ;
       PCalLocation beginLoc = GetLastLocationStart() ;
       AST.While result = new AST.While() ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       if (cSyntax) { GobbleThis("(") ; } ;
       result.test = GetExpr();
       if (cSyntax) { GobbleThis(")") ; } ;
       if (result.test.tokens.size()==0)
         { ParsingError("Empty while test at ") ;} ;
       if (pSyntax)
         { GobbleThis("do") ;
           result.unlabDo = GetStmtSeq() ;
           GobbleThis("end") ;
           GobbleThis("while") ;
           GobbleThis(";") ;
         }
       else
         { result.unlabDo = GetCStmt() ; } ;
       result.labDo = new Vector() ;
         /******************************************************************
         * For historical reasons, some methods expect a labDo field to    *
         * contain a vector, even though they are called before the real   *
         * labDo field is created.                                         *
         ******************************************************************/
       result.setOrigin(new Region(beginLoc,
             ((AST) result.unlabDo.elementAt(result.unlabDo.size()-1))
                .getOrigin().getEnd())) ;
       return result ; }

  public static boolean inGetMacro = false ;
    /***********************************************************************
    * This boolean equals true while inside a call to GetMacro.  It is used to  
    * flag an error if a label appears within a macro.                     
     * @throws ParseAlgorithmException *
    ***********************************************************************/

   /**
    * This variable is used by GetLabel to return the location of the label
    * for use in computing the origin field of the AST object in which the
    * label appears.  If GetLabel returns a string other than "", then 
    * getLabelLocation is the location at the beginning of the label.
    */
   public static PCalLocation getLabelLocation;
   
   public static String GetLabel() throws ParseAlgorithmException 
     /**********************************************************************
     * Checks if a label comes next.  If so, it gobbles it and returns     *
     * the label.  Otherwise, it returns "".                               *
     **********************************************************************/
     { String nextLabel = "" ;
       if (IsLabelNext())
         { nextLabel = GetAlgToken() ;
           getLabelLocation = new PCalLocation(lastTokLine-1, lastTokCol-1);
           if (inGetMacro)
                 { ParsingError("A label may not appear in a macro.") ; } ;
           if (nextLabel.equals("Done"))
                 { ParsingError("Cannot use `Done' as a label.") ; } ;
           if (nextLabel.equals("Error"))
                 { ParsingError("Cannot use `Error' as a label.") ; } ;
           GobbleThis(":") ;
           hasLabel = true ;
           allLabels.put(nextLabel, "") ;
           // The following code added by LL on 12 Jan 2011 as part of
           // implementation of the fairness modifiers on labels introduced
           // in Version 1.5.
           // Modified by LL on 20 Mar 2011 to set omitPC false if there's
           // a + or - modifier, since this modifier creates a reference
           // to the label in the fairness condition.
           if (PeekAtAlgToken(1).equals("+")) {
        	   GobbleThis("+") ;
        	   plusLabels.addElement(nextLabel) ;
        	   omitPC = false;
           } else {
        	  if (PeekAtAlgToken(1).equals("-")) {
        		  GobbleThis("-") ;
           	      minusLabels.addElement(nextLabel) ; 
                  omitPC = false;
        	  }
           }
         } ;
       return nextLabel;
     }     

   public static Vector GetStmtSeq() throws ParseAlgorithmException 
     /**********************************************************************
     * Parses a sequence of <Stmt>s and returns the result as a Vector of  *
     * <Stmt> nodes.  It detects the end of the sequence by the            *
     * appearance of one of the following tokens                           *
     *                                                                     *
     *   end   else   elsif   or                                           *
     *                                                                     *
     * in the p-syntax or "}" in the c-syntax.                             *
     **********************************************************************/
     { Vector result = new Vector() ;
       String tok = PeekAtAlgToken(1) ;
       while (! (    (    pSyntax
                      && (   tok.equals("end")
                          || tok.equals("else")
                          || tok.equals("elsif")
                          || tok.equals("or")     ))
                  || ( cSyntax && tok.equals("}")) ))
         { String nextLabel = GetLabel() ;
           PCalLocation labelLoc = getLabelLocation ;
           if (cSyntax && PeekAtAlgToken(1).equals("{"))
             { /************************************************************
               * We're using c-syntax and the next statement is a          *
               * StmtSeq.                                                  *
               ************************************************************/
               result.addAll(GetCStmtSeq(nextLabel)) ;
             } 
           else
             { /************************************************************
               * This is an ordinary statement.                            *
               ************************************************************/
               AST stmt = GetStmt() ;
               stmt.lbl = nextLabel ;
               stmt.lblLocation = labelLoc ;
               result.addElement(stmt) ;
             } ;
           tok = PeekAtAlgToken(1) ;
         } ;
        if (cSyntax && (result.size() == 0))
          /*****************************************************************
          * I'm not sure if GetStmtSeq should be able to return an empty   *
          * sequence in p-syntax, but it definitely shouldn't in c-syntax  *
          * (I think).                                                     *
          *****************************************************************/
          { ParsingError("Empty statement list") ; }
        return result ;
      }


   public static AST GetStmt() throws ParseAlgorithmException
     { String nextTok = PeekAtAlgToken(1) ;
       if (nextTok.equals("if"))     { return GetIf(0) ; }     ;
       if (nextTok.equals("either")) { return GetEither() ; }     ;
       if (nextTok.equals("with"))   { return GetWith(0) ; }   ;
       if (nextTok.equals("when"))   { return GetWhen(true) ; }   ;
       if (nextTok.equals("await"))  { return GetWhen(false) ; }   ;
       if (nextTok.equals("print"))  { return GetPrintS() ; } ;
       if (nextTok.equals("assert")) { return GetAssert() ; } ;
       if (nextTok.equals("skip"))   { return GetSkip() ; }   ;
       if (nextTok.equals("call"))   { return GetCallOrCallReturn() ; }   ;
       if (nextTok.equals("return")) { return GetReturn() ; }   ;
       if (nextTok.equals("goto"))   { return GetGoto() ; }   ;
       if (nextTok.equals("while"))  { return GetWhile() ; } ;
       if (PeekPastAlgToken(1).charAt(0)=='(')
         { return GetMacroCall() ; }
       return GetAssign() ;
     }

   public static Vector GetCStmtSeq(String lbl) throws ParseAlgorithmException 
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
	   PCalLocation lblLocation = getLabelLocation ;
	   MustGobbleThis("{") ;
       Vector sseq = GetStmtSeq() ;
       GobbleThis("}") ;
       GobbleThis(";") ;
       if (! lbl.equals(""))
         { /********************************************************
           * There entire StmtSeq is labeled.                      *
           ********************************************************/
           if ( ! ((AST) sseq.elementAt(0)).lbl.equals(""))
             { throw new ParseAlgorithmException("Duplicate labeling of statement",
                                        (AST) sseq.elementAt(0)) ; };
            AST firstStmt = (AST) sseq.elementAt(0) ;
            firstStmt.lbl = lbl ;
            firstStmt.lblLocation = lblLocation ;
        } ;
      return sseq ;
     }     

   public static Vector GetCStmt() throws ParseAlgorithmException
     /**********************************************************************
     * Get one (possibly labeled) statement in the c-syntax, which could   *
     * be a StmtSeq, so this returns a vector of AST nodes.                *
     **********************************************************************/
     { String label = GetLabel() ;
       PCalLocation labelLocation = getLabelLocation ;
       if (PeekAtAlgToken(1).equals("{"))
         { return GetCStmtSeq(label) ; } ;
       AST stmt = GetStmt() ;
       stmt.lbl = label ;
       stmt.lblLocation = labelLocation ;
       Vector result = new Vector() ;
       result.addElement(stmt) ;       
       return result ;
     }     

   public static boolean IsLabelNext() throws ParseAlgorithmException 
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
     { String tok = PeekAtAlgToken(1) ;
       if (   (tok.equals("while"))
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
          )
         {return false ;} ;
        tok = charReader.peek() ;
        if (   (tok.length() == 0) // I don't think this can happen.
            || (tok.charAt(0) != ':')
            || (   (tok.length() > 1)
                && (tok.charAt(1) == '='))
           )
          {return false ;} ;
        return true;
     }


   public static AST.LabelIf  GetIf(int depth) throws ParseAlgorithmException
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
     { if (depth == 0)
         { MustGobbleThis("if") ; }
       else 
         { MustGobbleThis("elsif") ; } ;
       PCalLocation beginLoc = GetLastLocationStart() ;
       AST.LabelIf result = new AST.LabelIf() ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       if (cSyntax) { GobbleThis("(") ; } ; 
       result.test = GetExpr() ;
       if (cSyntax) { GobbleThis(")") ; } ; 
       if (result.test.tokens.size() == 0)
         { ParsingError("Empty if test at ") ;} ;
       if (pSyntax)
         { GobbleThis("then") ;
           result.unlabThen = GetStmtSeq() ;}
       else
         { result.unlabThen = GetCStmt() ; } ;
       String nextTok = PeekAtAlgToken(1) ;
       if (pSyntax)
         { if (nextTok.equals("else"))
            { MustGobbleThis("else") ;
              result.unlabElse = GetStmtSeq() ;
            }
           else if (nextTok.equals("elsif"))
                 { AST.LabelIf innerIf = GetIf(depth + 1) ;
                   result.unlabElse = new Vector() ;
                   result.unlabElse.addElement(innerIf) ;
                 }
           else if (nextTok.equals("end")) 
                 { result.unlabElse = new Vector() ; 
                 }
            else { ParsingError(
                     "Expecting \"else\", \"elsif\", or \"end\"")  ; } ;
            if (depth == 0)
              { GobbleThis("end") ; 
                GobbleThis("if") ; 
                GobbleThis(";");  ;
              } ;
         }         
       else /* c syntax */
         { if (nextTok.equals("else"))
            { MustGobbleThis("else") ;
              result.unlabElse = GetCStmt() ;
            } 
           else
            { result.unlabElse = new Vector() ; }
         } ;
       result.labThen = new Vector() ; 
       result.labElse = new Vector() ; 

       /**
        * Set lastStmt to the AST node of the last statement in the
        * if, which is either at the end of the end clause or, if there is none,
        * at the end of the then clause.
        */
       AST lastStmt = null ;
       if (result.unlabElse.size() != 0) {
    	   lastStmt = (AST) result.unlabElse.elementAt(result.unlabElse.size()-1) ;
       }
       else {
    	   lastStmt = (AST) result.unlabThen.elementAt(result.unlabThen.size()-1);
       }
       
       /**
        * Set the LabelIf's origin to the region from the beginning of the "if"
        * to the end of the last then or else statement. 
        */
       result.setOrigin(new Region (beginLoc, lastStmt.getOrigin().getEnd())) ;
       return result ;
     }  

   public static AST.LabelEither  GetEither() throws ParseAlgorithmException
     { MustGobbleThis("either") ;
       PCalLocation beginLoc = GetLastLocationStart() ;
       AST.LabelEither result = new AST.LabelEither() ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       result.clauses = new Vector() ;
       boolean done = false ;
       boolean hasOr = false ;
       while (! done)
        { AST.Clause nextClause = new AST.Clause() ;
          nextClause.labOr = new Vector() ;
          if (pSyntax)
            { nextClause.unlabOr = GetStmtSeq() ; }
          else
            { nextClause.unlabOr = GetCStmt() ; }
          if (nextClause.unlabOr.size() == 0)
            {throw new ParseAlgorithmException(
                "`either' statement with empty `or' clause", result) ; } ;
          nextClause.setOrigin(new Region(
                  ((AST) nextClause.unlabOr.elementAt(0)).getOrigin().getBegin(), 
                  ((AST) nextClause.unlabOr.elementAt(nextClause.unlabOr.size()-1))
                         .getOrigin().getEnd())) ; 
          result.clauses.addElement(nextClause) ;
          String nextTok = PeekAtAlgToken(1) ;
          if (nextTok.equals("or"))
            { MustGobbleThis("or") ; 
              hasOr = true ;
            }
          else
            { done = true ; }
        } ;
        if (pSyntax)
          { MustGobbleThis("end") ;
            GobbleThis("either") ;
            GobbleThis(";") ;
          } ;
        if (! hasOr) 
          { throw new ParseAlgorithmException("`either' statement has no `or'", result) ;
          } ;
        result.setOrigin(new Region(beginLoc,
                  ((AST) result.clauses.elementAt(result.clauses.size()-1))
                     .getOrigin().getEnd())) ;
        return result ;
     }

   /**
    * For constructing the TLA+ to PlusCal mapping, the original GetWith
    * procedure was given a second argument and was renamed InnerGetWidth.
    * See the comments for that method
    *  
    * @param depth
    * @return
    * @throws ParseAlgorithmException
    */
   public static AST GetWith(int depth) throws ParseAlgorithmException {
       return InnerGetWith(depth, null) ;
   }
   public static AST InnerGetWith(int depth, PCalLocation beginLoc) throws ParseAlgorithmException
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
       PCalLocation begLoc = beginLoc ;
       if (depth == 0)
         { GobbleThis("with") ;
           begLoc = GetLastLocationStart() ;
           if (cSyntax) { GobbleThis("(") ; } ;
         } ;
       AST.With result = new AST.With() ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       result.var  = GetAlgToken() ;
       result.isEq = GobbleEqualOrIf() ;
       result.exp  = GetExpr() ;
       if (pSyntax || ! PeekAtAlgToken(1).equals(")"))
         { GobbleCommaOrSemicolon();
             /**************************************************************
             * Gobble the ";" or "," ending the <VarEqOrIn>, which may be  *
             * eliminated before a ")" or "do".                            *
             **************************************************************/
         } ;
       if (result.exp.tokens.size() == 0)
         { ParsingError("Empty with expression at ") ;} ;
       if (pSyntax && PeekAtAlgToken(1).equals("do"))
         { GobbleThis("do") ;
           result.Do   = GetStmtSeq() ;
           GobbleThis("end") ;
           GobbleThis("with") ;
           GobbleThis(";"); 
         }
       else if (cSyntax && PeekAtAlgToken(1).equals(")"))
         { MustGobbleThis(")") ;
           result.Do = GetCStmt() ;
         }
       else 
         { result.Do = new Vector() ;
           result.Do.addElement(InnerGetWith(depth+1, begLoc)) ;
         };
       result.setOrigin(new Region(begLoc, 
           ((AST) result.Do.elementAt(result.Do.size()-1)).getOrigin().getEnd())) ;
       return result ;
     } 

   public static AST.Assign GetAssign() throws ParseAlgorithmException
     { AST.Assign result = new AST.Assign() ;
       result.col  = curTokCol[0]  + 1;
       result.line = curTokLine[0] + 1;
         /******************************************************************
         * We use the fact here that this method is called after           *
         * PeekAtAlgToken(1), so LAT[0] contains the next token.           *
         ******************************************************************/
       result.ass = new Vector() ;
       result.ass.addElement(GetSingleAssign()) ;
       while (PeekAtAlgToken(1).equals("||"))
         { String throwAway = GetAlgToken() ;
           try {
           result.ass.addElement(GetSingleAssign()) ;
           } catch (ParseAlgorithmException e) {
           ParsingError("Bad assignment statement at ") ;
        }
         } ;
       GobbleThis(";") ; 
       AST firstAssign = (AST) result.ass.elementAt(0) ;
       AST lastAssign = (AST) result.ass.elementAt(result.ass.size()-1) ;
       result.setOrigin(new Region(firstAssign.getOrigin().getBegin(), 
                                   lastAssign.getOrigin().getEnd()));
       return result ;
     }

   public static AST.SingleAssign GetSingleAssign() throws ParseAlgorithmException
     { AST.SingleAssign result = new AST.SingleAssign() ;
       result.col  = curTokCol[0]  + 1;
       result.line = curTokLine[0] + 1;
         /******************************************************************
         * We use the fact here that this method is called after           *
         * PeekAtAlgToken(1), so LAT[0] contains the next token.           *
         ******************************************************************/
       result.lhs = GetLhs() ;
       GobbleThis(":=") ; 
       result.rhs = GetExpr() ;
       if (result.rhs.tokens.size() == 0)
         { ParsingError("Empty right-hand side of assignment at ") ;} ;
       result.setOrigin(new Region(result.lhs.getOrigin().getBegin(), 
               result.rhs.getOrigin().getEnd()));
       return result ;
     }

   public static AST.Lhs GetLhs() throws ParseAlgorithmException 
     { AST.Lhs result = new AST.Lhs() ;
       result.col  = curTokCol[0]  + 1;
       result.line = curTokLine[0] + 1;
         /******************************************************************
         * We use the fact here that this method is called after           *
         * PeekAtAlgToken(1), so LAT[0] contains the next token.           *
         ******************************************************************/
       PCalLocation beginLoc = null ;
       PCalLocation endLoc = null ;
       try
    {
        result.var = GetAlgToken() ;
        
        /**
         * beginning of LHS's region is the beginning of the variable.  Its
         * end is the end of the subscript expression, if there is one, else
         * the end of the variable token.
         */
        beginLoc = GetLastLocationStart() ;
        endLoc = GetLastLocationEnd() ;
        
        result.sub = GetExpr() ; 
    } catch (ParseAlgorithmException e)
    {
        throw new ParseAlgorithmException(e.getMessage());
    }  
       if (result.sub.getOrigin() != null) {
           endLoc = result.sub.getOrigin().getEnd() ;
       }
       result.setOrigin(new Region(beginLoc, endLoc));
       return result ;
     }

   public static AST.PrintS GetPrintS() throws ParseAlgorithmException 
     { MustGobbleThis("print") ;    
       PCalLocation beginLoc = GetLastLocationStart() ;
       AST.PrintS result = new AST.PrintS() ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       result.exp = GetExpr() ; 
       if (result.exp.tokens.size() == 0)
         { ParsingError("Empty expression in print statement at ") ;} ;
       result.setOrigin(new Region(beginLoc, result.exp.getOrigin().getEnd())) ;
       GobbleThis(";") ;
       return result ;
     }

   public static AST.Assert GetAssert() throws ParseAlgorithmException 
     { AST.Assert result = new AST.Assert() ;
       MustGobbleThis("assert") ;       
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       result.exp = GetExpr() ; 
       if (result.exp.tokens.size() == 0)
         { ParsingError("Empty expression in assert statement at ") ;} ;
       GobbleThis(";") ;
       result.setOrigin(new Region(new PCalLocation(
    		   result.line-1, result.col-1),
    		   result.exp.getOrigin().getEnd())) ;
       return result ;
     }

   public static AST.Skip GetSkip() throws ParseAlgorithmException 
     { AST.Skip result = new AST.Skip() ;
       MustGobbleThis("skip") ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       result.setOrigin(new Region(lastTokLine-1, lastTokCol-1, 4));
       GobbleThis(";") ;
       return result ;
     }

   public static AST.When GetWhen(boolean isWhen) throws ParseAlgorithmException 
     /**********************************************************************
     * Called with isWhen = true for a "when"                              *
     *                    = false for an "await"                           *
     **********************************************************************/
     { AST.When result = new AST.When() ;
       if (isWhen) {MustGobbleThis("when") ;} 
        else {MustGobbleThis("await") ;} ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;       
       result.exp = GetExpr() ; 
       result.setOrigin(new Region(new PCalLocation(
    		   result.line-1, result.col-1),
    		   result.exp.getOrigin().getEnd())) ;
       if (result.exp.tokens.size() == 0)
         { ParsingError("Empty expression in when statement at ") ;} ;
       GobbleThis(";") ; 
       return result ;
     }

   public static AST.Call GetCall() throws ParseAlgorithmException 
     { MustGobbleThis("call") ;
       AST.Call result = new AST.Call() ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       result.to = GetAlgToken() ;
       GobbleThis("(") ;
       result.args = new Vector() ;
       boolean moreArgs = (PeekPastAlgToken(0).charAt(0) != ')') ;
       while (moreArgs)
         { result.args.addElement(GetExpr()) ;
           if ( ((TLAExpr) result.args.lastElement()).tokens.size() == 0)
              { ParsingError("Empty argument in call statement at ") ;} ;
           if ( ! PeekAtAlgToken(1).equals(")") )
              { GobbleThis(",") ; } 
           else
              { moreArgs = false ; } ;
          } ;
       GobbleThis(")") ;
       result.setOrigin(new Region(new PCalLocation(result.line-1, result.col-1),
    		   new PCalLocation(lastTokLine-1, lastTokCol))) ;
                           // token ")" has width 1.
       GobbleThis(";") ;
       /*
        * Add the called procedure's name to proceduresCalled if it
        * is not already in it.
        */
       int i = 0 ;
       while (    (i < proceduresCalled.size()) 
    		   && ! result.to.equals(proceduresCalled.elementAt(i))) {
    	   i++ ;
       };
       if (i == proceduresCalled.size()) {
    	   proceduresCalled.addElement(result.to);
       }
       return result ;
     }

   public static AST.Return GetReturn() throws ParseAlgorithmException 
     /**********************************************************************
     * Note: GetReturn should not complain if the return is not inside a   *
     * procedure because it could be in a macro that is called only from   *
     * inside a procedure.                                                 *
     **********************************************************************/
     { AST.Return result = new AST.Return() ;
       MustGobbleThis("return") ;
       result.setOrigin(new Region(GetLastLocationStart(), GetLastLocationEnd())); 
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       result.from = currentProcedure ;
       result.setOrigin(new Region(lastTokLine-1, lastTokCol-1, 6));
       GobbleThis(";") ;
       return result ;
     }

   public static AST GetCallOrCallReturn() throws ParseAlgorithmException 
     /**********************************************************************
     * Note: should not complain if it finds a return that is not inside   *
     * a procedure because it could be in a macro that is called only      *
     * from inside a procedure.                                            *
     **********************************************************************/
     { AST.Call theCall = GetCall() ;
       if (PeekAtAlgToken(1).equals("return"))
         { MustGobbleThis("return") ;
           PCalLocation end = new PCalLocation(lastTokLine-1, lastTokCol+5);
           GobbleThis(";") ;
           AST.CallReturn result = new AST.CallReturn();
           result.col  = theCall.col ;
           result.line = theCall.line ;
           result.to   = theCall.to ;
           result.from = currentProcedure ;
           result.args = theCall.args ;
           result.setOrigin(new Region(theCall.getOrigin().getBegin(), end)) ;
           return result ;
         }
       else 
         { return theCall; }
     }

   public static AST.Goto GetGoto() throws ParseAlgorithmException 
     { MustGobbleThis("goto") ;
       AST.Goto result = new AST.Goto() ;
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       result.to   = GetAlgToken() ;
       result.setOrigin(new Region(new PCalLocation(result.line-1, result.col-1),
    		          new PCalLocation(lastTokLine-1, lastTokCol-1+result.to.length()))) ;
       gotoUsed = true ;
       // The translator accepts `goto "Done"' and treats it like
       // `goto Done'.  Testing reveals that the outer
       // parentheses seem to be removed before we get here, but I
       // don't trust my tests, so let's check for both.
       if (result.to.equals("Done") || result.to.equals("\"Done\"")) {
           gotoDoneUsed = true;
       }
       GobbleThis(";") ;
       return result ;
     }

//   public static AST.Macro ObsoleteGetMacro() throws ParseAlgorithmException 
//     /**********************************************************************
//     * This method was largely copied from GetProcedure.                   *
//     **********************************************************************/
//     { AST.Macro result = new AST.Macro() ;
//       inGetMacro = true ;
//       MustGobbleThis("macro") ;
//       result.col  = lastTokCol ;
//       result.line = lastTokLine ;
//       result.name = GetAlgToken() ;
//       GobbleThis("(") ;
//       result.params = new Vector() ;
//       boolean lookForComma = false ;
//       while (! PeekAtAlgToken(1).equals(")"))
//         { if (lookForComma)
//             { GobbleThis(",") ; } ;
//           result.params.addElement(GetAlgToken()) ;
//           lookForComma = true ;
//         }
//       MustGobbleThis(")") ;
//       GobbleBeginOrLeftBrace() ; ;
//       result.body = GetStmtSeq() ;
//       GobbleEndOrRightBrace("macro") ;
//       if (PeekAtAlgToken(1).equals(";"))
//         { String tok = GetAlgToken() ; } ;
//
//       ExpandMacrosInStmtSeq(result.body, new Vector()) ;
//         /******************************************************************
//         * This is a quick and dirty way to produce an error if the macro  *
//         * body contains a macro call.  It's a trifle inelegant to         *
//         * produce the same error message for a call of a nonexistent      *
//         * macro as for a macro call within a macro, but the user will     *
//         * have no problem figuring out which it is.                       *
//         ******************************************************************/
//       inGetMacro = false ;
//       return result ;
//     }

   /**
    *  GetMacro changed by LL on 14 July 2011 to take the vector of macros
    *  as an argument that it passes to ExpandMacrosInStmtSeq.  (Previously,
    *  it had passed an empty vector.)  This allows macros to be called inside
    *  previously declared macros.  I don't remember why this wasn't done
    *  originally, instead of not allowing macros to be called inside macros.
    *  I'm afraid that there was a reason that will appear later.  For that reason,
    *  the original GetMacro procedure is contained in the comments above.  To
    *  back out of this change, just remove the argument from the one call
    *  of GetMacro, and change the error message generated in
    *  ExpandMacroCall.
    */
   public static AST.Macro GetMacro(Vector macros) throws ParseAlgorithmException 
   /**********************************************************************
   * This method was largely copied from GetProcedure.                   *
   **********************************************************************/
   { AST.Macro result = new AST.Macro() ;
     inGetMacro = true ;
     MustGobbleThis("macro") ;
     PCalLocation beginLoc = GetLastLocationStart() ;
     result.col  = lastTokCol ;
     result.line = lastTokLine ;
     result.name = GetAlgToken() ;
     GobbleThis("(") ;
     result.params = new Vector() ;
     boolean lookForComma = false ;
     while (! PeekAtAlgToken(1).equals(")"))
       { if (lookForComma)
           { GobbleThis(",") ; } ;
         result.params.addElement(GetAlgToken()) ;
         lookForComma = true ;
       }
     MustGobbleThis(")") ;
     GobbleBeginOrLeftBrace() ; ;
     result.body = GetStmtSeq() ;
     GobbleEndOrRightBrace("macro") ;
     result.setOrigin(new Region(beginLoc, GetLastLocationEnd())) ;
     if (PeekAtAlgToken(1).equals(";"))
       { String tok = GetAlgToken() ; } ;

     ExpandMacrosInStmtSeq(result.body, macros) ;
     
     inGetMacro = false ;
     return result ;
   }
   
   public static AST.MacroCall GetMacroCall() throws ParseAlgorithmException 
     { AST.MacroCall result = new AST.MacroCall() ;
       result.name = GetAlgToken() ;
       PCalLocation beginLoc = GetLastLocationStart();
       result.col  = lastTokCol ;
       result.line = lastTokLine ;
       MustGobbleThis("(") ;
       result.args = new Vector() ;
       boolean moreArgs = (PeekPastAlgToken(0).charAt(0) != ')') ;
       while (moreArgs)
         { result.args.addElement(GetExpr()) ;
           if ( ((TLAExpr) result.args.lastElement()).tokens.size() == 0)
              { ParsingError("Empty argument in call statement at ") ;} ;
           if ( ! PeekAtAlgToken(1).equals(")") )
              { GobbleThis(",") ; } 
           else
              { moreArgs = false ; } ;
          } ;
       GobbleThis(")") ;
       result.setOrigin(new Region(beginLoc, GetLastLocationEnd())) ;
       GobbleThis(";") ;
       return result ;
     }

/***************************************************************************
*                          NEW METHODS ADDED Mar 2006                      
* @throws ParseAlgorithmException *
***************************************************************************/

   public static void AddLabelsToStmtSeq(Vector stmtseq) throws ParseAlgorithmException 
     { InnerAddLabels(stmtseq,
                      true,            // firstLabeled
                      false,           // inWith
                      new Vector(),    // inAssigned = {}
                      new Vector() );  // outAssigned
       return ;
     }

/***************************************************************************
* InnerAddLabels is the recursive procedure used to perform the work of    *
* AddLabelsToStmtSeq.  It returns the value false if the new value of      *
* stmtseq has no call or return statements and no labels; otherwise it     *
* returns true.  The return value generally indicates if the calling       *
* procedure needs to add a label to some following statement.              * 
*                                                                          *
***************************************************************************/
   public static boolean InnerAddLabels(
     Vector stmtseq, 
       /********************************************************************
       * The sequence of statements to which labels are to be added.       *
       ********************************************************************/
     boolean firstLabeled,
       /********************************************************************
       * True iff the first statement of the sequence needs a label.       *
       ********************************************************************/
     boolean inWith,
       /********************************************************************
       * True iff stmtseq occurs within a `with' statement.                *
       ********************************************************************/
     Vector inAssigned, 
       /********************************************************************
       * The set of variables to which assignments have been made in the   *
       * current step before executing stmtseq.  When calling              *
       * InnerAddLabels for an outermost `with', this will be set to the   *
       * empty set.                                                        *
       ********************************************************************/
     Vector outAssigned) throws ParseAlgorithmException
       /********************************************************************
       * This is a call-by-reference argument used to return the set of    *
       * variables to which values have been assigned in the current step  *
       * upon completing this sequence of statements.  It need not be a    *
       * superset of vlbsAssigned if there could be a label inside         *
       * stmtseq that starts a new step--which is the case if inWith =     *
       * false.                                                            *
       ********************************************************************/
     { int i = 0 ;


       /********************************************************************
       * Initialize outAssigned, outWithAssigned                           *
       ********************************************************************/
       Copy(inAssigned, outAssigned) ;

       boolean nextStepNeedsLabel = firstLabeled ;
         /******************************************************************
         * True iff the next step requires a label--e.g., because the      *
         * previous step is a return or an if containing a label.  It is   *
         * also the value returned by the entire procedure.                *
         ******************************************************************/

       boolean hadOrAddedLabel = false ;
         /******************************************************************
         * True iff a label has been found or added somewhere inside       *
         * stmtseq.                                                        *
         ******************************************************************/
         
       while (i < stmtseq.size())
         { AST stmt = (AST) stmtseq.elementAt(i) ;
           if (! stmt.lbl.equals(""))
             { hadOrAddedLabel = true ;
               outAssigned.removeAllElements() ;
               if (inWith) 
                 { throw new ParseAlgorithmException("Label in `with' statement", 
                                           stmt) ;
                 } ;
             } ;
           if (nextStepNeedsLabel)
            { if (inWith) 
                { throw new ParseAlgorithmException(
                    "Statement follows `call' or `return' inside a " +
                      "`with' statement.",
                     stmt) ;
                } ;

              NeedsLabel((AST) stmtseq.elementAt(i)) ;
                  nextStepNeedsLabel = false ;
              hadOrAddedLabel = true   ;
              outAssigned.removeAllElements() ;
                /***********************************************************
                * outAssigned := {}                                        *
                ***********************************************************/
            } ; 
          if (stmt.getClass().equals(AST.LabelIfObj.getClass()))
             { /************************************************************
               * This is an if statement.                                  *
               *   - Call InnerAddLabels on the the unlabThen and          *
               *     unlabElse fields.                                     *
               *   - Set outAssigned to the union of the values            *
               *     returned by the two calls.                            *
               *   - Set nextStepNeedsLabel to true iff either call        *
               *     returns true.                                         *
               ************************************************************/
               AST.LabelIf obj = (AST.LabelIf) stmt ;
                 /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
               Vector thenAssigned     = new Vector() ;
               Vector elseAssigned     = new Vector() ;
// System.out.println("If at " + stmt.location()) ;
// PcalDebug.printVector(outAssigned, "pre outAssigned") ;
// PcalDebug.printVector(inAssigned, "pre inAssigned") ;
               nextStepNeedsLabel =
                 InnerAddLabels(obj.unlabThen,  
                                false,             // firstLabeled
                                inWith,            // inWith
                                outAssigned,       // inAssigned = {}
                                thenAssigned) ;    // outAssigned
               nextStepNeedsLabel = 
                 InnerAddLabels(obj.unlabElse,  
                                false,             // firstLabeled
                                inWith,            // inWith
                                outAssigned,       // inAssigned = {}
                                elseAssigned)      // outAssigned
                 || nextStepNeedsLabel ;
// PcalDebug.printVector(outAssigned, "mid outAssigned") ;
              Copy(Union(thenAssigned, elseAssigned), outAssigned ) ;
// PcalDebug.printVector(outAssigned, "pst outAssigned") ;
              }
           else if (stmt.getClass().equals(AST.LabelEitherObj.getClass()))
             { /************************************************************
               * This is a LabelEither object.  The sequence of its        *
               * clauses' unlabOr fields are handled in much the same way  *
               * as unlabThen and unlabElse fields for a LabelIf object.   *
               ************************************************************/
               AST.LabelEither obj = (AST.LabelEither) stmt ;
                 /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
               int j = 0 ;
               Vector newOutAssigned = new Vector() ;
               Vector newOutWithAssigned = new Vector() ;

               while (j < obj.clauses.size())
                 { AST.Clause clause = (AST.Clause) obj.clauses.elementAt(j) ;
                   Vector orAssigned     = new Vector() ;
                   Vector orWithAssigned = new Vector() ;
                   nextStepNeedsLabel =
                     InnerAddLabels(clause.unlabOr,  
                                    false,             // firstLabeled
                                    inWith,            // inWith
                                    outAssigned,       // inAssigned = {}
                                    orAssigned)        // outAssigned
                     || nextStepNeedsLabel ;
                   Copy(Union(orAssigned, newOutAssigned), newOutAssigned) ;
                   j = j+1 ;
                 };               
               Copy(newOutAssigned, outAssigned) ;
             }
           else if (stmt.getClass().equals(AST.WhileObj.getClass()))
             { /************************************************************
               * This is a while statement.                                *
               *   - Add a label if needed and clear outAssigned.          *
               *   - Call InnerAddLabels on the unlabDo clause.            *
               *   - set nextStepNeedsLabel to false                       *
               ************************************************************/
               AST.While obj = (AST.While) stmt ;
                 /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
               if (inWith) 
                 {throw new ParseAlgorithmException(
                   "`while' inside a `with' statement", stmt) ; };
               NeedsLabel(stmt) ;
               hadOrAddedLabel = true ;
               outAssigned.removeAllElements() ;
               Vector newOutAssigned = new Vector() ;
               InnerAddLabels(obj.unlabDo,  
                              false,             // firstLabeled
                              false,             // inWith
                              outAssigned,       // inAssigned = {}
                              newOutAssigned) ;  // outAssigned
               nextStepNeedsLabel = false ;
                 /**********************************************************
                 * A label is never needed after a `while' statement       *
                 * because that statement immediately follows the labeled  *
                 * test.                                                   *
                 **********************************************************/
             } 
           else if (stmt.getClass().equals(AST.WithObj.getClass()))
             { /************************************************************
               * This is a with statement.  Apply InnerAddLabels to the    *
               * Do field.  If inWith = false, then this is an outermost   *
               * `with'.  In that case, call with inAssigned = {}, and     *
               * add a label to the statement iff the variables assigned   *
               * within the `with' has nonempty intersection with the      *
               * inAssigned parameter of the current call.                 *
               ************************************************************/
               AST.With obj = (AST.With) stmt ;
                 /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
               Vector newInAssigned  = new Vector() ;
               if (inWith) {Copy(inAssigned, newInAssigned) ;} ;
               Vector newOutAssigned = new Vector() ;
               nextStepNeedsLabel =
                  InnerAddLabels(obj.Do,  
                                 false,             // firstLabeled
                                 true,              // inWith
                                 newInAssigned,     // inAssigned 
                                 newOutAssigned) ;  // outAssigned
               Copy(newOutAssigned, outAssigned) ;
               if (!inWith)
                 { /********************************************************
                   * This is an outermost `with'.                          *
                   ********************************************************/
                   if (! HasEmptyIntersection(inAssigned, outAssigned))
                     { /****************************************************
                       * This `with' needs a label.                        *
                       ****************************************************/
                       NeedsLabel(stmt) ;
                       hadOrAddedLabel = true ;
                       outAssigned.removeAllElements() ;
                     } ;
                 } ;
             } 
           else if (stmt.getClass().equals(AST.AssignObj.getClass()))
             { /************************************************************
               * This is an Assign statement.  Set assignedVbls to the     *
               * set of variables being assigned.  If this has non-empty   *
               * intersection with outAssigned, then statement needs a     *
               * label.  Else add those variables to outAssigned.  Set     *
               * nextStepNeedsLabel false, since there's no a priori       *
               * reason why an assignment needs a label after it.          *
               ************************************************************/
               AST.Assign obj = (AST.Assign) stmt ;
                 /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
// System.out.println("Assgn at " + stmt.location() ) ;
// PcalDebug.printVector(outAssigned, "out") ;
               /************************************************************
               * assignedVbls := the set of variables being assigned.      *
               ************************************************************/
               Vector assignedVbls = new Vector() ;
               int j = 0 ;
               while (j < obj.ass.size())
                 { AST.SingleAssign assgn = 
                     (AST.SingleAssign) obj.ass.elementAt(j) ;
                   String vbl = assgn.lhs.var ;
                   if (! IsIn(vbl, assignedVbls))
                     { assignedVbls.addElement(vbl) ; } ;
                   j = j + 1 ;
                 } ;
               if (HasEmptyIntersection(outAssigned, assignedVbls))
                 { Copy(Union(outAssigned, assignedVbls), outAssigned) ;} 
               else
                 { /********************************************************
                   * Statement needs a label.                              *
                   ********************************************************/
                   if (inWith) {throw new ParseAlgorithmException(
                                 "Second assignment to same variable " +
                                     "inside a `with' statement",
                                 stmt) ; } ;
                   
                   NeedsLabel(stmt);
                   hadOrAddedLabel = true ;
                   Copy(assignedVbls, outAssigned) ;
                 } ;

               nextStepNeedsLabel = false ;
             }
           else 
             { /************************************************************
               * Some other statement type.  Set nextStepNeedsLabel and    *
               * set assignedVbls to the set of variables being assigned   *
               * by this statement.  Should set nextStepNeedsLabel to      *
               * true and set assignedVbls to a non-empty set iff this is  *
               * a call, return, or callReturn.                            *
               ************************************************************/
               nextStepNeedsLabel = false ;
               Vector assignedVbls = new Vector() ;

               /************************************************************
               * Set isCallOrReturn true iff this is a call, return, or    *
               * callReturn.  Will set setsPrcdVbls true iff this is a     *
               * return or callReturn or a call of currentProcedure.       *
               ************************************************************/
               boolean isCallOrReturn = false ;
               boolean setsPrcdVbls   = false ;
               if (stmt.getClass().equals(AST.CallObj.getClass()))
                 { AST.Call obj = (AST.Call) stmt ;
                     /******************************************************
                     * Sets obj to an alias of stmt of the right type.     *
                     ******************************************************/
                   isCallOrReturn = true ;
                   if (obj.to.equals(currentProcedure))
                     { setsPrcdVbls = true ; } ;
                 }
               else if (   stmt.getClass().equals(AST.ReturnObj.getClass())
                        || stmt.getClass().equals(AST.CallReturnObj.getClass())
                       )
                 { isCallOrReturn = true ;
                   setsPrcdVbls = true ; 
                 } 
               // The following "else if" clause was originally missing; 
               // It was added on 15 May 2006.
               else if (stmt.getClass().equals(AST.GotoObj.getClass()))
                 { nextStepNeedsLabel = true;
                 } ;
              if (isCallOrReturn)
                { nextStepNeedsLabel = true ;
                  assignedVbls.addElement("stack") ;
                    /*******************************************************
                    * A call or return assigns to `stack'.                 *
                    *******************************************************/
                  if (setsPrcdVbls)
                    { int j = 0 ;
                      while (j < procedures.size())
                        { AST.Procedure prcd = 
                            (AST.Procedure) procedures.elementAt(j) ;
                          int k = 0 ;
                          while (k < prcd.params.size())
                            { AST.PVarDecl decl = 
                                (AST.PVarDecl) prcd.params.elementAt(k) ;
                              assignedVbls.addElement(decl.var) ;
                              k = k + 1;
                            } ;
                          k = 0 ;
                          while (k < prcd.decls.size())
                            { AST.PVarDecl decl = 
                                (AST.PVarDecl) prcd.decls.elementAt(k) ;
                              assignedVbls.addElement(decl.var) ;
                              k = k + 1;
                            } ;
                          j = j + 1;
                        }
                    } ;
                }
               if (HasEmptyIntersection(outAssigned, assignedVbls))
                 { Copy(Union(outAssigned, assignedVbls), outAssigned) ;} 
               else
                 { /********************************************************
                   * Statement needs a label.                              *
                   ********************************************************/
                   if (inWith) {throw new ParseAlgorithmException(
                                 "Call or return makes second assignment " +
                                     "to a variable inside a `with' statement",
                                 stmt) ; } ;
                   NeedsLabel(stmt);
                   hadOrAddedLabel = true ;
                   Copy(assignedVbls, outAssigned) ;
                 } ;

             } ;

           i = i + 1 ;
         }        
       return hadOrAddedLabel || nextStepNeedsLabel ;
     }

   public static void NeedsLabel(AST stmt)
     /**********************************************************************
     * Add a label to statement stmt if it doesn't already have one.  The  *
     * label is PcalParams.LabelRoot concatenated with the next number     *
     * greater than or equal to nextLabelNum for which the resulting       *
     * label has not been typed by the user.                               *
     **********************************************************************/
     { if (stmt.lbl.equals("") )
         { String lbl = PcalParams.LabelRoot + nextLabelNum ;
           nextLabelNum = nextLabelNum + 1 ;
           while (allLabels.containsKey(lbl))
             { lbl = PcalParams.LabelRoot + nextLabelNum ;
               nextLabelNum = nextLabelNum + 1 ;
             } ;
           stmt.lbl = lbl ;
           addedLabels.addElement(lbl) ;
           addedLabelsLocs.addElement(stmt.location()) ;
         }
       return ;
     }
       
/***************************************************************************
*                   SETS OF STRINGS                                        *
*                                                                          *
* Methods for handling sets of strings, where such a set is represented    *
* as a vector of its elements.                                             *
***************************************************************************/
   public static boolean IsIn(String elt, Vector set)
     /**********************************************************************
     * True iff elt is in `set'.  Implemented in a dumb way because it     *
     * should usually be called when it returns false.                     *
     **********************************************************************/
     { int i = 0 ;
       boolean result = false ;
       while (i < set.size())
        { result = result || elt.equals((String) set.elementAt(i)) ;
          i = i+1 ;
        } ;
       return result ;
     }


   public static boolean HasEmptyIntersection(Vector S, Vector T)
     /**********************************************************************
     * Returns the value of (S \cap T = {}).  Implemented in a dumb way    *
     * because it should usually be called to return false.                *
     **********************************************************************/
     { boolean negResult = false ;
       int i = 0 ;
       while (i < T.size())
         { negResult = negResult ||  IsIn((String) T.elementAt(i), S) ;
           i = i+1;
         } ;
       return ! negResult ;
     }


   public static Vector Union(Vector S, Vector T)
     /**********************************************************************
     * Returns S \cup T.                                                   *
     **********************************************************************/
     { Vector result = (Vector) S.clone() ;
       int i = 0 ;
       while (i < T.size())
         { String str = (String) T.elementAt(i) ;
           if (! IsIn(str, result))
             { result.addElement(str) ; } ;
           i = i+1 ;
         } ;
       return result ;
     }

     
   public static void Copy(Vector in, Vector out)
     /**********************************************************************
     * Sets the non-null vector `out' to a copy of the non-null vector     *
     * `in'.  Note that `out' is a "call-by-reference" argument, while     *
     * `in' is a "call-by-value" argument.                                 *
     **********************************************************************/
     { out.removeAllElements() ;
       int i = 0 ;
       while (i < in.size())
        { out.addElement(in.elementAt(i)) ; 
          i = i+1 ;
        } ;
       return ;
     }


   public static Vector MakeLabeledStmtSeq(Vector stmtseq) throws ParseAlgorithmException 
     /**********************************************************************
     * Returns the sequence of <LabeledStmt> objects represented by the    *
     * sequence of <Stmt> objects and their lbl fields.                    *
     **********************************************************************/
     { Vector result = InnerMakeLabeledStmtSeq(stmtseq);
       CheckLabeledStmtSeq(result) ;
       return result ;
      }


   public static Vector InnerMakeLabeledStmtSeq(Vector stmtseq) 
     /**********************************************************************
     * This does the real work of MakeLabeledStmtSeq.  It is made a        *
     * separate procedure to avoid calling ClassifyStmtSeq with every      *
     * recursive call.                                                     *
     **********************************************************************/
     { Vector result = new Vector() ;
       int nextStmt = 0 ;
       while (nextStmt < stmtseq.size())
         { AST.LabeledStmt lstmt = new AST.LabeledStmt() ;
           AST stmt = (AST) stmtseq.elementAt(nextStmt) ;
             /**************************************************************
             * lstmt is the current <LabeledStmt> being constructed, and   *
             * stmt is the next <Stmt> in stmtseq.                         *
             **************************************************************/

           /****************************************************************
           * Set the location of lstmt.                                    *
           ****************************************************************/
           lstmt.col  = stmt.col ;
           lstmt.line = stmt.line ;
           lstmt.macroCol  = stmt.macroCol ;
           lstmt.macroLine = stmt.macroLine ;
           PcalDebug.Assert(!stmt.lbl.equals(""),
                            "Missing Label in MakeLabeledStmtSeq") ;

           /****************************************************************
           * Set its label.                                                *
           ****************************************************************/
           lstmt.label = stmt.lbl ;

           if (stmt.lbl.equals("")) {
	           Debug.ReportBug(
	           "ParseAlgorithmInnerMakeLabeledStmtSeq found null label starting labeled stmt seq");
           }
           
           lstmt.stmts = new Vector() ;
           PCalLocation lstmtBegin = null ;
           if (!stmt.lbl.equals("")) {
               lstmtBegin = stmt.lblLocation ;
           }

           /****************************************************************
           * lstmt.stmts is obtained from the sequence of <Stmt>s          *
           * consisting of stmt and all immediately following unlabeled    *
           * statements in stmtseq.                                        *
           ****************************************************************/
           boolean firstTime = true ;
           while (   (nextStmt < stmtseq.size())
                  && (   firstTime 
                      || stmt.lbl.equals("")))
             { firstTime = false ;
                lstmt.stmts.addElement(stmt) ;
               nextStmt = nextStmt + 1;
               if  (nextStmt < stmtseq.size())
                  {stmt = (AST) stmtseq.elementAt(nextStmt) ;} ;
             } ;         
          FixStmtSeq(lstmt.stmts) ;
          int numberOfStmts = lstmt.stmts.size() ;
          if (numberOfStmts == 0) {
        	  Debug.ReportBug(
        	    "Found empty statement sequence in InnerMakeLabeledStmtSeq");
          }
          
          if (lstmtBegin == null) {
              lstmtBegin = ((AST) lstmt.stmts.elementAt(0)) .getOrigin().getBegin();
          }
          PCalLocation lstmtEnd = ((AST) lstmt.stmts.elementAt(numberOfStmts-1))
        		                     .getOrigin().getEnd();
          lstmt.setOrigin(new Region (lstmtBegin, lstmtEnd));
          result.addElement(lstmt) ;
         }
       return result ;
     }


   public static void FixStmtSeq(Vector stmtseq) 
     /**********************************************************************
     * stmtseq is a sequence of statement objects that are produced by     *
     * GetStmtSeq.  This procedure expands the substatements within each   *
     * LabelIf, LabelEither, and While object in stmtseq.  For a LabelIf,  *
     * this removes the labeled statements from the unlabThen and          *
     * unlabElse sequences and puts them in labThen and labElse.           *
     **********************************************************************/
     { Vector result = new Vector() ;
       int i = 0 ;
       while (i < stmtseq.size())
        { AST stmt = (AST) stmtseq.elementAt(i) ;
          if (stmt.getClass().equals(AST.LabelIfObj.getClass()))
             { /************************************************************
               * This is an if statement.  Set the unlabThen field to the  *
               * result of calling FixStmtSeq on the prefix of its         *
               * current value consisting of unlabeled statements.  Set    *
               * labThen to the sequence of labeled statement obtained by  *
               * calling InnerMakeLabeledStmtSeq on the rest of the        *
               * statement sequence.                                       *
               ************************************************************/
               AST.LabelIf obj = (AST.LabelIf) stmt ;
                 /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
               Vector curr = obj.unlabThen ;
               obj.unlabThen = new Vector() ;
               while (    (curr.size() > 0)
                       && ((AST) curr.elementAt(0)).lbl.equals("") )
                { obj.unlabThen.addElement(curr.elementAt(0)) ;
                  curr.removeElementAt(0) ;
                } ;
               FixStmtSeq(obj.unlabThen) ;
               obj.labThen = InnerMakeLabeledStmtSeq(curr) ;
                /********************************************************
                * Set the unlabElse and labElse fields in an analogous  *
                * fashion.                                              *
                ********************************************************/
               curr = obj.unlabElse ;
               obj.unlabElse = new Vector() ;
               while (    (curr.size() > 0)
                       && ((AST) curr.elementAt(0)).lbl.equals("") )
                { obj.unlabElse.addElement(curr.elementAt(0)) ;
                  curr.removeElementAt(0) ;
                } ;
               FixStmtSeq(obj.unlabElse) ;
               obj.labElse = InnerMakeLabeledStmtSeq(curr) ;
              }
           else if (stmt.getClass().equals(AST.LabelEitherObj.getClass()))
             { /************************************************************
               * This is a LabelEither object.  For each `or' clause, set  *
               * the unlabDo and labDo fields in the same way as the       *
               * unlabThen and labThen fields for a LabelIf object.        *
               ************************************************************/
               AST.LabelEither obj = (AST.LabelEither) stmt ;
                 /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
               int j = 0 ;
               while (j < obj.clauses.size())
                 { AST.Clause clause = (AST.Clause) obj.clauses.elementAt(j) ;
                   Vector curr = clause.unlabOr ;
                   clause.unlabOr = new Vector() ;
                   while (    (curr.size() > 0)
                           && ((AST) curr.elementAt(0)).lbl.equals("") )
                    { clause.unlabOr.addElement(curr.elementAt(0)) ;
                      curr.removeElementAt(0) ;
                    } ;
                   FixStmtSeq(clause.unlabOr) ;
                   clause.labOr = InnerMakeLabeledStmtSeq(curr) ;
                   j = j+1 ;
                 };               

             }
           else if (stmt.getClass().equals(AST.WhileObj.getClass()))
             { /********************************************************
               * This is a while statement.  Set the unlabDo field to  *
               * the prefix of its current value consisting of         *
               * unlabeled statements.  Set labDo to the sequence of   *
               * labeled statement obtained by calling                 *
               * InnerMakeLabeledStmtSeq on the rest of the statement  *
               * sequence.                                             *
               ********************************************************/
               AST.While obj = (AST.While) stmt ;
                 /******************************************************
                 * Sets obj to an alias of stmt of the right type.     *
                 ******************************************************/
               Vector curr = obj.unlabDo ;
               obj.unlabDo = new Vector() ;
               while (    (curr.size() > 0)
                       && ((AST) curr.elementAt(0)).lbl.equals("") )
                { obj.unlabDo.addElement(curr.elementAt(0)) ;
                  curr.removeElementAt(0) ;
                } ;
               FixStmtSeq(obj.unlabDo) ;
               obj.labDo = InnerMakeLabeledStmtSeq(curr) ;
             } ;
          i = i + 1 ;
        } ;
       return ;
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
   public static void CheckLabeledStmtSeq(Vector stmtseq) throws ParseAlgorithmException
     { int i = 0 ;
       while (i < stmtseq.size())
         { AST.LabeledStmt stmt = (AST.LabeledStmt) stmtseq.elementAt(i) ;
           int ignore = ClassifyStmtSeq(stmt.stmts) ;
           i = i + 1 ;
         } ;
     }

   public static int ClassifyStmtSeq(Vector stmtseq) throws ParseAlgorithmException
     /**********************************************************************
     * Vector stmtseq must be a vector of <Stmt>s.  This method returns    *
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
     { int i = 0 ;
       int result = 0 ;
       while (i < stmtseq.size())
         { AST node = (AST) stmtseq.elementAt(i) ;
             if (node.getClass().equals(
                           AST.LabelIfObj.getClass()))
               { AST.LabelIf ifNode = (AST.LabelIf) node;
                 result = ClassifyIf(ifNode) ;
                 if (result < 2)
                   { AST.If newIf = new AST.If() ;
                     newIf.test = ifNode.test ;
                     newIf.Then = ifNode.unlabThen ;
                     newIf.Else = ifNode.unlabElse ;
                     newIf.setOrigin(ifNode.getOrigin()) ;
                     stmtseq.setElementAt(newIf, i) ;
                   } ;
               }
             else if (node.getClass().equals(
                           AST.LabelEitherObj.getClass()))
               { AST.LabelEither eitherNode = (AST.LabelEither) node;
                 result = ClassifyEither(eitherNode) ;
                 if (result < 2)
                   { AST.Either newEither = new AST.Either() ;
                     newEither.ors = new Vector() ;
                     int j = 0 ;
                     while (j < eitherNode.clauses.size())
                       { newEither.ors.addElement(
                          ((AST.Clause)  
                            eitherNode.clauses.elementAt(j)).unlabOr ) ;
                         j = j + 1;
                       } ;
                     newEither.setOrigin(eitherNode.getOrigin()) ;
                     stmtseq.setElementAt(newEither, i) ;
                   } ;
               }
             else if (node.getClass().equals(
                           AST.WithObj.getClass()))
               { result = ClassifyStmtSeq(((AST.With)node).Do) ; 
                 if (result == 2)
                   { throw new ParseAlgorithmException(
                      "with statement at " + node.location() + 
                      " contains a labeled statement") ;
                   }
               }
             else if (node.getClass().equals(
                           AST.WhileObj.getClass())  )
               { if (i != 0)
                   { PcalDebug.ReportBug(
                       "ParseAlgorithm.ClassifyStmtSeq encountered `while'" +
                       " not at beginning of StmtSeq.") ;
                   } ;
                 int ignore = ClassifyStmtSeq(((AST.While) node).unlabDo) ;
                 CheckLabeledStmtSeq(((AST.While) node).labDo) ;
               }
             else if (node.getClass().equals(
                           AST.CallObj.getClass()))
               { if (! (    (i < stmtseq.size() - 1)
                        &&  ( stmtseq.elementAt(
                               i+1).getClass().equals(
                                  AST.ReturnObj.getClass())  ) 
                       )
                    )                    
                   { result = 1 ;
                   } ;
               }
             else if (   (node.getClass().equals(
                           AST.ReturnObj.getClass())  )
                      || (node.getClass().equals(
                           AST.CallReturnObj.getClass())  )
                     )
               { if (currentProcedure == null)
                   { throw new ParseAlgorithmException(
                      "return statement not in a procedure at "
                        + node.location() ) ;
                   } ;
                 result = 1 ;
               }
             else if (node.getClass().equals(
                           AST.GotoObj.getClass())  
                     )
               { result = 1 ;
               }
             else if (! (   node.getClass().equals(AST.AssignObj.getClass())
                         || node.getClass().equals(
                               AST.WhenObj.getClass())  
                         || node.getClass().equals(
                               AST.PrintSObj.getClass())  
                         || node.getClass().equals(
                               AST.AssertObj.getClass())  
                         || node.getClass().equals(
                               AST.SkipObj.getClass())  
                         || node.getClass().equals(
                               AST.MacroCallObj.getClass())  )
                     )
               { PcalDebug.ReportBug(
                  "ParseAlgorithm.ClassifyStmtSeq encountered the unexpected" +
                  " statement type " + node.getClass().toString()) ;
             }
           if (result > 0)
             { if (i == stmtseq.size() - 1)
                 { return result ;}
               else
                  { node = (AST) stmtseq.elementAt(i+1) ;
                    PcalDebug.ReportBug(
                      "Translator discovered later than it should have " +
                       " that\n  " +
                      "Statement at " + node.location() + 
                      " must have a label");
                  } ;
              }
           i = i + 1 ;
         } ;
      return result ;
     }     

   public static int ClassifyIf(AST.LabelIf node) throws ParseAlgorithmException
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
       int thenClass = ClassifyStmtSeq(node.unlabThen) ;
       boolean isLabeled = false ;
       if (node.labThen.size() > 0)
         { isLabeled = true ;
           CheckLabeledStmtSeq(node.labThen) ;
         } ;
       int elseClass = ClassifyStmtSeq(node.unlabElse) ;  
       if (node.labElse.size() > 0)
         { isLabeled = true ;
           CheckLabeledStmtSeq(node.labElse) ;
         } ;
       if (   isLabeled
           || (thenClass == 2)
           || (elseClass == 2))
         { return 2 ; } ;
       if (thenClass + elseClass > 0)
         { return 1 ; } ;
       return 0 ;
     }

   public static int ClassifyEither(AST.LabelEither node) throws ParseAlgorithmException
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
       int theClass = 0 ;
       int i = 0 ;
       while (i < node.clauses.size())
         { AST.Clause currClause = (AST.Clause) node.clauses.elementAt(i) ;
           int unlabClass = ClassifyStmtSeq(currClause.unlabOr) ;
           if (unlabClass > theClass)
             { theClass = unlabClass ; }
           if (currClause.labOr.size() > 0)
             { theClass = 2 ;
               CheckLabeledStmtSeq(currClause.labOr) ;
             } ;
           i = i + 1;
         } ;
       return theClass ;
     }



/***************************************************************************
*                         MACRO EXPANSION                                  *
*                                                                          *
* Methods for expanding macros.                                            
 * @throws ParseAlgorithmException *
***************************************************************************/

   public static void CheckForDuplicateMacros(Vector macros) throws ParseAlgorithmException
     /**********************************************************************
     * Argument macros is a vector of AST.Macro                            *
     **********************************************************************/
     { int i = 0 ;
       while (i < macros.size())
         { String namei = ((AST.Macro) macros.elementAt(i)).name ;
           int j = i + 1 ;
           while (j < macros.size())
             { if (namei.equals(((AST.Macro) macros.elementAt(j)).name))
                 { throw new ParseAlgorithmException(
                     "Multiple definitions of macro name `" + namei +"'");
                 }
               j = j + 1 ;
             }
           i = i + 1 ;
         }
     }     

   public static void ObsoleteExpandMacrosInLabeledStmtSeq(
                        Vector stmtseq, // of LabeledStmt
                        Vector macros) throws ParseAlgorithmException  // of Macro
     /**********************************************************************
     * Expands macro calls.                                                *
     **********************************************************************/
     { int i = 0 ;
       while (i < stmtseq.size())
         { AST.LabeledStmt stmt = (AST.LabeledStmt) stmtseq.elementAt(i) ;
           ExpandMacrosInStmtSeq(stmt.stmts, macros) ;
           i = i + 1 ;
         }
     }

   public static void ExpandMacrosInStmtSeq(Vector stmtseq, Vector macros) throws ParseAlgorithmException
     /**********************************************************************
     * This is called on a sequence stmtseq of statements, before          *
     * MakeLabeledStmtSeq has been called.  Therefore, stmtseq contains    *
     * no AST.If or AST.Either objects, and with empty lab...  fields in   *
     * AST.LabelIf, AST.LabelEither, and AST.while objects.                *
     **********************************************************************/
     { int i = 0 ;
       while (i < stmtseq.size())
         { AST node = (AST) stmtseq.elementAt(i) ;
             if (node.getClass().equals(
                           AST.LabelIfObj.getClass()))
               { ExpandMacrosInStmtSeq(((AST.LabelIf) node).unlabThen, 
                                       macros) ;
                 ExpandMacrosInStmtSeq(((AST.LabelIf) node).unlabElse, 
                                         macros) ;
               }
             else if (node.getClass().equals(
                           AST.LabelEitherObj.getClass()))
               { AST.LabelEither eNode = (AST.LabelEither) node ;
                 int j = 0 ;
                 while (j < eNode.clauses.size())
                   { ExpandMacrosInStmtSeq(
                       ((AST.Clause) eNode.clauses.elementAt(j)).unlabOr, 
                       macros);
                     j = j + 1;
                   } ;
               }
             else if (node.getClass().equals(
                           AST.WithObj.getClass()))
               { ExpandMacrosInStmtSeq(((AST.With)node).Do, macros) ; 
               }
             else if (node.getClass().equals(
                           AST.WhileObj.getClass())  )
               { ExpandMacrosInStmtSeq(((AST.While) node).unlabDo, macros) ;
               }
             else if (node.getClass().equals(
                           AST.MacroCallObj.getClass())  )
               { Vector expansion = 
                          ExpandMacroCall( ((AST.MacroCall) node), macros);
                 
                 stmtseq.remove(i) ;
                 int j = expansion.size() ;
                 while (j > 0)
                   { stmtseq.insertElementAt(expansion.elementAt(j-1), i) ;
                     j = j - 1 ;
                   } ;
                 i = i + expansion.size() - 1 ;
               }
           i = i + 1 ;
         } ;
      return ;
     }     

   public static Vector ExpandMacroCall(AST.MacroCall call, Vector macros) throws ParseAlgorithmException
     { // Set macroDef to the Macro object
       AST.Macro macroDef = null ;
       int i = 0 ;
       while (i < macros.size() )
         { AST.Macro md = (AST.Macro) macros.elementAt(i) ;
           if (md.name.equals(call.name))
             { macroDef = md ; } ;
           i = i + 1 ;
         } ;

       if (macroDef == null)
         { throw new ParseAlgorithmException("Macro " + call.name + 
           // This error message changed by LL on 14 July 2011 when GetMacro was 
           // changed to allow macros to call other macros.  Change back the message
           // to back out of that other change.
           //
           //  " undefined or called inside a macro definition,\n    at "
            " undefined,\n    at " + call.location() ) ; 
         } ;

       int numOfArgs = call.args.size() ;
       if (macroDef.params.size() != numOfArgs)
         { throw new ParseAlgorithmException("Macro " + call.name + 
                                 " called with wrong number of arguments at "
                                   + "\n    " + call.location()) ; 
         } ;
      Vector result = SubstituteInStmtSeq(macroDef.body,
                                          call.args,
                                          macroDef.params,
                                          call.line,
                                          call.col ) ;
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
      if (result.size() > 0) 
        { AST first = (AST) result.elementAt(0) ;
          first.lbl = call.lbl ;
          first.lblLocation = call.lblLocation ;
          Region callOrigin = call.getOrigin();
          if (callOrigin != null) {
              first.macroOriginBegin = callOrigin.getBegin();
              AST last = (AST) result.elementAt(result.size() - 1) ;
              last.macroOriginEnd = callOrigin.getEnd();
          }
        } ;

      return result ;
     }



    public static Vector SubstituteInLabeledStmtSeq(
                           Vector stmts,  // of AST.LabeledStmt 
                           Vector args,   // of TLAExpr
                           Vector params) throws ParseAlgorithmException // of String
      { Vector result = new Vector() ;
        int i = 0 ;
        while (i < stmts.size())
          {  result.addElement( SubstituteInLabeledStmt( 
                                (AST.LabeledStmt) stmts.elementAt(i),
                                args,
                                params) );
           i = i + 1 ;
          } ;

        return result ;
      }

   public static AST.LabeledStmt SubstituteInLabeledStmt(
                                   AST.LabeledStmt stmt, 
                                   Vector args,   // of TLAExpr
                                   Vector params) throws ParseAlgorithmException // of String
      { AST.LabeledStmt result = new AST.LabeledStmt() ;
        result.label = stmt.label ;
        result.stmts = SubstituteInStmtSeq(stmt.stmts, args, params, -1, 0) ;
        result.setOrigin(stmt.getOrigin()) ;
        return result ;
      }
      
/***************************************************************************
* The SubstituteInStmtSeq method does substitutions only in the class of   *
* statements found in the body of a macro.  However, it is simple to       *
* define a SubstituteInLabeledStmtSeq method and enhance                   *
* SubstituteInStmtSeq so the SubstituteInLabeledStmtSeq can be used to do  *
* arbitrary substitutions in the body of a process or uniprocess           *
* algorithm.                                                               *
***************************************************************************/
    public static Vector SubstituteInStmtSeq(Vector stmts, // of AST
                                             Vector args,   // of TLAExpr
                                             Vector params, // of String
                                             int macroLine,
                                             int macroCol) throws ParseAlgorithmException
      /*********************************************************************
      * A vector of new AST nodes obtained from the statements in stmts    *
      * by substituting the expressions in args for the corresponding      *
      * parameters in params inside the expansion of a macro call at line  *
      * macroLine, column macroCol, where macroLine = -1 if this is not    *
      * being called because of a macro expansion.                         *
      *********************************************************************/
      { Vector result = new Vector() ;
        int i = 0 ;
        while (i < stmts.size())
          {  result.addElement( SubstituteInStmt( (AST) stmts.elementAt(i),
                                args,
                                params,
                                macroLine,
                                macroCol   ) );
           i = i + 1 ;
          } ;

        return result ;
      }

    public static AST SubstituteInStmt(AST stmt, 
                                       Vector args,   // of TLAExpr
                                       Vector params, // of String
                                       int macroLine,
                                       int macroCol) throws ParseAlgorithmException
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
        if (stmt.getClass().equals( AST.AssignObj.getClass()))
          { AST.Assign tstmt = (AST.Assign) stmt ;
            AST.Assign result = new AST.Assign() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            int i = 0 ;
            result.ass = new Vector() ;
            while (i < tstmt.ass.size())
              { result.ass.addElement(
                  SubstituteInSingleAssign(
                    (AST.SingleAssign) tstmt.ass.elementAt(i),
                    args, params, macroLine, macroCol) ) ;
                i = i + 1 ;
              } ;
           return result ;
          }

        if (stmt.getClass().equals( AST.IfObj.getClass()))
          { AST.If tstmt = (AST.If) stmt ;
            AST.If result = new AST.If() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 

            result.test  = tstmt.test.cloneAndNormalize() ;
            result.test.substituteForAll(args, params) ;

            result.Then = SubstituteInStmtSeq(
                            tstmt.Then, args, params, macroLine, macroCol );

            result.Else = SubstituteInStmtSeq(
                            tstmt.Else, args, params, macroLine, macroCol );
            
            return result;
          } ;

        if (stmt.getClass().equals( AST.EitherObj.getClass()))
          { AST.Either tstmt = (AST.Either) stmt ;
            AST.Either result = new AST.Either() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            result.ors = new Vector() ;
            int i = 0 ;
            while (i < tstmt.ors.size())
              { result.ors.addElement(
                     SubstituteInStmtSeq(
                        (Vector) tstmt.ors.elementAt(i), 
                          args, params, macroLine, macroCol ) ) ;
                i = i + 1 ;
              } ;
              
            return result;
          } ;

        if (stmt.getClass().equals( AST.WithObj.getClass()))
          { AST.With tstmt = (AST.With) stmt ;
            AST.With result = new AST.With() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 

            result.var  = tstmt.var ;
            result.isEq = tstmt.isEq ;
            result.exp  = tstmt.exp.cloneAndNormalize() ;
            result.exp.substituteForAll(args, params) ;
            result.Do = SubstituteInStmtSeq(
                            tstmt.Do, args, params, macroLine, macroCol);
            return result;
          } ;

        if (stmt.getClass().equals( AST.WhenObj.getClass()))
          { AST.When tstmt = (AST.When) stmt ;
            AST.When result = new AST.When() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 

            result.exp  = tstmt.exp.cloneAndNormalize() ;
            result.exp.substituteForAll(args, params) ;
            return result;
          } ;

        if (stmt.getClass().equals( AST.AssertObj.getClass()))
          { AST.Assert tstmt = (AST.Assert) stmt ;
            AST.Assert result = new AST.Assert() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 

            result.exp  = tstmt.exp.cloneAndNormalize() ;
            result.exp.substituteForAll(args, params) ;
            return result;
          } ;


        if (stmt.getClass().equals( AST.SkipObj.getClass()))
          { AST.Skip tstmt = (AST.Skip) stmt ;
            AST.Skip result = new AST.Skip() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            return result;
          } ;


        if (stmt.getClass().equals( AST.PrintSObj.getClass()))
          { AST.PrintS tstmt = (AST.PrintS) stmt ;
            AST.PrintS result = new AST.PrintS() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            result.exp  = tstmt.exp.cloneAndNormalize() ;
            result.exp.substituteForAll(args, params) ;
            return result;
          } ;
       
        /*******************************************************************
        * The following statements are ones that may not appear in a macro *
        * definition body.                                                 *
        *******************************************************************/
        if (stmt.getClass().equals( AST.WhileObj.getClass()))
          { AST.While tstmt = (AST.While) stmt ;
            AST.While result = new AST.While() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            result.test  = tstmt.test.cloneAndNormalize() ;
            result.test.substituteForAll(args, params) ;
            result.unlabDo = 
              SubstituteInStmtSeq(tstmt.unlabDo, 
                                  args,   
                                  params, 
                                  macroLine,
                                  macroCol) ;
            result.labDo = 
              SubstituteInLabeledStmtSeq(tstmt.labDo, 
                                          args,   
                                          params) ;

            return result;
          } ;

        if (stmt.getClass().equals( AST.LabelIfObj.getClass()))
          { AST.LabelIf tstmt = (AST.LabelIf) stmt ;
            AST.LabelIf result = new AST.LabelIf() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            result.test  = tstmt.test.cloneAndNormalize() ;
            result.test.substituteForAll(args, params) ;
            result.unlabThen = 
              SubstituteInStmtSeq(tstmt.unlabThen, 
                                  args,   
                                  params, 
                                  macroLine,
                                  macroCol) ;
            result.labThen = 
              SubstituteInLabeledStmtSeq(tstmt.labThen, 
                                          args,   
                                          params) ;
            result.unlabElse = 
              SubstituteInStmtSeq(tstmt.unlabElse, 
                                  args,   
                                  params, 
                                  macroLine,
                                  macroCol) ;
            result.labElse = 
              SubstituteInLabeledStmtSeq(tstmt.labElse, 
                                          args,   
                                          params) ;

            return result;
          } ;

        if (stmt.getClass().equals( AST.LabelEitherObj.getClass()))
          { AST.LabelEither tstmt = (AST.LabelEither) stmt ;
            AST.LabelEither result = new AST.LabelEither() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            result.clauses = new Vector() ;
            int i = 0 ;
            while (i < tstmt.clauses.size())
             { AST.Clause oldClause = 
                    (AST.Clause) tstmt.clauses.elementAt(i);
               AST.Clause newClause = new AST.Clause() ;
               newClause.setOrigin(oldClause.getOrigin()) ;
               newClause.labOr = SubstituteInLabeledStmtSeq(
                                     oldClause.labOr, 
                                     args,   
                                     params) ;
               newClause.unlabOr = SubstituteInStmtSeq(
                                     oldClause.unlabOr, 
                                     args,   
                                     params, 
                                     macroLine,
                                     macroCol) ;
               result.clauses.addElement(newClause) ;
               i = i + 1 ;
             } ;
            return result ;
          } ;

        if (stmt.getClass().equals( AST.CallObj.getClass()))
          { AST.Call tstmt = (AST.Call) stmt ;
            AST.Call result = new AST.Call() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            result.to        = tstmt.to ;
            result.returnTo  = tstmt.returnTo ;
            result.args = 
               TLAExpr.SeqSubstituteForAll(tstmt.args, args, params) ;
            return result;
          } ;

        if (stmt.getClass().equals( AST.ReturnObj.getClass()))
          { AST.Return tstmt = (AST.Return) stmt ;
            AST.Return result = new AST.Return() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            result.from = tstmt.from ;
            return result;
          } ;

        if (stmt.getClass().equals( AST.CallReturnObj.getClass()))
          { AST.CallReturn tstmt = (AST.CallReturn) stmt ;
            AST.CallReturn result = new AST.CallReturn() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            result.to   = tstmt.to ;
            result.from = tstmt.from ;
            result.args = 
               TLAExpr.SeqSubstituteForAll(tstmt.args, args, params) ;
            return result;
          } ;

        if (stmt.getClass().equals( AST.GotoObj.getClass()))
          { AST.Goto tstmt = (AST.Goto) stmt ;
            AST.Goto result = new AST.Goto() ;
            result.col  = tstmt.col ;
            result.line = tstmt.line ;
            result.macroCol  = tstmt.macroCol ;
            result.macroLine = tstmt.macroLine ;
            result.setOrigin(tstmt.getOrigin()) ;
            if (macroLine > 0)
              { result.macroLine = macroLine ;
                result.macroCol  = macroCol ;
              } ; 
            result.to = tstmt.to ;
            return result;
          } ;

        PcalDebug.ReportBug(
           "Found unexpected statement type in macro at" +
             stmt.location() ); 
        return new AST(); // Needed to keep Java from complaining.
      } catch (UnrecoverableException e) 
      {
          throw new ParseAlgorithmException(e.getMessage());
      }
    }      

    public static AST SubstituteInSingleAssign(
                AST.SingleAssign assgn, 
                Vector args,   // of TLAExpr
                Vector params, // of String
                int macroLine,
                int macroCol) throws ParseAlgorithmException
      /*********************************************************************
      * A new AST.SingleAssign node obtained from assgn by substituting    *
      * the expressions in args for the corresponding parameters in        *
      * params inside the expansion of a macro call at line macroLine,     *
      * column macroCol, where macroLine = -1 if this is not being called  *
      * during macro expansion.                                            *
      *********************************************************************/
      { 
        try {
        AST.SingleAssign result = new AST.SingleAssign() ;
        result.setOrigin(assgn.getOrigin());
        result.col  = assgn.col ;
        result.line = assgn.line ;
        result.macroCol  = assgn.macroCol ;
        result.macroLine = assgn.macroLine ;
        if (macroLine > 0)
          { result.macroLine = macroLine ;
            result.macroCol  = macroCol ;
          } ; 
        /*******************************************************************
        * Do substitution in right-hand-side expression.                   *
        *******************************************************************/
        result.rhs = assgn.rhs.cloneAndNormalize() ;
        result.rhs.substituteForAll(args, params) ;

        result.lhs = new AST.Lhs() ;
        result.lhs.setOrigin(assgn.getOrigin()) ;
        result.lhs.sub = assgn.lhs.sub ;
        /*******************************************************************
        * If there is a subscript on the left-hand-side, substitute in     *
        * it.                                                              *
        *******************************************************************/
        if (    (assgn.lhs.sub.tokens != null) 
             && (assgn.lhs.sub.tokens.size() != 0))
            /***************************************************************
            * I'm not sure any more if an AST.SingleAssign representing    *
            * an assignment with no subscript has a null sub field or a    *
            * vector of length 0.                                          *
            ***************************************************************/
          { result.lhs.sub = assgn.lhs.sub.cloneAndNormalize() ;
            result.lhs.sub.substituteForAll(args, params) ;
          } ;

        /*******************************************************************
        * Do substitution for the variable if necessary.                   *
        *******************************************************************/
        result.lhs.var = assgn.lhs.var ;
        
        int i = 0 ;
        boolean found = false ;
        while (   (i < params.size())
               && ! found )
          { if (result.lhs.var.equals((String) params.elementAt(i)))
              { found = true ;}
            else {i = i + 1 ;}
          } ;

        if (found)
          { TLAExpr subForVar = (TLAExpr) args.elementAt(i) ;
            TLAToken varToken = subForVar.tokenAt(new IntPair(0,0)) ;
            if (varToken.type != TLAToken.IDENT)
              { throw new ParseAlgorithmException(
                 "Macro expansion substitutes `" + varToken.string +
                 "' for assignment variable\n    at " + result.location());
              } ;
            result.lhs.var = varToken.string ;

            if (subForVar.stepCoord(new IntPair(0,0), 1) != null)
              { /***********************************************************
                * More than a single token is being substituted for the    *
                * variable--for example, we may be substituting "x[0]"     *
                * for "y" in "y[i] := ...".  The rest of the expression    *
                * must therefore be prepended to the subscript.            *
                *                                                          *
                * We first set exprCopy to a clone of the substituting     *
                * expression with the first token (the one that became     *
                * the assignment variable) removed.                        *
                ***********************************************************/
                TLAExpr exprCopy = subForVar.cloneAndNormalize() ;
                Vector firstLine = (Vector) exprCopy.tokens.elementAt(0) ;
                firstLine.removeElementAt(0) ;
                exprCopy.normalize() ; 
                  /*********************************************************
                  * We must normalize because the deleted token may be an  *
                  * anchor token, and the deletion might have created an   *
                  * empty first line.                                      *
                  *********************************************************/
                if (   (result.lhs.sub == null)
                    || (result.lhs.sub.tokens.size() == 0))
                   /********************************************************
                   * I'm not sure any more if an AST.SingleAssign          *
                   * representing an assignment with no subscript has a    *
                   * null sub field or a vector of length 0.               *
                   ********************************************************/
                  { /*******************************************************
                    * There was no subscript in the original statement.    *
                    *******************************************************/
                    result.lhs.sub = exprCopy ;
                  } 
                else
                  { /*******************************************************
                    * There was already a subscript, so we must prepend.   *
                    * We don't add any space after the prepended           *
                    * expression because, to be sensible, the existing     *
                    * subscript must begin with "[" or ".".                *
                    *******************************************************/
                    result.lhs.sub.prepend(exprCopy, 0) ;
                  } 
              }  
          }
        return result;
        } catch (TLAExprException e) 
        {
            throw new ParseAlgorithmException(e.getMessage());
        }
      }


/*************************** UTILITY METHODS ******************************/
//    private static String Loc(int line , int col)
//      { return  }

    private static void ParsingError(String msg) throws ParseAlgorithmException
      { throw new ParseAlgorithmException(
           msg + "\n    line " + lastTokLine + ", column " + lastTokCol );
      }

   public static void GobbleCommaOrSemicolon() throws ParseAlgorithmException
     /**********************************************************************
     * Equivalent to GobbleThis(",") if the next token is a ",", else to   *
     * GobbleThis(";").                                                    *
     **********************************************************************/
     { String nxt = PeekAtAlgToken(1) ;
       if (nxt.equals(",")) { GobbleThis(",") ;}
       else {GobbleThis(";");};
       return ;
     }
          
   public static void GobbleBeginOrLeftBrace() throws ParseAlgorithmException
     /**********************************************************************
     * Used when expecting a "begin" in the p-syntax or a "{" in the       *
     * c-syntax.  Gobbles is and sets pSyntax or cSyntax.                  *
     **********************************************************************/
     { if (pSyntax) 
         { GobbleThis("begin") ;}
       else if (cSyntax)
         { GobbleThis("{") ;}
       else {PcalDebug.ReportBug("Syntax not initialized.") ;} ;
       return ;
     }

   public static void GobbleEndOrRightBrace(String str) throws ParseAlgorithmException
     /**********************************************************************
     * Used when expecting an "end str" in the p-syntax or a "}" in the    *
     * c-syntax.                                                           *
     **********************************************************************/
     { if (pSyntax) 
         { GobbleThis("end") ;
           GobbleThis(str) ; }
       else if (cSyntax)
         { GobbleThis("}") ;}
       else
         { PcalDebug.ReportBug("Bad call of GobbleEndRightBrace") ; } ;
       return ;
     }

   public static void GobbleThis(String str) throws ParseAlgorithmException
     { /********************************************************************
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
       if ( str.equals(";") )
         { String nxt = PeekAtAlgToken(1) ;
           if (    nxt.equals("end")
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
              )
             { return ;
             };                   
          if (     nxt.equals("if")
                || nxt.equals("either")
                || nxt.equals("while")
                || nxt.equals("with")
                || nxt.equals("call")
                || nxt.equals("return")
                || nxt.equals("goto")
                || nxt.equals("print")
                || nxt.equals("assert")
                || nxt.equals("skip")
              )
             { /************************************************************
               * This was changed from a warning to an error by LL on 28   *
               * Feb 2006 because the translation will be incorrect if     *
               * there is a label following the missing ";".               *
               ************************************************************/
              throw new ParseAlgorithmException("Missing `;' before line " + 
                                   (curTokLine[0] + 1) +
                                   ", column " +
                                   (curTokCol[0] + 1) );
             };                   
         } ;
       String tok = GetAlgToken(); 
       if (! tok.equals(str) )
         { ParsingError("Expected \"" + str + "\" but found \""
                            + tok + "\"") ; } ;
     }

   public static void MustGobbleThis(String str) throws ParseAlgorithmException
     { 
       String tok;
    try
    {
        tok = GetAlgToken();
    } catch (ParseAlgorithmException e)
    {
        throw new ParseAlgorithmException(e.getMessage());
    }
       if (! tok.equals(str) )
         { PcalDebug.ReportBug("Expected \"" + str + "\" but found \""
                                 + tok + "\"") ; } ;
     }

   public static boolean GobbleEqualOrIf() throws ParseAlgorithmException
     /**********************************************************************
     * Gobbles the next token, returns true if it is "=", false if it is   *
     * "\in", and reports an error otherwise.                              *
     **********************************************************************/
     { String tok = GetAlgToken() ;
       if (tok.equals("="))
         { return true ; } ;
       if (tok.equals("\\in"))
         { return false ; }
       ParsingError("Expected \"=\" or \"\\in\"  but found \""
                                 + tok + "\"") ; 
       return false ; // Never executed, but the compiler needs it.
     }
     

   public static String[] LAT = new String[10] ;
   public static int LATsize = 0; 
     /**********************************************************************
     * LAT[0], LAT[1], ...  , LAT[LATsize-1] contain tokens that have      *
     * been read from the algorithm with Tokenize.GetAlgorithmToken but    *
     * not yet processed.  It should never contain a token that's part of  *
     * an Expr.                                                            *
     **********************************************************************/

   public static int[] curTokCol  = new int[10];
   public static int[] curTokLine = new int[10];
     /**********************************************************************
     * curTokCol[i] and curTokLine[i] are the result of calling            *
     * PcalCharReader.getLineNumber() and                                  *
     * PcalCharReader.getColumnNumber() when the reader was positioned     *
     * just before the token in LAT[i].                                    *
     **********************************************************************/

   public static int lastTokCol ;
   public static int lastTokLine ;
     /*********************************************************************
     * The column and line number of the last token returned with          *
     * GetAlgToken, where the numbering starts at 1.  The translation      *
     * from Java ordinals to human ordinals occurs when these variables    *
     * are set.                                                            *  
     * @throws ParseAlgorithmException *                                   *
     **********************************************************************/
   /**
    * The last string returned by GetAlgToken or gobbled by Gobble...
    */
   private static String lastTokString ;
   
   
   /**
    * Returns the PCalLocation object corresponding to the beginning of
    * the last token returned by GetAlgToken or gobbled by a Gobble...
    * method.  
    * 
    * @return
    */
   private static PCalLocation GetLastLocationStart() {
       return new PCalLocation(lastTokLine-1, lastTokCol-1) ;
   }
   
   /**
    * Returns the PCalLocation object corresponding to the position to
    * the right of the last token returned by GetAlgToken or gobbled by 
    * a Gobble... method.
    * 
    * @return
    */
   private static PCalLocation GetLastLocationEnd() {
       return new PCalLocation(lastTokLine-1, lastTokCol-1 + lastTokString.length()) ;
   }
   public static String GetAlgToken() throws ParseAlgorithmException
     /**********************************************************************
     * Return the next algorithm token.                                      *
     **********************************************************************/
     { if (LATsize == 0)
         { charReader.peek() ;
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
           lastTokCol  = charReader.getColumnNumber() + 1;
           lastTokLine = charReader.getLineNumber() + 1;
           String tok;
        try
        {
            tok = Tokenize.GetAlgorithmToken(charReader);
        } catch (TokenizerException e)
        {
            throw new ParseAlgorithmException(e.getMessage());
        } 
           lastTokString = tok ;
           return tok ; 
         } ;
       lastTokCol  = curTokCol[0] + 1 ;
       lastTokLine = curTokLine[0] + 1 ;
       String result = LAT[0] ;
       int i = 1 ;
       while (i < LATsize)
         { LAT[i-1] = LAT[i] ;
           curTokCol[i-1]  = curTokCol[i] ;
           curTokLine[i-1] = curTokLine[i] ;
           i = i + 1;
         } ;
       LATsize = LATsize - 1 ;
       lastTokString = result ;
       return result;
     }   

   public static String PeekAtAlgToken(int tokNum) throws ParseAlgorithmException
     /**********************************************************************
     * This returns the tokNum-th token ahead, but does not actually       *
     * remove any token from the input stream.  PeekAtAlgToken(1) returns  *
     * the next token, PeekAtAlgToken(2) returns the one after that, etc.  *
     **********************************************************************/
     { while ((LATsize < tokNum))
         { /****************************************************************
           * Move charReader to beginning of next non-space token and get  *
           * line and column numbers.                                      *
           ****************************************************************/

           /****************************************************************
           * Change made 14 January 2009 by LL. Changed call of            *
           * charReader.peek() to this call plus test for end of file to   *
           * correct bug_08_12_12.                                         *
           ****************************************************************/
           if (charReader.peek().equals("\t") ) { 
               throw new ParseAlgorithmException(
                 "Premature end of file, perhaps because of " + 
                 "unclosed comment, near\n" + 
                 "    line " + (curTokLine[LATsize]+1) +
                 ", column " + (curTokCol[LATsize]+1)); 
             };
           curTokCol[LATsize]  = charReader.getColumnNumber();
           curTokLine[LATsize] = charReader.getLineNumber();
           try
        {
            LAT[LATsize] = Tokenize.GetAlgorithmToken(charReader);
        } catch (TokenizerException e)
        {
            throw new ParseAlgorithmException(e.getMessage());
        }
           LATsize = LATsize + 1 ;
         } ;
       return LAT[tokNum - 1] ;
     }          

   public static String PeekPastAlgToken(int tokNum) throws ParseAlgorithmException
     /**********************************************************************
     * This performs and returns the results of a PcalCharReader.peek()    *
     * at the input stream after the tokNum-th token after the current     *
     * one, where tokNum = 0 means from the current logical point in the   *
     * input stream.  This produces an error if tokNum > LATsize, meaning  *
     * that you can't perform this operation at a point before a token     *
     * that has been peeked at using PeekAtAlgToken.                       *
     **********************************************************************/
     { 
       if (tokNum < LATsize)
         { PcalDebug.ReportBug ("ParseAlgorithm.PeekPastAlgToken called " +
                                 "to peek after a token" +
                                 "\n    it has already peeked at") ; 
         } ;
       while (tokNum > LATsize)
         { try
        {
            LAT[LATsize] = Tokenize.GetAlgorithmToken(charReader);
        } catch (TokenizerException e)
        {
            throw new ParseAlgorithmException(e.getMessage());
        }
           LATsize = LATsize + 1 ;
         } ;
       return charReader.peek() ;
     } ;


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
   public static void uncomment(Vector inp,
                                int begLine,
                                int begCol) throws ParseAlgorithmException

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
     { int line = begLine ;
       int col  = begCol ;
       boolean notDone = true ;
       int commentDepth = 0 ;
       StringBuffer newLine = 
           new StringBuffer(((String) 
                               inp.elementAt(line)).substring(0, col)) ;
       while(notDone && line < inp.size())
         { String oldLine = (String) inp.elementAt(line) ;
           boolean inString = false ;
           boolean afterBackslash   = false ;
           boolean afterAsterisk    = false ;
           while (notDone && col < oldLine.length())
             { char inChar = oldLine.charAt(col) ;
               char outChar = inChar ;
               if (    (inChar == '(')
                    && ! inString
                    && (col < oldLine.length()-1)
                    && (oldLine.charAt(col+1) == '*'))
                 { commentDepth = commentDepth + 1 ;
                   outChar = ' ' ;
                   col = col + 1 ;
                   newLine.append(outChar) ;
                 } 
               else if (    (inChar == '*')
                    && ! inString
                    && (col < oldLine.length()-1)
                    && (oldLine.charAt(col+1) == ')'))
                 { if (commentDepth == 0)
                     { // This end comment must come after the end of
                       // the algorithm.
                       newLine.append(inChar) ;
                       outChar = ')' ;   
                       col = col + 1 ;
                       notDone = false ;
                     }
                   else
                    { commentDepth = commentDepth - 1 ;
                      outChar = ' ' ;
                      col = col + 1 ;
                      newLine.append(outChar) ;
                    };
                 } 
               else if (commentDepth == 0)
                 { /********************************************************
                   * Not in a comment.                                     *
                   ********************************************************/
                   if (inString)
                    { if (inChar == '"' /* " */ )
                        { inString = false ;
                        } 
                      else if (  (inChar == '\\')
                               && (col < oldLine.length()-1))
                        { newLine.append(inChar) ;
                          outChar = oldLine.charAt(col+1)  ;
                          col = col + 1 ;
                        } ;
                    } 
                  else // Not in a string.
                   { if (   (inChar == '\\')
                         && (col < oldLine.length()-1)
                         && (oldLine.charAt(col+1) == '*'))
                       { // End-of-line comment
                         outChar = ' ' ;
                         col = oldLine.length() ;
                       }
                     else if (inChar == '"')
                      { inString = true ;
                      }
                   } ;
                  }
               else
                 { /********************************************************
                   * In a comment.                                         *
                   ********************************************************/
                   outChar = ' ' ;
                 } ;
               newLine.append(outChar) ;
               col = col + 1;
             } ;
           if (inString)
            { throw new ParseAlgorithmException("Unterminated string in line " + 
                                        (line+1) ) ;
            }
           inp.set(line, newLine.toString()) ;           
           newLine = new StringBuffer() ;
           col  = 0 ;
           line = line + 1 ;
         }
       return;
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
     public static boolean ProcessVersion(Vector inputVec, 
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
    public static int ProcessOptions(Vector untabInputVec, IntPair curLoc)
    {
        String curLine = GotoNextNonSpace(untabInputVec, curLoc);
        if (curLine.substring(curLoc.two).startsWith("options"))
        {
            // Process the options and move curLoc and curLine
            // to just after the closing ")".
            curLoc.two = curLoc.two + 7; // go to position after "options"
            curLine = GotoNextNonSpace(untabInputVec, curLoc);
            if (!curLine.substring(curLoc.two).startsWith("("))
            {
                curLoc.one = untabInputVec.size();
                PcalDebug.reportError("`PlusCal options' not followed by '('");
                return trans.STATUS_EXIT_WITH_ERRORS;
            }
            curLoc.two++;
            curLine = GotoNextNonSpace(untabInputVec, curLoc);

            Vector argsVec = new Vector();
            // the vector of option arguments

            while (curLoc.one < untabInputVec.size() && (curLine.charAt(curLoc.two) != ')'))
            {
                if (curLine.charAt(curLoc.two) == ',')
                {
                    curLoc.two++;
                } else
                {
                    int endOfArg = NextDelimiterCol(curLine, curLoc.two);
                    argsVec.addElement(curLine.substring(curLoc.two, endOfArg));
                    curLoc.two = endOfArg;
                }
                curLine = GotoNextNonSpace(untabInputVec, curLoc);
            }

            if (!(curLoc.one < untabInputVec.size()))
            {
                PcalDebug.reportError("No closing ')' found in options statement");
                return trans.STATUS_EXIT_WITH_ERRORS;
            }
            curLoc.two++;
            curLine = GotoNextNonSpace(untabInputVec, curLoc);

            // Process the options arguments.
            argsVec.addElement(""); // add dummy final argument
            String[] argsArray = new String[argsVec.size()];
            for (int i = 0; i < argsArray.length; i++)
            {
                argsArray[i] = (String) argsVec.elementAt(i);
            }
// printArray(argsArray);           
            int status = trans.parseAndProcessArguments(argsArray);
            if (status != trans.STATUS_OK)
            {
                return status;
            }
        }
        return trans.STATUS_OK;
    }
   
   /**
    * Searches for token, starting from curLoc in the String Vector inputVec, and
    * updates curLoc to the position immediately after the token if it's found.
    * Otherwise, it throws a ParseAlgorithmException.  The token must be
    * a sequence of letters, numbers, and "_" characters that is terminated by
    * any other kind of character or the end of a line.
    * 
    * See the comments above for an explanation of the arguments.
    * 
    * @param token           The token being searched for.
    * @param inputVec        Input String Vector 
    * @param curLoc          <row, column> (Java coordinates) of beginning of search.
    * @throws ParseAlgorithmException
    */
   public static void FindToken(
           String token,  
           Vector inputVec,  
           IntPair curLoc,   
           String errorMsg  // The error message to be reported if not found.
          )
             throws ParseAlgorithmException {
       boolean found = false;
       while ((!found) && (curLoc.one < inputVec.size())) {
         String curLine = GotoNextNonSpace(inputVec, curLoc);
             if (curLine.substring(curLoc.two).startsWith(token)){
                 int endLoc = curLoc.two + token.length();
                 if ( (endLoc >= curLine.length()) || 
                        ! (Character.isLetter(curLine.charAt(endLoc)) ||
                           (curLine.charAt(endLoc) == '_'))) {                
                   found = true;
//                   if (outputVec != null && curLoc.two != 0) {
//                      outputVec.addElement(curLine.substring(0, curLoc.two));
//                   }
                   curLoc.two = endLoc;
                 }                
              }
             curLoc.two = NextSpaceCol(curLine, curLoc.two);
             
            // if ((!found) && (curLoc.two < curLine.length()))
            //
            // {
            // char c = curLine.charAt(curLoc.two);
            // if ((c == '(') && (curLoc.two + 1 < curLine.length()) && (curLine.charAt(curLoc.two + 1) == '*'))
            // {
            // ParseAlgorithm.gotoEndOfComment(inputVec, curLoc);
            // curLine = GotoNextNonSpace(inputVec, curLoc);
            // } else if ((c == '\\') && (curLoc.two + 1 < curLine.length())
            // && (curLine.charAt(curLoc.two + 1) == '*'))
            // {
            // // if (replace) {
            // // inputVec.setElementAt(
            // // curLine.substring(0, curLoc.two), curLoc.one);
            // // }
            // curLoc.two = curLine.length();
            // } else if (c == '"')
            // {
            // curLoc.two = ParseAlgorithm.findEndOfString(curLine, curLoc.two, curLoc.one);
            // }
            // }

       } // end of while, either found beginning or at end of file
       if (!found) {
           throw new ParseAlgorithmException(errorMsg) ;
         } ;

       return ;

   }
   
   /**
    * Assumes that curLoc points to a left brace ("{") in the String 
    * Vector inputVec, and it searches for the matching right brace.
    * It updates curLoc to the position immediately after the token if 
    * it's found.  Otherwise, it raises a ParseAlgorithmException.
    * 
    * See the comments above for an explanation of the arguments.
    * The PlusCal code currently calls this only with replace = true and 
    * outputVec = null.
    * 
    * @param inputVec        Input String Vector 
    * @param outputVec       Output String Vector, or null
    * @param curLoc          <row, column> (Java coordinates) of beginning of search.
    * @param replace         True iff replacing comments by spaces.
    * @throws ParseAlgorithmException
    */
   public static void FindMatchingBrace(
           Vector inputVec,  // Vector of strings
//           Vector outputVec, // null or Vector of strings
           IntPair curLoc,   // <row, column> in Java coordinates of
                              // "(*" that begins a comment.
//           boolean replace, // true iff comment should
//                           // be replaced by spaces.
           String errorMsg  // The error message if the brace isn't found
          )
             throws ParseAlgorithmException {

       curLoc.two++;
       while (curLoc.one < inputVec.size()) {
           String curLine = (String) inputVec.elementAt(curLoc.one);
           while (curLoc.two < curLine.length()) {
             curLoc.two = NextBraceQuoteOrCommentCol(curLine, curLoc.two);
                if (curLoc.two < curLine.length())
                {
                    char c = curLine.charAt(curLoc.two);
                    if (c == '}')
                    {
                        curLoc.two++;
                        // if (outputVec != null) {
                        // outputVec.addElement(curLine.substring(0, curLoc.two));
                        // }
                        return;
                    } else if (c == '{')
                    {
                        FindMatchingBrace(inputVec, curLoc, errorMsg);
                        curLine = (String) inputVec.elementAt(curLoc.one);
                    } else if ((c == '(') && (curLoc.two + 1 < curLine.length())
                            && (curLine.charAt(curLoc.two + 1) == '*'))
                    {
                        ParseAlgorithm.gotoEndOfComment(inputVec, curLoc);
                        curLine = (String) inputVec.elementAt(curLoc.one);
                    } else if ((c == '\\') && (curLoc.two + 1 < curLine.length())
                            && (curLine.charAt(curLoc.two + 1) == '*'))
                    {
                        // if (replace) {
                        // inputVec.setElementAt(
                        // curLine.substring(0, curLoc.two), curLoc.one);
                        // }
                        curLoc.two = curLine.length();
                    } else if (c == '"')
                    {
                        curLoc.two = ParseAlgorithm.findEndOfString(curLine, curLoc.two, curLoc.one);
                    }
                }

         }// end of while, either at end of line or found matching brace
         curLoc.one ++;
         curLoc.two = 0;
       } // end of while, either found beginning or at end of file

           throw new ParseAlgorithmException(errorMsg) ;


   }
   /*********************** Helpful Methods for Parsing StringVectors ************/
   
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
//    static int NextCharOf(String str, int col, char[] chs) {
//       int curcol = col;
//       boolean found = false;
//       while ((!found) && (curcol < str.length())) {
//           char c = str.charAt(curcol);
//           for(int i = 0; i < chs.length; i++) {
//               if (c == chs[i]) {
//                   found = true;
//               }
//           }
//           curcol++;
//       }
//       return curcol;
//   }
   /**
    * Returns the position of the first space at or after position col
    * in str, or str.size() if there is none.
    */
//   private static int NextSpaceCol(String str, int col) {
//      int res = str.indexOf(' ', col);
//      if (res == -1) { return str.length(); };
//      return res;
//   }
   
   /**
    * Returns the position of the first space , ",", or ")" at or after position col
    * in str, or str.size() if there is none.
    */
   private static int NextDelimiterCol(String str, int col) {
       String[] splitStr = str.substring(col).split(" |,|\\)");
       if (splitStr.length == 0) { return col ; }
       return col + splitStr[0].length();
   }
   
   /**
    * Returns the position of the first spaceat or after position col in 
    * str, or str.size() if there is none.
    * @param str
    * @param col
    * @return
    */
   private static int NextSpaceCol(String str, int col) {
       String[] splitStr = str.substring(col).split(" ");
       if (splitStr.length == 0) { return col ; }
       return col + splitStr[0].length();
   }
   
   /**
    * Returns the position of the first "{", "}", quote ("), "(*", or
    * "\*" at or after position col in str, or str.size() if there is
    * none.
    * @param str
    * @param col
    * @return
    */
   private static int NextBraceQuoteOrCommentCol(String str, int col) {
       String[] splitStr = 
           str.substring(col).split("\\{|\\}|\"|\\(\\*|\\\\\\*");
       if (splitStr.length == 0) { return col ; }
       return col + splitStr[0].length();
   }
   
   /**
    * Returns the position of the first character not a letter, number,
    * or "_" at or after position col in str, or str.size() if there is
    * none.
    * @param str
    * @param col
    * @return
    */
   public static int NextNonIdChar(String str, int col) {
       int curCol = col;
       char c = str.charAt(col);
       while ((curCol < str.length()) &&
               (Character.isLetter(c) || Character.isDigit(c) ||
                 (c == '_'))) {
           curCol++;
           if (curCol < str.length()) { c = str.charAt(curCol); }
       }
       return curCol;
   }

   
   /** 
    * This method searches for the next non-space character and sets curLoc to 
    * its location.  If there is no non-space character found, then the location 
    * is set to column 0 of the first row after the end if inputVec.  It returns 
    * the line to which curLoc is pointing to, or "" if loc is after the end of the 
    * Note: it does the right thing if loc is the column after the end of a row.
    * 
    * See the comments above for an explanation of the arguments.  (No comment
    * removal is possible.)
    * 
    */
   public static String GotoNextNonSpace(Vector inputVec, IntPair curLoc) {
       boolean found = false;
       while ((!found) && curLoc.one < inputVec.size()) {
         String line = (String) inputVec.elementAt(curLoc.one);
         while ((!found) && curLoc.two < line.length()) {
             if (line.charAt(curLoc.two) == ' ') {
                 curLoc.two++;
              } else {
                  found = true;
              }
         }
         if (!found) {
//             if (outputVec != null) {
//                 outputVec.addElement(inputVec.elementAt(curLoc.one));
//             }
             curLoc.one++;
             curLoc.two = 0;
         }
       }
       if (curLoc.one < inputVec.size()) {return (String) inputVec.elementAt(curLoc.one);}
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
//   public static String GotoNextNonSpaceOrComment(
//                Vector inputVec, Vector outputVec, IntPair curLoc, 
//                boolean replace)
//            throws ParseAlgorithmException {
//       boolean found = false;
//       while ((!found) && curLoc.one < inputVec.size()) {
//         String curLine = GotoNextNonSpace(inputVec, outputVec, curLoc);
//         char c = curLine.charAt(curLoc.two);
//
//         if (   (c == '(') 
//                    && (curLoc.two + 1 < curLine.length())
//                    && (curLine.charAt(curLoc.two+1) == '*')) {
//             ParseAlgorithm.gotoEndOfComment(inputVec, outputVec, curLoc, replace);
//             curLine = GotoNextNonSpace(inputVec, outputVec, curLoc);
//         } else if (   (c == '\\') 
//                 && (curLoc.two + 1 < curLine.length())
//                 && (curLine.charAt(curLoc.two+1) == '*')) {
//             if (replace) {
//                 inputVec.setElementAt(
//                      curLine.substring(0, curLoc.two), curLoc.one);
//             }
//             curLoc.two = curLine.length();
//         } else {
//             found = true;
//         }
//       }
//       if (curLoc.one < inputVec.size()) {
//           return (String) inputVec.elementAt(curLoc.one);}
//       return "";
//   }

   
   
   /**
    * This method assumes that str is a string whose character at
    * position loc is a quote (").  It returns the position immediately after
    * the matching quote that ends a TLA+ string.  If there is no matching
    * quote, then it throws a ParseAlgorithmException, reporting the error at
    * line line+1, column loc+1
    */
   public static int findEndOfString(String str, int loc, int line) 
     throws ParseAlgorithmException {
       int pos = loc + 1;
       boolean found = false;
       while ((!found) && (pos < str.length())) {
           char c = str.charAt(pos);
           if (c == '"') {
               found = true;
           } else if (c == '\\' && (pos < str.length()-1)) {
               pos++;
           } 
           pos++;
       }
       if (!found) {
           throw new ParseAlgorithmException("Unterminated string begun at line " 
                   + "\n    line " + (line+1) + ", column " + (loc+1)  ) ;
       }
       return pos;
   }
   
   /**
    *  Finds the end of a comment in the String Vector inputVec, assuming
    *  that loc is the location of the "(" in the "(*" that begins the comment,
    *  and advances loc to the position just beyond the end of the closing "*)".
    * 
    * See the comments above for an explanation of the arguments.
    */
   public static void gotoEndOfComment(Vector inputVec,  // Vector of strings
//                                       Vector outputVec, // null or Vector of strings
                                       IntPair curLoc      
                                         // <row, column> in Java coordinates of
                                         // "(*" that begins a comment.
//                                       boolean replace // true iff comment should
                                                       // be replaced by spaces.
                                      )
                        throws ParseAlgorithmException {
       IntPair originalLoc = curLoc ; // value saved for error reporting;
       boolean found = false;
       String curLine = (String) inputVec.elementAt(curLoc.one);

       StringBuffer newLine = new StringBuffer(curLine.substring(0, curLoc.two));
//       if (replace) {
//           newLine.append("  ");
//       }

       curLoc.two = curLoc.two + 2; // skip over "(*"
       
       while ((!found) && (curLoc.one < inputVec.size())) {
           while ((!found) && (curLoc.two < curLine.length())) {
               char c = curLine.charAt(curLoc.two);
               if (    (c == '(') 
                    && (curLoc.two + 1 < curLine.length())
                    && (curLine.charAt(curLoc.two+1) == '*')) {
                   // this character begins an inner comment.
                   // must set inputVec to correct value if replacing
//                   if (replace) {
//                      inputVec.setElementAt(
//                        newLine.append(curLine.substring(curLoc.two)).toString(),
//                                       curLoc.one);
//                   }
                   gotoEndOfComment(inputVec, curLoc);
                   // must reset curLine and newLine
                   curLine = (String) inputVec.elementAt(curLoc.one);
//                   if (replace) {
//                       newLine = new StringBuffer(curLine.substring(0, curLoc.two));
//                   }
               } else if (    (c == '*') 
                          && (curLoc.two + 1 < curLine.length())
                          && (curLine.charAt(curLoc.two+1) == ')')) {
                   // this character begins the comment-ending "*)"
//                   if (replace) {
//                       newLine.append("  ");
//                   }
                   curLoc.two = curLoc.two + 2;
                   found = true;
               } else {
//                   if (replace) {
//                       newLine.append(" ");
//                   }
                   curLoc.two++;
               }
           } // end of loop over characters in curLine
            if (!found) {
//                if (replace)
//                {
//                    inputVec.setElementAt(newLine.toString(), curLoc.one);
//                    newLine = new StringBuffer();
//                }
//                if (outputVec != null)
//                {
//                    outputVec.addElement(inputVec.elementAt(curLoc.one));
//                }
                curLoc.one++;
                curLoc.two = 0;
                if (curLoc.one < inputVec.size()) {
                    curLine = (String) inputVec.elementAt(curLoc.one);
                }
            }
       } // end of while loop over lines.
//      if (found && replace) {
//          newLine.append(curLine.substring(curLoc.two));
//          inputVec.setElementAt(newLine.toString(), curLoc.one);
//      }
      if (!found) {
          throw new ParseAlgorithmException("Unterminated comment begun at line " 
                  + "\n    line " + (curLoc.one+1) + ", column " + (curLoc.two+1)  ) ;
      }
      return;
   }
   
   // Copied from StringHelper
   public static final void printArray(Object[] array) {
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

