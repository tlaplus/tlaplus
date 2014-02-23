// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
//
// last modified on Mon  9 November 2009 at 17:14:53 PST by lamport

//
//  4/9/2006 Added a check in RecordConstructor for duplicate fields
//  ........ Added processing for \exists

// XXXXXXXXXXXXXX THINGS TO DO: see file tla/inria/bugs.txt
////   Fix Bug  9 in tla/inria/bugs.txt
////   Fix Bug 10 in tla/inria/bugs.txt  (this looks easy)
////   
////   Test the implementation of labeling of ASSUME/PROVE nodes.

package tla2sany.semantic;

import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;

import tla2sany.parser.Operators;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParserConstants;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Stack;
import tla2sany.utilities.Strings;
import tla2sany.utilities.Vector;
import tlc2.output.EC;
import tlc2.output.MP;
import util.UniqueString;
import util.WrongInvocationException;



// This class generates a semantic graph from a parse tree. It also uses
// the list of modules to access contexts to instantiate or extend.

// The construction of the graph follows from the grammar and the API.

// The first invocation of the translation of a module is going to be
// done with the global context, which contains external symbols. The
// embedded modules will use the context of the englobing module.

// SymbolTable and Context must be suitably initialized *before*
// generateModule is invoked, since we do not know in which context we
// are working from the inside.

/***************************************************************************
* Only one object of class Generator is ever created--namely, the object   *
* gen in drivers/SANY.java.  So it seems like all fields and methods of    *
* this class could have been made static.                                  *
***************************************************************************/

public class Generator implements ASTConstants, SyntaxTreeConstants,
                                   LevelConstants, TLAplusParserConstants {

  private Context     context;        // current context, not very useful.
  private SymbolTable symbolTable;    // symbol table used throughout the spec.
                                      //   except for embedded modules
    /***********************************************************************
    * A SymbolTable is actually a stack of contexts, where a context is a  *
    * mapping from symbols to their meanings.  Elements are looked up in   *
    * a SymbolTable by going through the stack of contexts from the top    *
    * down.                                                                *
    *                                                                      *
    * symbolTable appears to contain the definitions and declarations of   *
    * all symbols that are currently defined or declared.  When a          *
    * construct containing local definitions or declarations is            *
    * entered--for example, when constructing the ExprNode for a LET/IN,   *
    * a new context is pushed onto symbolTable to hold those local defs    *
    * or decls.  It appears that after the complete semantic ModuleNode    *
    * has been created, symbolTable should contain only a single context,  *
    * which becomes the ModuleNode's context.                              *
    *                                                                      *
    * symbolTable entries are made for SymbolNode objects (objects         *
    * belonging to a subclass of SymbolNode).  It appears that all of      *
    * those objects are added (to the context at the top of the stack)     *
    * symbolTable by the SymbolNode object's constructor.                  *
    ***********************************************************************/

  private ExternalModuleTable moduleTable;
  public  Errors      errors;
  private Stack       excStack;       // Holds stack of OpApplNodes for $Except
                                      //   operators; used for @
  private Stack       excSpecStack;   // Holds stack of OpApplNode for @Pair
                                      //   operators representing ExceptSpecs;
                                      //   also used for @

  // dummy definitions; used during the creation of the "-- TLA+ BUILTINS --" phony module,
  // before real modules are processed; also used somewhat inconsistently to avoid returning
  // null values, and to allow semantic analysis to proceed when an error is detected
  private SubstInNode       nullSubstIn;
  private FormalParamNode[] nullParam;
  private OpDefNode         nullODN;
  protected OpApplNode      nullOAN;
  protected LabelNode       nullLabelNode;
    /***********************************************************************
    * This is a special OpApplNode that gets returned in various places    *
    * when an error is detected.  This allows semantic analysis to         *
    * continue, presumably by preventing a NullPointerException.           *
    ***********************************************************************/
  protected OpArgNode       nullOpArg;

  private final static UniqueString S_e      = UniqueString.uniqueStringOf("\\E");
  private final static UniqueString S_ex     = UniqueString.uniqueStringOf("\\exists");
  private final static UniqueString S_f      = UniqueString.uniqueStringOf("\\A");
  private final static UniqueString S_fx     = UniqueString.uniqueStringOf("\\always");
  private final static UniqueString S_te     = UniqueString.uniqueStringOf("\\EE");
  private final static UniqueString S_tf     = UniqueString.uniqueStringOf("\\AA");
  private final static UniqueString S_a      = UniqueString.uniqueStringOf("<<");
  private final static UniqueString S_brack  = UniqueString.uniqueStringOf("[");
  private final static UniqueString S_sf     = UniqueString.uniqueStringOf("SF_");
  private final static UniqueString S_wf     = UniqueString.uniqueStringOf("WF_");
  private final static UniqueString S_at     = UniqueString.uniqueStringOf("@");
  private final static UniqueString S_lambda = 
                           UniqueString.uniqueStringOf("LAMBDA");
  private final static UniqueString S_subexpression = 
                           UniqueString.uniqueStringOf("$Subexpression");

  class Function {
    /***********************************************************************
    * The only object of this class ever created is `functions', declared  *
    * right after the class definition.  So, I don't know why this         *
    * class's methods weren't just made ordinary methods of the Generator  *
    * class.  Perhaps this was done so the subclass `pair' could be        *
    * defined within it without interfering with any other subclass by     *
    * that name.  However, there is no other subclass by that name in the  *
    * Generator class.                                                     *
    *                                                                      *
    * See the comments attached to the `functions' object for the class's  *
    * explanation.                                                         *
    ***********************************************************************/
    class pair{
      UniqueString a;
      OpApplNode   b;

      pair(UniqueString uniqueString, OpApplNode oan) { a = uniqueString; b = oan; }
      UniqueString uniqueString() { return a; }
      OpApplNode   oan() { return b; }
    }

    Stack funcStack = new Stack();

    void push(UniqueString uniqueString, OpApplNode oan) {
      funcStack.push( new pair(uniqueString, oan) );
    }

    void pop() { funcStack.pop(); }

    // If same function found farther down on stack, then this is a recursive
    // function definition--change the operator to indicate so.
    boolean recursionCheck(UniqueString uniqueString) {
      for (int lvi = funcStack.size()-1; lvi>=0; lvi-- ) { 
        if (uniqueString.equals( ((pair)funcStack.elementAt( lvi )).uniqueString())) {
           // OA-rfs = recursive func spec
           ((pair)funcStack.elementAt(lvi)).oan().resetOperator(OP_rfs); 
           return true;
        }
      }
      return false;
    }

  } // end class Function

  // This is the only instance of class Function

  Function functions = new Function();
    /***********************************************************************
    * This object is used to detect that a function definition is          *
    * recursive.  It is a stack of <<UniqueString, OpApplNode>> pairs.     *
    * An element <<f, opAp>> in the stack indicates that the current node  *
    * being processed is inside the body of a function definition of the   *
    * form f[...] == body.  The current context assigns to f an OpDefNode  *
    * whose body is the OpApplNode opAp whose operator is either           *
    * $RecursiveFcnSpec or $NonRecursiveFcnSpec having (an OpDeclNode      *
    * for) the bound identifier f and having the body of the definition    *
    * as its operand.  The following methods can be applied:               *
    *                                                                      *
    *   functions.push(UniqueString us, OpApplNode oan)                    *
    *      Pushes <<us, oan>> onto the stack.                              *
    *                                                                      *
    *   functions.pop()                                                    *
    *      Pops the last element off the stack.                            *
    *                                                                      *
    *   recursionCheck(UniqueString us)                                    *
    *      If there is a pair <<us, oan>> on the stack, then the           *
    *      operator of oan is set to $RecursiveFcnSpec.                    *
    *                                                                      *
    * An entry for f is pushed on the stack before processing the body     *
    * f's definition, and popped upon return.                              *
    *                                                                      *
    * When processing a FcnAppl syntax nodefor an expression f[...],       *
    * functions.recursionCheck is called to see the node occurs in the     *
    * body of the definition of f, in which case the definition body's     *
    * OpApplNode's operator is changed to indicate that f's definition is  *
    * recursive.                                                           *
    ***********************************************************************/
    


  // This class represents a generalized identifier, e.g. a syntactic 
  // phrase such as A(2)!B(x,y)!C!D(u,v,w)  In this case the compoundID 
  // would be A!B!C!D and the args array would contain [2,x,y]  
  // (i.e. not including u,v,and w, because they are 
  // args to the main operator, and not part of the GenID
  private class GenID {

    private TreeNode          treeNode;      
      // The syntax tree node holding this GenID
    private StringBuffer      compoundID;    
      // The string name of the compound op, with "!"'s, if any
    private Vector            argsVector = new Vector();        
      // Vector of arguments (ExprNodes and OpArgNodes)
      // that are embedded in the generalized identifier

    // The next three fields are null until the finalAppend 
    // method has been called
    private UniqueString      compoundIDUS;      
       // UniqueString version of compoundID
    private SymbolNode        fullyQualifiedOp;  
       // SymbolNode for compoundID
    private ExprOrOpArgNode[] args;              
      // Array with same contents as argsVector

    // Constructor
    public GenID(TreeNode node) {
      treeNode         = node;
      compoundID       = new StringBuffer("");
      compoundIDUS     = null;
      fullyQualifiedOp = null;
      args             = null;
    }

    public final UniqueString getCompoundIDUS() { return compoundIDUS;}

    public final SymbolNode getFullyQualifiedOp() { return fullyQualifiedOp; }

    public final ExprOrOpArgNode[] getArgs() { return args; }

    public final Vector getArgsVector() { return argsVector; }

    /** Append a new segment to the compound name of the operator */
    public final void append(String s) { 
      compoundID.append(s);
    }

    /** Add a new argument to the vector of arguments being constructed */
    public final void addArg(ExprOrOpArgNode arg) {
      argsVector.addElement(arg);
    }

    /**
     * Appends the final element of the fully-qualified name to the
     * GenID that has been being built using addArg() and
     * append(). Since it signals the completion of the construction
     * of the name, this method converts the name from StringBuffer to
     * UniqueString, resolves it to a SymbolNode, and converts the
     * argument list from vector to array form.
     */
    public final void finalAppend(String s, boolean unaryNegKludge) {
      // append the final segment of the compound name
      if (unaryNegKludge && s.equals("-")) {
        compoundID.append("-.");
      }
      else {
        compoundID.append(s);
      }

      // convert the full name to a UniqueString
      compoundIDUS = UniqueString.uniqueStringOf(compoundID.toString());

      // look up the full name in the SymbolTable (may return null)
      fullyQualifiedOp = symbolTable.resolveSymbol(Operators.resolveSynonym(compoundIDUS));

      if (fullyQualifiedOp == null && compoundIDUS != S_at) {
        // if not in the symbol table and not "@", then it is an unresolved symbol
        errors.addError(treeNode.getLocation(),
                        "Could not find declaration or definition of symbol '" +
                        UniqueString.uniqueStringOf(compoundID.toString()) + "'.");
      }
    }

    public final void finalizeID() {
      // copy argsVector contents into args array
      args = new ExprOrOpArgNode[argsVector.size()];

      for (int i = 0; i < args.length; i++) {
        args[i] = (ExprOrOpArgNode)argsVector.elementAt(i);
      }
    }

    /**
     * Special kluge to append a "." to the name of this ID; 
     * should be used ONLY to change unary "-" to "-."
     */
    public final void appendDot() {
      compoundIDUS = UniqueString.uniqueStringOf(compoundIDUS.toString() + ".");
    }

    public final String toString(int n) {
      String ret = "compound ID: " + compoundID.toString() + "\nargs: " + args.length + "\n";
      for (int i = 0; i < args.length; i++) {
        ret += Strings.indent(2,args[i].toString(n));
      }
      return ret;
    }

  } // end GenID


  final UniqueString AtUS    = UniqueString.uniqueStringOf("@") ;
    /***********************************************************************
    * This is needed in a couple of places.  (I didn't notice that this    *
    * is already defined to equal S_at.)                                   *
    ***********************************************************************/

  /*************************************************************************
  * An object of subclass Selector is used to represent a the translation  *
  * of a GeneralId or an OpApplication whose operator is a GeneralId.  It  *
  * contains the data represented in the Subexpression +cal algorithm by   *
  * the arrays ops and args.  For example, the user expression             *
  *                                                                        *
  *   Foo(a,b)!:!(c)                                                       *
  *                                                                        *
  * produces the following in Subexpression algorithm:                     *
  *                                                                        *
  *   ops  = << "Foo",    ":",   "null"    >>                              *
  *   args = << <<a, b>>, << >>,  << <<c>> >>,                             *
  *                                                                        *
  * This is represented by a Selector object with four arrays of           *
  * length 3.  The first is:                                               *
  *                                                                        *
  *   int[] ops with  ops[0] = NameSel                                     *
  *                   ops[1] = ColonSel                                    *
  *                   ops[2] = NullSel                                     *
  *                                                                        *
  * The set of all possible values of ops[i] are:                          *
  *                                                                        *
  *   An integer i >= 0 // Represents the i of  "!i".                      *
  *                                                                        *
  *   One of the following integers < 0.                                   *
  *************************************************************************/

  final int NameSel  = -1 ; // A name like "Foo"  ;
  final int NullSel  = -2 ; // A "(...)" selector ;
  final int GGSel    = -3 ; // ">>" ;
  final int LLSel    = -4 ; // "<<" ;
  final int ColonSel = -5 ; // ":"  ;
  final int AtSel    = -6 ; // "@"  ;
   
  /*************************************************************************
  * The remaining three arrays are:                                        *
  *                                                                        *
  *   SyntaxTreeNode[] opsSTN with values equal to the syntax tree         *
  *                                nodes for the corresponding element     *
  *                                of ops.                                 *
  *                                                                        *
  *   UniqueString[] opNames with opNames[0] = "Foo"                       *
  *                               opNames[1] = ":"                         *
  *                               opNames[2] = null                        *
  *                                                                        *
  *   SyntaxTreeNode[] args with args[0] = "(a, b)"                        *
  *                              args[1] = null                            *
  *                              args[2] = "(c)"                           *
  *                                                                        *
  * Note: we can't turn the arguments into semantic nodes yet because we   *
  * want to use generateExprOrOpArg to do that, which requires that we     *
  * know the operator of which they're the arguments.  Hence, that         *
  * computation has to be folded into the Subexpression algorithm.         *
  *                                                                        *
  * These arrays are initialized by the finish method, which is called     *
  * after all calls of addSelector have been issued.                       *
  *************************************************************************/
  private class Selector {
     /**********************************************************************
     * A single field for the syntax tree node of the entire selector.     *
     **********************************************************************/
     SyntaxTreeNode selSTN ;
          
     /**********************************************************************
     * The fields modified by addSelector:                                 *
     **********************************************************************/
     private Vector opVec    = new Vector(); // of SyntaxTreeNode    ;
     private Vector argVec   = new Vector(); // of SyntaxTreeNode ;

     /**********************************************************************
     * The fields set from opVec and argVec by finalize.                   *
     **********************************************************************/
     int[] ops                = null ;
     UniqueString[] opNames   = null ;
     SyntaxTreeNode[] opsSTN  = null ;    
     SyntaxTreeNode[] args    = null ;

     /**********************************************************************
     * Constants not needed elsewhere.                                     *
     **********************************************************************/
     final UniqueString GGUS    = UniqueString.uniqueStringOf(">>") ;
     final UniqueString LLUS    = UniqueString.uniqueStringOf("<<") ;
     final UniqueString ColonUS = UniqueString.uniqueStringOf(":") ;

     /**********************************************************************
     * The constructor.                                                    *
     **********************************************************************/

     Selector(SyntaxTreeNode tn) {
       selSTN = tn ;
       }     
     void addSelector(SyntaxTreeNode stn, SyntaxTreeNode opargs) {
       /********************************************************************
       * opargs is the args entry.                                         *
       *                                                                   *
       * stn is the syntax tree node representing the ops entry.  If       *
       * there are no arguments, it should be null.  For a NullSel entry   *
       * it should be the OpArgs node (the "(arg1, ...  , argN)") that is  *
       * used as the second argument.                                      *
       ********************************************************************/
       opVec.addElement(stn) ;
       argVec.addElement(opargs) ;
      } // addSelector

     void finish() throws AbortException {
       int arrayLen = opVec.size() ;
       ops     = new int[arrayLen] ;
       opNames = new UniqueString[arrayLen]  ;
       opsSTN  = new SyntaxTreeNode[arrayLen] ;    
       args    = new SyntaxTreeNode[arrayLen] ;    
       for (int i = 0; i < arrayLen; i++) {
         args[i] = (SyntaxTreeNode) argVec.elementAt(i) ;
         SyntaxTreeNode stn = (SyntaxTreeNode) opVec.elementAt(i) ;
         opsSTN[i] = stn ;
         opNames[i] = stn.getUS() ;
         switch (stn.getKind()) {
           case  IDENTIFIER:
           case  N_InfixOp:
           case  N_NonExpPrefixOp:
           case  N_PostfixOp:
           case  N_PrefixOp:
           case  ProofStepLexeme:
// xyz: following case added by LL on 13 Oct 2007
//           
           case  ProofImplicitStepLexeme:
             ops[i] = NameSel ;
           break ;



           case N_StructOp:
             if (stn.heirs().length > 0) {
               /************************************************************
               * This is a number.                                         *
               ************************************************************/
               TreeNode numNode =  stn.heirs()[0].heirs()[0] ;
               ops[i] = Integer.parseInt(numNode.getImage()) ;
               }
             else {
               /************************************************************
               * This is not a number, so it is ">>", "<<", "@", or ":".   *
               ************************************************************/
               UniqueString us = stn.getUS() ;
                 if (us == GGUS)         {ops[i] = GGSel ;}
                 else if (us == LLUS)    {ops[i] = LLSel ;}
                 else if (us == ColonUS) {ops[i] = ColonSel ;}
                 else if (us == AtUS)    {ops[i] = AtSel ; }
                 else { errors.addAbort(
                         stn.getLocation(),
                         "Internal error: Unexpected selector `" + 
                         stn.getImage() + "'.") ;} 
              } // if stn.heirs().length > 0
           break ;

           case N_OpArgs:
              ops[i] = NullSel ;
           break ;

           default:
             /***************************************************************
             * This error occurs on silly input like                        *
             *                                                              *
             *        USE DEF <<1, 2>>                                      *
             *                                                              *
             * It therefore seems better to report a mysterious error and   *
             * let processing continue in the hopes that it will generate   *
             * a later, more useful error.                                  *
             ***************************************************************/
//             errors.addAbort(
             errors.addError(
               stn.getLocation(),
//               "Internal error: Selector had unexpected node kind " + 
//               stn.getKind()) ;
              "Unexpected token found." ) ;
            break ;
          } ;
        } // for
      }

     public String toString() {
       /********************************************************************
       * For debugging.                                                    *
       ********************************************************************/
       String retval = "Selector object:\n" ;
       for (int i = 0; i < ops.length; i++) {
        retval = retval + " elt " + i + " : ops = " + ops[i] + 
                   ", opNames = " + opNames[i].toString() + 
                   ", opsSTN.kind = " + opsSTN[i].getKind() + 
                   ", args.kind = " + 
                      ((args[i] == null)?"null":(args[i].getKind()+" ")) + "\n" ;
        }
       return retval ;
      }

  } // class Selector 

//  private ExprOrOpArgNode[] opArgsToArray(SyntaxTreeNode opArgNode) 
//    /***********************************************************************
//    * Converts an OpArgs node to the array of ExprOrOpArgNodes that it     *
//    * specifies.                                                           *
//    *                                                                      *
//    * opArgNode should be of kind N_OpArgs.                                *
//    ***********************************************************************/
//    throws AbortException {
//      SyntaxTreeNode[] heirs = opArgNode.heirs() ;
//      int arity = (heirs.length - 1) / 2 ;
//      ExprOrOpArgNode[] retval = new ExprOrOpArgNode[arity] ;
//      for (i = 0 ; i < arity ; i++) {
//        retval[i] = generateExprOrOpArg(
//                     ) ;
//       } // for      
//   } //  opArgsToArray

  private Selector genIdToSelector(SyntaxTreeNode genId)
                        throws AbortException {
    /***********************************************************************
    * Constructs a selector in which all the addSelector calls to          *
    * translate the GeneralId node genId have been made and finish has     *
    * been called.                                                         *
    *                                                                      *
    * See the commments in tla+.jj before the OpOrExpr() production to     *
    * see what the tree structure of a GeneralId node looks like.          *
    ***********************************************************************/
    Selector retval = new Selector(genId) ;
    TreeNode prefix = genId.heirs()[0] ;
    TreeNode[] prefixElts = prefix.heirs() ;
    SyntaxTreeNode lastOp = (SyntaxTreeNode) genId.heirs()[1] ;
    for (int i = 0 ; i < prefixElts.length; i++) {
      TreeNode[] pe = prefixElts[i].heirs();
      if (pe.length == 0) { 
        /*******************************************************************
        * We reach this point when processing the nonsensical input        *
        *   HIDE DEF X'                                                    *
        * So we report a not very helpful error in the hopes that further  *
        * processing will produce a more useful error message.             *
        *******************************************************************/
        errors.addError(genId.getLocation(), 
                "Was expecting a GeneralId."); 
        break ;} ;
      SyntaxTreeNode thisPrefix = (SyntaxTreeNode) pe[0] ;
      switch (thisPrefix.getKind()) {
        case N_OpArgs: 
          retval.addSelector(thisPrefix, thisPrefix) ;
        break;   
        case N_StructOp:
          retval.addSelector(thisPrefix, null) ;
        break;   
        default:
          /*****************************************************************
          * This must be an identifier or operator.  It may or may not     *
          * have arguments.                                                *
          *****************************************************************/
          if (prefixElts[i].heirs().length == 2) {
            /***************************************************************
            * There are no arguments (the 2nd heir is the "!").            *
            ***************************************************************/
             retval.addSelector(thisPrefix, null) ;
           }
          else {
            /***************************************************************
            * There are arguments, which are heirs()[1].                   *
            ***************************************************************/
            if (prefixElts[i].heirs().length != 3) {
              errors.addAbort(
                prefixElts[i].getLocation(),
                "Internal error: " + 
                  "IdPrefixElement has other than 2 or 3 heirs.") ;
              } ;
            retval.addSelector(thisPrefix, 
                               (SyntaxTreeNode) prefixElts[i].heirs()[1]) ;
           } // if}           
        break ;
       } // switch
     }; // for i

    if (lastOp.getKind() == N_OpArgs) {retval.addSelector(lastOp, lastOp) ;} 
      else                            {retval.addSelector(lastOp, null) ;} ;

    retval.finish() ;
    return retval ;            
  } // genIdToSelector


  /***********************************************************************
  * Constants for use in selectorToNode.                                 *
  ***********************************************************************/
  private final int FindingOpName   = 11 ;
  private final int FollowingLabels = 22 ;
  private final int FindingSubExpr  = 33 ;

  private final int ArgNum(int op, int arity) {
    /***********************************************************************
    * This is the implementation of ArgNum in Subexpression.tla.  Beware   *
    * that this is the human argument number (where the first argument is  *
    * argument 1), not the Java argument number.                           *
    ***********************************************************************/
    if (op > 0)      {if (op <= arity) {return op;} ;
                      return -1 ;
                      } ;
    if (op == LLSel) {return (arity > 0) ? 1 : -1 ;} ;
    if (op == GGSel) {// if (arity == 1) {return 1;} ;
                      /**************************************************
                      * Commented out on 9 Mar 2010 by LL. Apparently,  *
                      * I once thought it was a good idea to let !>>    *
                      * refer to the argument of a unary operator.  I   *
                      * no longer think so.                             *
                      **************************************************/
                      if (arity == 2) {return 2;} ;
                      } ;
    return -1;
    } // ArgNum

  LevelNode selectorToNode(Selector sel,      // The selector.
                           int expectedArity,
                           boolean isFact,    // true if looking for a fact
                           boolean isDef,     // true if looking for a DEF
                                              //    clause item.
                           ModuleNode cm )    // The current module.
    throws AbortException {
    /***********************************************************************
    * This is an implementation of the +cal algorithm in module            *
    * Subexpression.tla, which is attached as a comment to the end of      *
    * this file.  If expectedArity >= 0, then it returns an                *
    * ExprOrOpArgNode, otherwise it returns an OpDefNode or a              *
    * ThmOrAssumpDefNode.  On an error, it returns nullOAN which will      *
    * allow semantic analysis to continue.                                 *
    *                                                                      *
    * The +cal algorithm describes only the case isFact = false and isDef  *
    * = false.  It should be updated to include the other case as well.    *
    * It also doesn't mention the case of a NumberedProofStepKind OpDef    *
    * node.                                                                *
    *                                                                      *
    * This code was modified on 15 Oct 2007 by LL to allow the use of a    *
    * ModuleInstanceKind node (the M in "M == INSTANCE ...") as a fact or  *
    * a DEF in a BY, USE, or HIDE. Parameterized instances can be used in  *
    * a DEF (without the parameters), but only a non-parameterized module  *
    * instance can be used as a fact.                                      *
    *                                                                      *
    * It appears that, if an error has occurred, a call with               *
    * expectedArity>0 can return something other than an OpArgNode         *
    * (probably an OpApplNode).  This caused a problem in one              *
    * place--namely, in generateOpArg.  I didn't try figuring out whether  *
    * this is actually a bug in selectorToNode.  Instead, I just kludged   *
    * something to handle that case.                                       *
    ***********************************************************************/
    Vector substInPrefix = new Vector() ; // of SubstInNode
    Vector params        = new Vector() ; // of FormalParamNode
    Vector allArgs       = new Vector() ; // of ExprOrOpArgNode

    /***********************************************************************
    * Local algorithm variables.                                           *
    ***********************************************************************/
    UniqueString curName = null ;
    UniqueString newName = null ; // Initial value set to make Eclipse happy.
    SemanticNode curNode = null ;
    SemanticNode newNode ;

    int idx = 0 ;
      /*********************************************************************
      * We use the Java convention of counting from 0 instead of the       *
      * human convention of couunting from 1.                              *
      *********************************************************************/
    int mode = FindingOpName ;
    int prevMode = -999 ; 
      /*********************************************************************
      * The compiler is too dumb to figure out that it always gets set     *
      * before it's used.                                                  *
      *********************************************************************/
    Context letInContext = null ;
      /*********************************************************************
      * This implements the algorithm's curContext variable when that      *
      * context is a LET/IN node's context.  When mode = FindingOpName,    *
      * letInContext is null iff this is the first time that mode is       *
      * entered--i.e., for the name that is the initial part of the        *
      * selector.  In this case, the algorithm's curContext is             *
      * represented by the method's "global variable" symbolTable, since   *
      * any name legal in that context can be referred to.  When mode is   *
      * subsequently set to FindingOpName, it means that the name being    *
      * sought is from a LET/IN node.  In that case, letInContext will     *
      * contain the Context that implements the algorithm's curContext     *
      * variable.                                                          *
      *********************************************************************/
    int opDefArityFound = 0 ;
    Vector opDefArgs = new Vector() ; // of ExprOrOpArgNode objects
    boolean firstFindingOpName = true;
    SymbolNode subExprOf = null;

    boolean inAPsuffices = false ;
      /*********************************************************************
      * Added 16 Feb 2009.  An AssumeProveNode with suffices field true    *
      * represents SUFFICE ASSUME / PROVE, and the SUFFICES is treated as  *
      * if it were a 1-argument operator.  This flag is set true when the  *
      * node is first encountered.                                         *
      *********************************************************************/

    while (idx < sel.args.length) {
      /*********************************************************************
      * Check the one part of the algorithm's assert that should not       *
      * automatically hold -- the first conjunct of the last conjunct --   *
      * for i = idx:                                                       *
      *********************************************************************/
      if (   (   (    (sel.ops[idx] != NameSel)
                  &&  (sel.ops[idx] != NullSel))
              || (expectedArity != 0) )
          && (sel.args[idx] != null)) {
        errors.addError(
           sel.opsSTN[idx].getLocation(),
           "Selector `" + selectorItemToString(sel, idx) + 
           "' should not have argument(s).") ;
        return nullOAN ;
        } // if (sel.ops[idx] == NameSel) ...  ;

      /*********************************************************************
      * Check that, if sel.args[idx] != null, then it is an OpArgs node.   *
      *********************************************************************/
      if (   (sel.args[idx] != null)
          && (sel.args[idx].getKind() != N_OpArgs) ) {
        errors.addAbort(
         sel.args[idx].getLocation(),
         "Internal error: Unexpected syntax node kind.");
        } ;

      switch (mode) {
       case FindingOpName :
         // Following code changed on 23 Sep 2009 to fix bug, and corrected
         // on 9 Nov 2009.  See description in Subexpression.tla.
         SymbolNode newSymbolNode = null;
         Vector tempArgs = new Vector() ; 
           // a vector of SyntaxTreeNode objects, one for each argument
           // found for an undefined operator name in the following loop
                   
         while (newSymbolNode == null && idx < sel.args.length) {
         /******************************************************************
         * +cal: newName := IF IsName(ops[idx]) ... ELSE null ;            *
         ******************************************************************/
         if (sel.ops[idx] == NameSel) {
           if (curName == null) { 
             newName = Operators.resolveSynonym(sel.opNames[idx]) ; 
               /************************************************************
               * Need to call resolveSynonym so things like (+), aka       *
               * \oplus, are handled properly.                             *
               ************************************************************/
            }  
           else { newName = 
                   UniqueString.uniqueStringOf(
                    curName.toString() + "!" + 
                      Operators.resolveSynonym(sel.opNames[idx]).toString()) ;
            } ;
          } // if (sel.ops[idx] = NameSel) 
         else { newName = null ; } ;

         if (    (curName == null)
              && (sel.ops[idx] != NameSel)) {
           if (idx == 0) { errors.addError(
                             sel.opsSTN[idx].getLocation(),
                             "Need name or step number here, not `" +
                              sel.opNames[idx] + "'.") ;
                           return nullOAN ; }
           else {errors.addAbort(sel.opsSTN[idx].getLocation(),
                         "Internal error: should have name here.") ;
            } ;
           } ; // if (curName == null) ...  ;
           if (newName != null) {
               if (letInContext == null) {
                 /***************************************************************
                 * See the comments for the declaration of letInContext.        *
                 ***************************************************************/
                 newSymbolNode = symbolTable.resolveSymbol(newName) ;
                }
               else {
                 newSymbolNode = letInContext.getSymbol(newName) ;
                } ;
               } ; // if (newName != null) 
          if (newSymbolNode == null) {
              curName = newName;
              if (sel.args[idx] != null) {
                  // sel.args[idx].heirs() is the array of SyntaxTreeNode objects
                  // representing:
                  //   "("   "arg1"   ","  ... ","  "arg_n"  ")"
                  // We add these SyntaxTreeNode objects to tempArgs.
                  int numOfOpArgs = (sel.args[idx].heirs().length - 1) / 2 ;
                  for (int i = 0 ; i < numOfOpArgs; i++) {
                      tempArgs.addElement(sel.args[idx].heirs()[2*i+1]);
                  }
              }
              idx++;
          }
         } // while (newNode == null)

         if (newSymbolNode == null) {
           int eidx = (idx < sel.args.length) ? idx : (sel.args.length-1);
           errors.addError(
               sel.opsSTN[eidx].getLocation(),
               "Unknown operator: `" + 
               selectorItemToString(sel, eidx) + "'.") ;
           return nullOAN ; 
          } ; 
        
         if (newSymbolNode.getKind() == ModuleKind) {
             errors.addError(
               sel.opsSTN[idx].getLocation(),
               "Module name (" + sel.opNames[idx].toString() +
               ") not allowed here.") ;
             return nullOAN ; 
           } ; // if 
            
         curNode = newSymbolNode ;
         SymbolNode curSymbolNode = newSymbolNode ;
           /****************************************************************
           * A version of curNode "cast" as a SymbolNode.                  *
           ****************************************************************/
         curName = newName ;
         switch (curSymbolNode.getKind()) {
           case ConstantDeclKind: 
           case VariableDeclKind:
           case FormalParamKind:
           case BuiltInKind:
           case NewConstantKind:
           case NewVariableKind:
           case NewStateKind:
           case NewActionKind:
           case NewTemporalKind:
           case NumberedProofStepKind:
             /**************************************************************
             * This last case added by LL on 17 Aug 2007.  I think it      *
             * fits in here nicely, but I wouldn't swear to it.            *
             **************************************************************/
             if (idx != 0) {
               errors.addAbort(
                 sel.selSTN.getLocation(),
                 "Internal error: impossible naming of declaration.") ;
               }
             else if (sel.ops.length != 1) {
               errors.addError(
                 sel.opsSTN[idx].getLocation(),
                 "Cannot take subexpression of `" + curName.toString() 
                  + "'.") ;
               return nullOAN ; 
            } //  ;

           /****************************************************************
           * Warning: horrible Java programming hack.  There is            *
           * deliberately no break here, so this case "joins" the          *
           * following case.                                               *
           ****************************************************************/
           //$FALL-THROUGH$
           case UserDefinedOpKind:
           case ThmOrAssumpDefKind:
           case ModuleInstanceKind:
             /**************************************************************
             * +cal: nodeArity := Arity(curNode) ;                         *
             **************************************************************/
             int nodeArity = curSymbolNode.getArity() ;
             /**************************************************************
             * +cal: if expectedArity = 0                                  *
             **************************************************************/
             if (expectedArity == 0) {
               SyntaxTreeNode opArgs = sel.args[idx] ;
               int numOfOpArgs = 0 ;
               if (opArgs != null) { 
                   // if there are arguments, add them to tempArgs. 
                   /**********************************************************
                   * The heirs of an oparg node are                          *
                   *                                                         *
                   *     "("   "arg1"   ","  ... ","  "arg_n"  ")"           *
                   **********************************************************/
                   numOfOpArgs = (opArgs.heirs().length - 1) / 2 ;
                    for (int i = 0 ; i < numOfOpArgs; i++) {
                        tempArgs.addElement(sel.args[idx].heirs()[2*i+1]);
                 } ;

               };
               /**************************************************************
               * +cal  then if opDefArityFound + Len(tempArgs) # nodeArity  *
               **************************************************************/
               if (opDefArityFound + tempArgs.size() != nodeArity) {
                 errors.addError(
                    (opArgs == null)? sel.selSTN.getLocation() :
                                      sel.args[idx].getLocation(),
                    "The operator " + curName.toString() + " requires " + 
                    (nodeArity - opDefArityFound) + " arguments.") ;
                 return nullOAN ;
                 } ; // if
               ExprOrOpArgNode[] opArgNodes = 
                                   new ExprOrOpArgNode[tempArgs.size()] ;
                 /**********************************************************
                 * The array of semantic nodes generated by the arguments. *
                 **********************************************************/
               for (int i = 0 ; i < tempArgs.size(); i++) {
                 /**********************************************************
                 * Call generateExprOrOpArg to generate the semantic       *
                 * nodes for the arguments and add them to the vector      *
                 * opDefArgs.  Note that curSymbolNode is used as the      *
                 * argument to generateExprOrOpArg that specifies the      *
                 * operator to which the arguments are being given.  (The  *
                 * comments for that method assumes that the operator      *
                 * arguments appear in an OpApplication node, but the      *
                 * method doesn't really care; it just uses that operator  *
                 * to check the arity of the arguments.)  Note that        *
                 * argument number i of sel.args[idx] represents argument  *
                 * number i + opDefArityFound of the operator described    *
                 * by curSymbolNode.                                       *
                 **********************************************************/
                 opDefArgs.addElement( 
                   generateExprOrOpArg(
                     curSymbolNode,
                     sel.opsSTN[idx],
                     i + opDefArityFound,
                     (TreeNode) tempArgs.elementAt(i),
                     cm));
                } ; // end for
  
              } // if expectedArity = 0
             /**************************************************************
             * +cal: else if expectedArity > 0)                            *
             **************************************************************/
             else {
               if (expectedArity > 0) {
                 /**********************************************************
                 * Subexpression.tla has a test to report an error if a    *
                 * higher-order operator is specified, since such an       *
                 * operator can't be used as an operator argument.  That   *
                 * test is eliminated here because this error should be    *
                 * caught by the caller of the selectorToNode method.      *
                 **********************************************************/
                } 
              } ; // else [expectedArity != 0]
           opDefArityFound = nodeArity ;
  
           if (curNode.getKind() == ModuleInstanceKind) {
             if ((idx == sel.ops.length - 1) && ! (isDef || isFact)) {
               errors.addError(
                 sel.opsSTN[idx].getLocation(),
                 "Operator name " + curName.toString()  + " is incomplete.");
               return nullOAN ; 
               };
            }
           else { 
             /**************************************************************
             * curNode.getKind() \in                                       *
             *      {UserDefinedOpKind, ThmOrAssumpDefKind,                *
             *       ConstantDeclKind, VariableDeclKind, FormalParamKind,  *
             *       BuiltInKind, BoundSymbolKind, NumberedProofStepKind}  *
             **************************************************************/
             /**************************************************************
             * +cal: then if /\ curNode.kind = UserDefinedOpKind ...       *
             **************************************************************/
             if (   (curNode.getKind() == UserDefinedOpKind)
                 && ( ! ((OpDefNode) curNode).isDefined )
                 && (sel.ops.length != 1)) {
               errors.addError(
                 sel.opsSTN[idx].getLocation(),
                 "Subexpression of  `" + curName.toString()  + 
                  "' used inside the operator's definition.");
               return nullOAN ; 
               } ;

             /**************************************************************
             * +cal: if /\ firstFindingOpName ...                          *
             **************************************************************/
             if (   firstFindingOpName
                 && (   (curNode.getKind() == UserDefinedOpKind)
                     || (curNode.getKind() == ThmOrAssumpDefKind))) {
               subExprOf = (SymbolNode) curNode;
              }
             /**************************************************************
             * +cal: idx # Len(ops)                                        *
             **************************************************************/
             if (idx != sel.ops.length - 1) {
               FormalParamNode[] opParams ;
               if (curNode.getKind() == UserDefinedOpKind) {
                 opParams = ((OpDefNode) curNode).getParams() ;
                 newNode = ((OpDefNode) curNode).getBody() ;
                 } // if
                else { // curNode.getKind() == ThmOrAssumpDefKind
                 opParams = ((ThmOrAssumpDefNode) curNode).getParams() ;
                 newNode = ((ThmOrAssumpDefNode) curNode).getBody() ;
                } ;
               for (int i = 0 ; i < opParams.length ; i++) {
                 params.addElement(opParams[i]) ;
                 } ; // for
               curName = null ;
               if (sel.ops[idx+1] == NameSel) {mode = FollowingLabels; }
                else {mode = FindingSubExpr ;} ;
               for (int i = 0 ; i < opDefArgs.size() ; i++) {
                 allArgs.addElement(opDefArgs.elementAt(i)) ;
                 } ; // for
               opDefArityFound = 0;
               opDefArgs = new Vector() ;

               /************************************************************
               * If newNode = null, then I think there's an error.  It     *
               * should be caught later.                                   *
               ************************************************************/
               if (newNode != null) {
                 while (newNode.getKind() == SubstInKind) {
                   substInPrefix.addElement(newNode) ;
                   newNode = ((SubstInNode) newNode).getBody() ;
                   }; // while
                   while (newNode.getKind() == APSubstInKind) {
                       substInPrefix.addElement(newNode) ;
                       newNode = ((APSubstInNode) newNode).getBody() ;
                       }; // while
                } ;
               if (mode == FindingSubExpr) {
                 curNode = newNode ;
                } ;
              } // if (idx != sel.ops.length - 1) 
             } // else curNode.getKind() \in {UserDefinedOpKind, ...}
            prevMode = FindingOpName ;
         break ; 

         default:
           errors.addAbort(sel.opsSTN[idx].getLocation(),
                          "Internal error: unexpected node kind.") ;
         break ;
        } ; // switch (curSymbolNode.getKind())

       break ; // case FindingOpName 


       case FollowingLabels :
         /******************************************************************
         * Invariant: sel.ops[idx] = NameSel                               *
         ******************************************************************/
         if (   (   (prevMode == FindingOpName) 
                 && (curNode.getKind() != UserDefinedOpKind)
                 && (curNode.getKind() != ThmOrAssumpDefKind))
             || (   (prevMode != FindingOpName) 
                 && (curNode.getKind() != LabelKind))) {
             errors.addAbort(sel.selSTN.getLocation(),
                            "Unexpected node kind in FollowingLabels mode.") ;
          } ;

         LabelNode newLabelNode = 
            ((OpDefOrLabelNode) curNode).getLabel(sel.opNames[idx]) ;

         if (newLabelNode == null) {
           errors.addError(
                 sel.opsSTN[idx].getLocation(),
                 "Cannot find label `" + sel.opNames[idx].toString() + "'.");
           return nullOAN ; 
          } ;

         curNode = newLabelNode ;
 
         if (illegalLabelRef(newLabelNode, sel.opsSTN[idx])) {
           errors.addError(
                 sel.opsSTN[idx].getLocation(),
                 "Accessing subexpression labeled `" + 
                 sel.opNames[idx].toString() + 
                 "' of ASSUME/PROVE clause within the scope of " +
                 "a declaration\n from outside that declaration's scope.");
           return nullOAN ; 
          } ;

         if (expectedArity == 0) {

           /****************************************************************
           * Check that label has right number of arguments.               *
           ****************************************************************/
           if (newLabelNode.getArity() !=
                ((sel.args[idx] == null) 
                   ? 0 
                   : (sel.args[idx].heirs().length-1)/2)) {
             errors.addError(
                 sel.opsSTN[idx].getLocation(),
                 "Label `" + sel.opNames[idx].toString() 
                   + "' used with wrong number of arguments.");
             return nullOAN ; 
            } ;      
          for (int i = 0; i < newLabelNode.getArity(); i++) {
            allArgs.addElement(generateExpression(
                                 sel.args[idx].heirs()[2 * i + 1] , cm)) ;
           } ;
          }; // if (expectedArity == 0)

         for (int i = 0; i < newLabelNode.getArity(); i++) {
            FormalParamNode pdecl = newLabelNode.params[i] ;
            params.addElement(pdecl);
           } ;

         if ((idx < sel.ops.length - 1) && (sel.ops[idx+1] != NameSel)) {
           mode = FindingSubExpr ;
           } ; 

         if ((mode == FindingSubExpr) || (idx == sel.ops.length)) {
           curNode = newLabelNode.getBody() ;
           } ;

         prevMode = FollowingLabels ;
       break ; // case FollowingLabels

       case FindingSubExpr:
         if (sel.ops[idx] == ColonSel) {
           if ( (prevMode == FindingSubExpr)
               || ! (   (   (idx == sel.ops.length - 1)
                         && (prevMode == FindingOpName))
                     || (   (idx < sel.ops.length - 1)
                         && (sel.ops[idx+1] == NameSel)))) {
             errors.addError(
                sel.opsSTN[idx].getLocation(),
                "`!:' can be used only after a name and either at the " +
                   "end after an\noperator name or before an operator name.");
             return nullOAN ; 
            } // if ( (prevMode == FindingSubExpr) ...)
          } // if (sel.ops[idx] == ColonSel)
         else if (curNode == null) {
           errors.addError(sel.opsSTN[idx].getLocation(),
                "Subexpression selection failed, probably due to " +
                "an error in the selected expression.");
           return nullOAN ; 
           }
         else if (curNode.getKind() == LetInKind) {
           if (ArgNum(sel.ops[idx], 1) == 1) {
             curNode = ((LetInNode) curNode).getBody() ;
            } else {
             errors.addError(sel.opsSTN[idx].getLocation(),
                             "A LET/IN expression has only one operand.");
             return nullOAN ; 
            } ;
          } // else if (curNode.getKind() == LetInKind) 

         else if (curNode.getKind() == OpApplKind) {         
           OpApplNode curOpApplNode = (OpApplNode) curNode ;
           ExprOrOpArgNode[] curArgs = curOpApplNode.getArgs() ;
           SymbolNode opNode = curOpApplNode.getOperator();
           if (   (opNode.getKind() == FormalParamKind)
               || (opNode.getKind() == ConstantDeclKind)
               || (opNode.getKind() == UserDefinedOpKind)) {
             int temp = ArgNum(sel.ops[idx], opNode.getArity()) ;
             if (temp == -1) {
                 reportSelectorError(sel, idx) ;
//               errors.addError(sel.opsSTN[idx].getLocation(),
//                               "NoNexistent operand specified by `"
//                                + sel.opNames[idx].toString() + "'.");
               return nullOAN ; 
               } ;
             curNode = curArgs[temp-1] ;
             } // if (opNode.getKind() == FormalParamKind) || ...

           else if (opNode.getKind() == BuiltInKind) {
             if (   (opNode.getName() == OP_rc)      // $RcdConstructor
                 || (opNode.getName() == OP_sor)){   // $SetOfRcds
               
               int temp = ArgNum(sel.ops[idx], curArgs.length) ;
               if (temp == -1) {
//                 errors.addError(sel.opsSTN[idx].getLocation(),
//                                 "NonExistent operand specified by `"
//                                  + sel.opNames[idx].toString() + "'.");
                 reportSelectorError(sel, idx) ;
                 return nullOAN ; 
                } ;
               curOpApplNode = (OpApplNode) curArgs[temp-1] ;
               if (curOpApplNode.getOperator().getName() != OP_pair) {
                 errors.addAbort(
                   sel.opsSTN[idx].getLocation(),
                   "Internal error: Expecting $Pair and didn't find it.") ;
                  } ;
               curNode = curOpApplNode.getArgs()[1] ;
              } // if opNode.name == $RcdConstructor or $SetOfRcds

             else if (opNode.getName() == OP_case) { //$Case 
               if (idx == sel.ops.length - 1) {
                 errors.addError(
                    sel.opsSTN[idx].getLocation(),
                    "Subexpression of CASE must have form !i!j.");
                 return nullOAN ; 
                } ;
               int temp = ArgNum(sel.ops[idx], curArgs.length) ;
               if (temp == -1) {
                 reportSelectorError(sel, idx) ;
                 return nullOAN ; 
                } ;
               curOpApplNode = (OpApplNode) curArgs[temp-1] ;
               if (curOpApplNode.getOperator().getName() != OP_pair) {
                 errors.addAbort(
                   sel.opsSTN[idx].getLocation(),
                   "Internal error: Expecting $Pair and didn't find it.") ;
                  } ;
               idx = idx + 1;
               temp = ArgNum(sel.ops[idx], 2) ;
               if (temp == -1) {
                 errors.addError(
                   sel.opsSTN[idx].getLocation(),
                   "Second selector for CASE subexpression must specify "
                    + " one of two operands.");
                 return nullOAN ; 
                } ;
               curNode = curOpApplNode.getArgs()[temp-1] ;
               if (curNode == null) {
                 errors.addError(
                   sel.opsSTN[idx].getLocation(),
                   "Selecting OTHER in a CASE statement.");
                 return nullOAN ; 
                 } ;
              }  // if opNode.name = $Case

             else if (opNode.getName() == OP_exc) { //$Except
               /************************************************************
               * In an $Except node representing                           *
               *                                                           *
               *   [exp_1 ELSE !... = exp_2, ..., !... = exp_n]            *
               *                                                           *
               * operand i names exp_i.                                    *
               ************************************************************/
               int temp = ArgNum(sel.ops[idx], curArgs.length) ;
               if (temp == -1) {
                 reportSelectorError(sel, idx) ;
                 return nullOAN ; 
                } ;
               /************************************************************
               * Selection of subexpressions of EXCEPT have been outlawed  *
               * because they may contain a dangling "@".  This doesn't    *
               * seem to be worth fixing because it's unlikely that        *
               * anyone will actually want to refer to such a              *
               * subexpression.                                            *
               * Change made 25 Oct 2007.                                  *
               ************************************************************/
               if (temp > 1) {
                 errors.addError(
                   sel.opsSTN[idx].getLocation(),
                   "Selecting subexpression of an " + 
                     "EXCEPT not yet implemented.");
                 return nullOAN ; 
                 } ;
               curNode = curArgs[temp-1];
               if (isNullSelection(curNode, sel, idx))
                 { return nullOAN ; } ;
               if (temp > 1) {
                 curOpApplNode = (OpApplNode) curNode ;
                 if (curOpApplNode.getOperator().getName() != OP_pair) {
                   errors.addAbort(
                     sel.opsSTN[idx].getLocation(),
                     "Internal error: Expecting $Pair and didn't find it.") ;
                    } ;
                 curNode = curOpApplNode.getArgs()[1] ;
                }; // if (temp > 1) 
              }  // if opNode.name = $Except

             else { // Handled by standard procedure 
               if (   (curOpApplNode.getNumberOfBoundedBoundSymbols() == 0)
                   && (   (curOpApplNode.getUnbdedQuantSymbols() == null) 
                       || (curOpApplNode.getUnbdedQuantSymbols().length 
                            == 0) )  
                      /*****************************************************
                      * I'm not sure getUnbdedQuantSymbols always returns  *
                      * null if there are no such symbols.                 *
                      *****************************************************/
                   ) {
                 /**********************************************************
                 * Current subexpression has no bound variables.           *
                 **********************************************************/
                 int temp = ArgNum(sel.ops[idx],
                                   curOpApplNode.getArgs().length) ;
                 if (temp == -1) {
                 reportSelectorError(sel, idx) ;
                 return nullOAN ; 
                  } ;
                 curNode = curOpApplNode.getArgs()[temp-1] ;
                } // if current subexpression has no bound variables
               else {
                 /**********************************************************
                 * Current subexpression has bound variables.              *
                 **********************************************************/
                 if (   (sel.ops[idx] == NullSel)
                     || (sel.ops[idx] == AtSel))  {
                   /********************************************************
                   * Set temp to the array of FormalParamNodes for the     *
                   * parameters.                                           *
                   ********************************************************/
                   FormalParamNode[] temp ;
                   if (curOpApplNode.getNumberOfBoundedBoundSymbols() > 0) {
                     FormalParamNode[][] symbs = 
                             curOpApplNode.getBdedQuantSymbolLists() ;
                     int numSymbs = 0 ;
                     for (int i = 0 ; i < symbs.length ; i++) {
                       numSymbs = numSymbs + symbs[i].length ;
                      }; // for
                     temp = new FormalParamNode[numSymbs] ;
                     int k = 0 ;
                     for (int i = 0 ; i < symbs.length ; i++) {
                       for (int j = 0 ; j < symbs[i].length ; j++) {
                         temp[k] = symbs[i][j] ;
                         k++;
                        }; // for j
                      }; // for i
                    } // if (curOpApplNode.getNumberOf... > 0) 
                   else {
                     temp = curOpApplNode.getUnbdedQuantSymbols() ;
                    } ; // else not (curOpApplNode.getNumberOf... > 0) 

                    /*******************************************************
                    * Add the elements of temp to the params vector.       *
                    *******************************************************/
                    for (int i = 0 ; i < temp.length ; i++) {
                      params.addElement(temp[i]) ;
                     } ; // for i

                    if (sel.ops[idx] == NullSel) {
                      /*****************************************************
                      * Add the arguments to allArgs, checking if there    *
                      * are the right number.                              *
                      *****************************************************/
                      int numOfArgs = (sel.args[idx].heirs().length-1)/2 ;
                      if ( temp.length != numOfArgs) {
                        errors.addError(
                           sel.opsSTN[idx].getLocation(),
                           "Selector with " + numOfArgs + 
                            " argument(s) used for quantifier with "  +
                            temp.length + " bound identifier(s).");
                        return nullOAN ; 
                       } ;
                      for (int i = 0; i < numOfArgs; i++) {
                        allArgs.addElement(
                                  generateExpression(
                                    sel.args[idx].heirs()[2 * i + 1] , cm)) ;
                       } ; // for i
                     } ; // if (sel.ops[idx] == NullSel)
                    curNode = curOpApplNode.getArgs()[0] ;
                  } // if (sel.ops[idx] == NullSel) || ...
                 else {
                   int temp = ArgNum(
                                sel.ops[idx], 
                                curOpApplNode.getBdedQuantBounds().length);
                   if (temp == -1) {
                     reportSelectorError(sel, idx) ;
                     return nullOAN ; 
                    } ;
                   curNode = curOpApplNode.getBdedQuantBounds()[temp-1] ;
                  }; // else
                }; // else Current subexpression has bound variables
              }; // Handled by standard procedure 
             } // else if (opNode.getKind() == BuiltInKind)

           else {
             errors.addError(
                sel.opsSTN[idx].getLocation(),
                "Choosing operand `" + selectorItemToString(sel, idx) + 
                "' of subexpression with no operands." );
             return nullOAN ; 
            } ;

          } // else if ((curNode.getKind() == OpApplKind) 

         else if (curNode.getKind() == AssumeProveKind) { 
           AssumeProveNode curAPNode = (AssumeProveNode) curNode;

           /****************************************************************
           * 16 Feb 2009: Case of curAPNode.suffices true added.           *
           ****************************************************************/
           if (   (curAPNode.isSuffices()) 
               && (! inAPsuffices) )   {
             /**************************************************************
             * In this case, the selector must be 1, and the curNode is    *
             * left equal to the AssumeProve, but with inAPsuffices set    *
             * to true.                                                    *
             **************************************************************/
             if (ArgNum(sel.ops[idx], 1) != 1) {
               errors.addError(sel.opsSTN[idx].getLocation(),
                    "Accessing non-existent subexpression of " +
                     "a SUFFICES");
               return nullOAN ; 
              };
             inAPsuffices = true ;             
             } // if (curAPNode.isSuffices())
           else {
             inAPsuffices = false;
               /************************************************************
               * Added 16 Feb 2009 by LL.                                  *
               ************************************************************/
             int temp = ArgNum(sel.ops[idx], 
                               1 + curAPNode.getAssumes().length);
             if (temp == -1) {
               reportSelectorError(sel, idx) ;
               return nullOAN ; 
              } ;
  
             if (illegalAPPosRef(curAPNode, temp)){
               errors.addError(sel.opsSTN[idx].getLocation(),
                    "Accessing ASSUME/PROVE clause within the scope of " +
                   "a declaration\n from outside that declaration's scope.");
               return nullOAN ; 
               } ;
             if (temp <= curAPNode.getAssumes().length) {
               curNode = curAPNode.getAssumes()[temp-1] ;                 
               if (isNullSelection(curNode, sel, idx)) { return nullOAN; } ;
               if (   (curNode.getKind() == NewSymbKind)
                   && (idx != sel.args.length-1)) {
                 /************************************************************
                 * Extra conjunct added to if test to allow selection of a   *
                 * NEW clause as a fact.                                     *
                 ************************************************************/
                 errors.addError(
                    sel.opsSTN[idx].getLocation(),
                    "Selected a subexpression of a NEW clause of an ASSUME.");
                 return nullOAN ; 
                }
              }
             else {
               curNode = curAPNode.getProve() ;
             };
           } // else if (curAPNode.isSuffices())
          } // else if (curNode.getKind() == AssumeProveKind) 

         else if (curNode.getKind() == OpArgKind) { 
           SymbolNode opNode = ((OpArgNode) curNode).getOp() ;
           if (   (opNode.getKind() != UserDefinedOpKind)
               || (opNode.getName() !=S_lambda)) {
             errors.addError(
                sel.opsSTN[idx].getLocation(),
                "Trying to select subexpression of an operator argument.");
             return nullOAN ; 
            } ;
           OpDefNode opDefOpNode = (OpDefNode) opNode ;
           if (   (sel.ops[idx] != NullSel)
               && (sel.ops[idx] != AtSel)) {
             errors.addError(
                sel.opsSTN[idx].getLocation(),
                "Cannot use !" + sel.opNames[idx].toString() +
                " to select subexpression of a LAMBDA.");
             return nullOAN ; 
             } ;
           if (sel.ops[idx] == NullSel) {
             int numOfArgs = (sel.args[idx].heirs().length-1)/2 ;
             if (opDefOpNode.getArity() != numOfArgs) {
               errors.addError(
                  sel.opsSTN[idx].getLocation(),
                  "Selector with " + numOfArgs + 
                   "arguments used for LAMBDA expression taking "  +
                   opDefOpNode.getArity() + " arguments.");
               return nullOAN ; 
              } ;
             for (int i = 0; i < numOfArgs; i++) {
               allArgs.addElement(generateExpression(
                                  sel.args[idx].heirs()[2 * i + 1] , cm)) ;
              } ;
             } ; // if (sel.ops[idx] == NullSel)
            for (int i = 0; i < opDefOpNode.getArity(); i++) {
              params.addElement(opDefOpNode.getParams()[i]) ;
             } ;
            curNode = opDefOpNode.getBody() ;
          } // else if (curNode.getKind() == OpArgKind) 

         else if (   (curNode.getKind() == UserDefinedOpKind) 
                  || (curNode.getKind() == BuiltInKind)
                  || (curNode.getKind() == NumberedProofStepKind)) { 
              errors.addAbort(
                sel.opsSTN[idx].getLocation(),
                "Internal error: " +
                " Should not have been able to select this node.") ;
          } // else if (curNode.getKind() == UserDefinedOpKind) || ...

         else if (   (curNode.getKind() == AtNodeKind) 
                  || (curNode.getKind() == DecimalKind) 
                  || (curNode.getKind() == NumeralKind) 
                  || (curNode.getKind() == StringKind) 
                  || (curNode.getKind() == FormalParamKind) 
                  || (curNode.getKind() == ConstantDeclKind) 
                  || (curNode.getKind() == VariableDeclKind) 
                  || (curNode.getKind() == BoundSymbolKind) ) { 
              errors.addError(
                sel.opsSTN[idx].getLocation(),
                "Selecting subexpression of expression that has none.") ;
              return nullOAN ;
          } // else if (curNode.getKind() == AtNodeKind) || ...

         else if (curNode.getKind() == LabelKind) { 
           curNode = ((LabelNode) curNode).getBody() ;
           idx = idx - 1;
          } // else if (curNode.getKind() == LabelKind) 

         else { 
           errors.addAbort(
             sel.opsSTN[idx].getLocation(),
             "Internal error: " +
              " Unknown node kind.") ;
          } ; // end last else of if sel.ops[idx] != ColonSel

         if (isNullSelection(curNode, sel, idx)) { return nullOAN; } ;

         if (idx != sel.ops.length - 1) {
           if (sel.ops[idx+1] == NameSel) {
             while (curNode.getKind() == LabelKind) {
               curNode = ((LabelNode) curNode).getBody();
               if (isNullSelection(curNode, sel, idx)) { return nullOAN; } ;
              }; // while
             if (curNode.getKind() == LetInKind) {
               letInContext = ((LetInNode) curNode).context ;
               mode = FindingOpName ;
               firstFindingOpName = false;
              } 
             else {
               errors.addError(
                 sel.opsSTN[idx].getLocation(),
                 "A name selector here must be from a LET clause.") ;
               return nullOAN ;
              }
            } // if (sel.ops[idx+1] == NameSel) 
           else if (sel.ops[idx+1] == ColonSel) {
             errors.addError(
                 sel.opsSTN[idx].getLocation(),
                 "!: should not follow an operand selector.") ;
             return nullOAN ;
              }
          } ; // if (idx != sel.ops.length - 1)

         prevMode = FindingSubExpr ;
       break ; // case FindingSubExpr

       default:
         errors.addAbort(sel.selSTN.getLocation(),
                         "Internal error: Unexpected mode") ;
       } // switch (mode)
      idx++ ;
     } // while idx < 
     /**********************************************************************
     * +cal: end while ;                                                   *
     **********************************************************************/

    /***********************************************************************
    * +cal: if curNode.kind = AssumeProveKind ... end if                   *
    *                                                                      *
    * Modified 17 Feb 2009 by LL to allow ASSUME/PROVE to be used as a     *
    * fact.  This seems to have been a bug in the original.                *
    *                                                                      *
    * Not corrected in the PlusCal code because that code doesn't talk     *
    * about the isFact case.                                               *
    ***********************************************************************/
    if (curNode.getKind() == AssumeProveKind) {
      if (isFact) { return (AssumeProveNode) curNode ; };
      errors.addError(
               sel.selSTN.getLocation(),
               "Selected ASSUME/PROVE instead of expression.") ;
             return nullOAN ; 
     } ;

    /***********************************************************************
    * The following added to allow naming of NEW constructs of an          *
    * ASSUME/PROVE in facts.                                               *
    ***********************************************************************/
    if (curNode.getKind() == NewSymbKind) {
      if (isFact) { return (LevelNode) curNode ; } ;
      errors.addError(
         sel.selSTN.getLocation(), 
         "Selected a NEW declaration as an expression or operator.") ;
      return nullOAN ;
     } ;
    
    /***********************************************************************
    * +cal: if expectedArity < 0  ... end if;                              *
    ***********************************************************************/
    if (expectedArity < 0) {
      if (    (prevMode != FindingOpName)
          || !(   (curNode.getKind() == UserDefinedOpKind)
               || (curNode.getKind() == ThmOrAssumpDefKind)
               || (curNode.getKind() == NumberedProofStepKind)
               || // This clause added by LL 15 Oct 2007, not in +cal code
                  (   (curNode.getKind() == ModuleInstanceKind)
                   && isDef))) {
            errors.addError(
              sel.selSTN.getLocation(), 
              "DEF clause entry should describe a defined operator.") ;
            return nullOAN ;
       } ; 
      if (   (curNode.getKind() == NumberedProofStepKind)
          && (((OpDefNode) curNode).getStepNode().getKind() != DefStepKind)) {
         errors.addError(
           sel.selSTN.getLocation(), 
           "DEF clause entry refers to a non-definition step.") ;
          return nullOAN ;
       }
      return (LevelNode) curNode;
     }; // if (expectedArity < 0)

    if (curNode.getKind() == NumberedProofStepKind) {
         errors.addError(
           sel.selSTN.getLocation(), 
           isFact ? "Step number of non-fact used as a fact"
             : "Step number of non-expression step used as an expression.") ;
          return nullOAN ;
      }

    /***********************************************************************
    * +cal: if expectedArity > 0 ... end if                                *
    ***********************************************************************/
    if (expectedArity > 0) {
      int temp = params.size() ;
      if (curNode.getKind() == OpArgKind) {
        temp = temp + ((OpArgNode) curNode).getArity();
       }
      else if (prevMode == FindingOpName) {
        temp = temp + ((SymbolNode) curNode).getArity();
       } ;

      if (expectedArity != temp) {
            errors.addError(
               sel.selSTN.getLocation(),
               "Expected arity " + expectedArity + 
               " but found operator of arity " + temp + ".") ;
            return nullOAN ;
        } ; 
     }; // if (expectedArity > 0)

    /***********************************************************************
    * If opDefArgs is non-empty, we will need to convert it to an array,   *
    * so we might as well do it here.                                      *
    ***********************************************************************/
    ExprOrOpArgNode[] opDefArgArray = 
                            new ExprOrOpArgNode[opDefArgs.size()] ;
    for (int i = 0 ; i < opDefArgs.size() ; i++) {
      opDefArgArray[i] = (ExprOrOpArgNode) opDefArgs.elementAt(i) ;
     } ; // for
       
    /***********************************************************************
    * +cal: if /\ prevMode = "FindingOpName" ... end if;                   *
    ***********************************************************************/
    if (   (prevMode == FindingOpName)
         && (params.size() + substInPrefix.size() > 0)) {

      /*********************************************************************
      * Set nodeParams to the +cal program's curNode.params value.         *
      *********************************************************************/
      FormalParamNode[] nodeParams = null ;
      if (curNode.getKind() == UserDefinedOpKind) {
        nodeParams = ((OpDefNode) curNode).getParams();
       }
      else {
        if (curNode.getKind() != ThmOrAssumpDefKind) {
              errors.addAbort(
                sel.opsSTN[sel.opsSTN.length-1].getLocation(),
                "Internal Error: " +
                 " Found unexpected node kind after FindingOpName") ;
         } ;
        nodeParams = ((ThmOrAssumpDefNode) curNode).getParams();
       } ;

      for (int i = 0 ; i < opDefArgs.size() ; i++) {
        allArgs.addElement(opDefArgArray[i]) ;
       } ; // for

      ExprOrOpArgNode[] temp = new ExprOrOpArgNode[nodeParams.length] ;
      for (int i = 0; i < nodeParams.length; i++) {
        FormalParamNode pm = nodeParams[i] ;
        /*******************************************************************
        * Set newpm to a "clone" of pm.                                    *
        *******************************************************************/
        FormalParamNode newpm = new FormalParamNode(pm.getName(),
                                                    pm.getArity(), 
                                                    pm.stn,
                                                    null, 
                                                    cm) ;

        /*******************************************************************
        * Set eoag to the ExprOrOpArgNode constructed from newpm.          *
        *******************************************************************/
        ExprOrOpArgNode eoag = null ;
        if (pm.getArity() == 0) {
          /*****************************************************************
          * Formal parameter eoag is an ordinary (non-operator) parameter. *
          *****************************************************************/
          eoag = new OpApplNode(newpm,
                                new ExprNode[0],
                                sel.selSTN,
                                cm) ;
         }
        else {
          /*****************************************************************
          * Formal parameter eoag is an operator parameter.                *
          *****************************************************************/
          eoag = new OpArgNode(newpm, sel.selSTN, cm) ;
         } ;
        temp[i] = eoag ;
        params.addElement(newpm) ;
       } ; // for
      SymbolNode curSymNode = (SymbolNode) curNode ;
      curNode = new OpApplNode(curSymNode,
                               temp, // opDefArgArray,
                               sel.selSTN, // TreeNode
                               cm );

     } ;// if (prevMode == FindingOpName) ...


    /***********************************************************************
    * +cal: if curNode.kind = OpArgKind                                    *
    ***********************************************************************/
    if (curNode.getKind() == OpArgKind) {
      OpArgNode curOpArgNode = (OpArgNode) curNode ;

      /*********************************************************************
      * +cal: if expectedArity = 0 then ... elsif                         *
      *********************************************************************/
      if (expectedArity == 0) {
        errors.addError(
               sel.selSTN.getLocation(),
               "Selected operator argument when expression expected.") ;
        return nullOAN ;
       } ;

      /*********************************************************************
      * +cal: elsif expectedArity # Len(params) + ... else                 *
      *********************************************************************/
      int temp = params.size() + curOpArgNode.getArity() ;
      if (expectedArity != temp) {
        errors.addError(
               sel.selSTN.getLocation(),
               "Expected operator of arity " + expectedArity +
               " but selected operator has arity " + temp + ".") ;
        return nullOAN ;
       }; 

      /*********************************************************************
      * +cal: else ... end if                                              *
      *********************************************************************/
      if (params.size() + substInPrefix.size() > 0) {
        FormalParamNode[] temp2 = 
                            new FormalParamNode[curOpArgNode.getArity()];
        for (int i = 0; i < temp2.length; i++) {
          UniqueString temp3 = UniqueString.uniqueStringOf(
                                 "NewParam" + i) ;
          temp2[i] = new FormalParamNode(
                           temp3,                      // name
                           0,                          // arity
                           new SyntaxTreeNode(temp3),  // syntax tree node
                           null,                       // symbol table
                           cm) ;                       // module
          params.addElement(temp2[i]) ;
         } ; // for
        curNode = new OpApplNode(curOpArgNode.getOp(),
                                 opDefArgArray,
                                 sel.selSTN, // TreeNode
                                 cm );
       } ; // if (params.size() + ...)
      
     }; // if (curNode.getKind() == OpArgKind)
 
    /***********************************************************************
    * This code doesn't seem to be present in the +cal code.  I forget     *
    * why not; perhaps I added it without correcting the +cal.             *
    *                                                                      *
    * Modified 19 May 2008 by LL because of addition of labeled            *
    * ASSUME/PROVE nodes.                                                  *
    ***********************************************************************/
    if (    ! isFact 
        && (   (    (curNode.getKind() == ThmOrAssumpDefKind)
                 && ( ((ThmOrAssumpDefNode) curNode).getBody().getKind()
                         == AssumeProveKind))
                /***********************************************************
                * curNode is an ASSUME/PROVE theorem.                      *
                ***********************************************************/
            || (    (curNode.getKind() == LabelKind)
                 && (((LabelNode) curNode).isAssumeProve)))
                /***********************************************************
                * curNode is a LabelNode naming an ASSUME/PROVE.           *
                ***********************************************************/
       ) { 
      errors.addError(
           sel.selSTN.getLocation(),
           "ASSUME/PROVE used where an expression is required.") ;
        return nullOAN ;
     };

    /***********************************************************************
    * The following code added 18 Oct 2007 to check if a                   *
    * pseudo-expression like "HAVE P" or "PICK ..." was used as an         *
    * expression.                                                          *
    ***********************************************************************/
   if (   (! isFact)
       && (curNode.getKind() == ThmOrAssumpDefKind)
       && (((ThmOrAssumpDefNode) curNode).getBody().getKind() 
                == OpApplKind)) {
      UniqueString opName = 
         ((OpApplNode) ((ThmOrAssumpDefNode) 
                           curNode).getBody()).getOperator().getName() ;
      String exprType = null ;
      if (opName == OP_qed) { exprType = "QED step" ;}
      else if (opName == OP_pfcase)  { exprType = "CASE" ;}
      else if (opName == OP_have)    { exprType = "HAVE" ;}
      else if (opName == OP_take)    { exprType = "TAKE" ;}
      else if (opName == OP_pick)    { exprType = "PICK" ;}
      else if (opName == OP_witness) { exprType = "WITNESS" ;}
      else if (opName == OP_suffices) { exprType = "SUFFICES" ;};
        /*******************************************************************
        * OP_suffices added by LL 16 Feb 2009.                             *
        *******************************************************************/
      if (exprType != null) {
         errors.addError(
            sel.selSTN.getLocation(),
            exprType + " proof step selected instead of expression.");
        return nullOAN ;
       } ;
    } // if


    /***********************************************************************
    * +cal: if curNode.kind \in {UserDefinedOpKind, ConstantDeclKind...    *
    ***********************************************************************/
    if (   (curNode.getKind() == UserDefinedOpKind) 
        || (curNode.getKind() == ConstantDeclKind) 
        || (curNode.getKind() == VariableDeclKind) 
        || (curNode.getKind() == FormalParamKind) 
        || (curNode.getKind() == BuiltInKind) 
        || (curNode.getKind() == BoundSymbolKind) 
        || (curNode.getKind() == ThmOrAssumpDefKind)
        || (curNode.getKind() == NewConstantKind)
        || (curNode.getKind() == NewVariableKind)
        || (curNode.getKind() == NewStateKind)
        || (curNode.getKind() == NewActionKind)
        || (curNode.getKind() == NewTemporalKind)) {
      SymbolNode curSymbolNode = (SymbolNode) curNode ;
      if (expectedArity > 0) {
        return new OpArgNode(curSymbolNode, sel.selSTN, cm) ;
       } 

      /*********************************************************************
      * +cal: elsif expectedArity = 0 then                                 *
      *********************************************************************/
      else {
        /*******************************************************************
        * expectedArity = 0                                                *
        *******************************************************************/
        OpApplNode oan = new OpApplNode(curSymbolNode,
                                        opDefArgArray,
                                        sel.selSTN,
                                        cm ) ;
        oan.subExpressionOf = subExprOf;
        return oan;
       }  // if (expectedArity > 0)
     } ; // if (curNode.getKind() == UserDefinedOpKind)

    /***********************************************************************
    * +cal: elsif curNode.kind = OpArgKind then                            *
    ***********************************************************************/
    if (curNode.getKind() == OpArgKind) { return (OpArgNode) curNode; } ;

    /***********************************************************************
    * +cal: else                                                           *
    ***********************************************************************/

    /***********************************************************************
    * The following test is not in Subexpression.tla and should not be,    *
    * having been added to allow the use of a ModuleInstanceKind as a      *
    * Fact or Def.  The else case should not occur because if it would be  *
    * the case, then the error should have been caught earlier (I think).  *
    ***********************************************************************/
    if (curNode.getKind() == ModuleInstanceKind) {
      if (isFact || isDef) {
        return (OpDefNode) curNode; 
        } 
      else {
        errors.addError(
          sel.selSTN.getLocation(),
             "Module instantiation selected instead of expression.");
        return nullOAN ;
       }
      } ;    
    /***********************************************************************
    * curNode should be an expression node.                                *
    ***********************************************************************/
    if (!(curNode instanceof ExprNode)) {
      errors.addAbort(sel.selSTN.getLocation(),
                      "Internal error: Expected expression node.") ;
     } ;
    ExprNode curExprNode = (ExprNode) curNode ;
    int temp = substInPrefix.size() ;

    /***********************************************************************
    * +cal: while temp > 0 do ... end while                                *
    ***********************************************************************/
    while (temp > 0) {
      // Modified on 13 Nov 2009 by LL to handle the case of a subexpression
      // of a Theorem or Assumption. 
      Object substOb = substInPrefix.elementAt(temp-1) ;
      if (substOb instanceof SubstInNode) {
          SubstInNode subst = (SubstInNode) substOb;
          curExprNode = new SubstInNode(subst.stn,
                                        subst.getSubsts(),
                                        curExprNode,
                                        subst.getInstantiatingModule(),
                                        subst.getInstantiatedModule()
                                       );
      } else {
          APSubstInNode subst = (APSubstInNode) substOb;
          curExprNode = new SubstInNode(subst.stn,
                                        subst.getSubsts(),
                                        curExprNode,
                                        subst.getInstantiatingModule(),
                                        subst.getInstantiatedModule()
                 );
          
      }
      temp = temp - 1;
     }; // while

    /***********************************************************************
    * Will need params as an array.                                        *
    ***********************************************************************/
    FormalParamNode[] paramsArray = new FormalParamNode[params.size()] ;
    for (int i = 0; i < params.size(); i++) {
      paramsArray[i] = (FormalParamNode) params.elementAt(i) ;
      } ;

    /***********************************************************************
    * If there are params, will need a Lambda operator.                    *
    ***********************************************************************/
    OpDefNode newLambda = null ;
    if (paramsArray.length > 0) {
      newLambda =
        new OpDefNode(S_lambda,          // The operator name is "LAMBDA"
                      UserDefinedOpKind, // The node kind 
                      paramsArray,       // the array of formal parameters
                      false ,            // localness, which is meaningless
                      curExprNode,       // the body 
                      cm,                // the module
                      null,              // the symbol table
                      sel.selSTN,        // syntax-tree node
                      true,              // Is defined.  
                      null ) ;           // Source
      } ;
    
    /***********************************************************************
    * +cal: if expectedArity > 0                                           *
    ***********************************************************************/
    if (expectedArity > 0) {
      if (paramsArray.length != expectedArity) {
        errors.addError(
          sel.selSTN.getLocation(),
          "Expected operator argument with arity " + expectedArity + 
          " but found one of arity " + paramsArray.length + ".") ;
        return nullOAN ; 
       } ;
      return new OpArgNode(newLambda, sel.selSTN, cm) ;
      } // if (expectedArity > 0) 

    /***********************************************************************
    * expectedArity = 0                                                    *
    * +cal: else if Len(params) # Len(allArgs)                             *
    ***********************************************************************/
    if (paramsArray.length != allArgs.size()) {
      errors.addError(
        sel.selSTN.getLocation(),
        "Expected " + paramsArray.length + " arguments but found " +
          allArgs.size() + ".") ;
      return nullOAN ; 
     } ; 
    /***********************************************************************
    * +cal: if Len(params) = 0 then                                        *
    ***********************************************************************/
    if (paramsArray.length == 0) {
      /*********************************************************************
      * In this case, we don't have to construct a new LAMBDA or OpAppl    *
      * node.  However, we want to have a new node to which to attach the  *
      * SyntaxTree node.  So, we create an OpApplNode with the dummy       *
      * builtin operator $Nop and return it.                               *
      *********************************************************************/
      ExprOrOpArgNode[] args = new ExprOrOpArgNode[1] ;
      args[0] = curExprNode ;
      OpApplNode ln = new OpApplNode(OP_nop, args,  sel.selSTN, cm) ;
      ln.subExpressionOf = subExprOf ;
      return ln;}

    /***********************************************************************
    * +cal: else                                                           *
    ***********************************************************************/
    /***********************************************************************
    * Will need allArgs as an array.                                       *
    ***********************************************************************/
    ExprOrOpArgNode[] allArgsArray = new ExprOrOpArgNode[allArgs.size()] ;
    for (int i = 0; i < allArgs.size(); i++) {
      allArgsArray[i] = (ExprOrOpArgNode) allArgs.elementAt(i) ;
      } ;
    
    OpApplNode oan = 
          new OpApplNode (newLambda, allArgsArray, sel.selSTN, cm) ; 
    oan.subExpressionOf = subExprOf ;
    return oan ;
       
   } // selectorToNode

  private static String selectorItemToString(Selector sel, int idx) {
    String selStr = sel.opNames[idx].toString() ;
    if (selStr.equals("N_StructOp")) {
      selStr = "argument selector " + 
               sel.opsSTN[idx].heirs()[0].heirs()[0].getImage() ;
     } 
    else if (selStr.equals("N_OpArgs")) {
      selStr = "!(...)" ;
     };
    return selStr ;
    }

  private void reportSelectorError(Selector sel, int idx) {
    /***********************************************************************
    * Just a method to perform error reporting when an error is detected   *
    * when executing selectorToNode.                                       *
    ***********************************************************************/
    errors.addError(sel.opsSTN[idx].getLocation(),
                    "Nonexistent operand specified by `"
                     +  selectorItemToString(sel, idx) + "'.");
   }

  private boolean isNullSelection(SemanticNode node, Selector sel, int idx) {
    /***********************************************************************
    * A method for use in selectorToNode to test if a a null node has      *
    * been selected.  This should happen only if the null node was         *
    * created as a result of a previous error.  If the node is null, then  *
    * an error is reported and true is returned.                           *
    ***********************************************************************/
    boolean val = (node == null) ;
    if (val) { 
      errors.addError(sel.opsSTN[idx].getLocation(),
                    "An unexpected null node specified by "
                     +  selectorItemToString(sel, idx) + "'."
                     + "\nThis is probably due to a previous error.");
     };
    return val ;
   } 

  // Constructor
  public Generator(ExternalModuleTable moduleTable, Errors errs) {
    nullParam = new FormalParamNode[0];
    nullODN   = new OpDefNode(UniqueString.uniqueStringOf("nullODN"));
    nullOAN   = new OpApplNode(nullODN);
    nullOpArg = new OpArgNode(UniqueString.uniqueStringOf("nullOpArg"));
    nullLabelNode = new LabelNode(nullOAN) ;
    this.errors       = errs;
    this.moduleTable  = moduleTable;
    this.symbolTable  = new SymbolTable(moduleTable, errors);
    this.excStack     = new Stack(); 
    this.excSpecStack = new Stack();
  }

  public final SymbolTable getSymbolTable() { return symbolTable; }

  public final ModuleNode generate(TreeNode treeNode) throws AbortException {
    /*************************************************************************
    * This is the method called to generate the semantic graph for a module. *
    *************************************************************************/
//System.out.println("TRUE = " + symbolTable.resolveSymbol(
//                      UniqueString.uniqueStringOf("TRUE"))) ;
//System.out.println("$SetEnumerate = " + symbolTable.resolveSymbol(
//                      UniqueString.uniqueStringOf("$SetEnumerate"))) ;


    if (treeNode.isKind( N_Module )) {
      this.context = symbolTable.getContext();
      return this.generateModule(treeNode, null);
    } 
    return null;
  }

  private final Context getContext(UniqueString us) {
    ModuleNode symbolNode = symbolTable.resolveModule(us);

    if (symbolNode == null) {
      return moduleTable.getContext(us);
    }
    return symbolNode.getContext();
  }

  private final ModuleNode generateModule(TreeNode treeNode, ModuleNode parent)
  throws AbortException {
    moduleNestingLevel++ ;
    TreeNode[] children    = treeNode.heirs();     // Array of heirs of the module root
    TreeNode[] definitions = null;                 
      // Array of definitions in the module
      /*********************************************************************
      * Actually, the array of all syntactic nodes that are heirs of the   *
      * module's body node--that is, definitions, theorems, parameter      *
      * declarations, etc.                                                 *
      *********************************************************************/
    TreeNode[] ss          = children[0].heirs();  // Array of heirs of the module header
                                                   // ss[1] is always the module name
    String  moduleName     = ss[1].getImage();     // the module name
    ModuleNode currentModule = new ModuleNode(ss[1].getUS(), context, treeNode);
    currentModule.nestingLevel = moduleNestingLevel ;
    // if this is an internal module, add its ModuleNode to the end of
    // the list of definitions for the parent
    if (parent != null) {
      parent.appendDef(currentModule);
    }

    symbolTable.setModuleNode( currentModule );
    // children[1] == extends
    // children[1] is always the Extend's list (even if none)
    processExtendsList(children[1].heirs(), currentModule); 

    // children[2] == body
    // children[2] is always the module body note that this line
    // redefines "children" to be the array of definitions in the
    // module
    definitions = children[2].heirs();

    // for each declaration, op definition, etc. in the body...
    for (int lvi = 0; lvi < definitions.length; lvi++) {
      switch (definitions[lvi].getKind()) {
      case N_VariableDeclaration :
        checkIfInRecursiveSection(definitions[lvi], "A VARIABLE declaration") ;
        processVariables(definitions[lvi].heirs(), currentModule);
        break;

      case N_ParamDeclaration :
        checkIfInRecursiveSection(definitions[lvi], "A declaration") ;
        processParameters(definitions[lvi].heirs(), currentModule);
        break;

      case N_OperatorDefinition :
        processOperator(definitions[lvi], null, currentModule);
        break;

      case N_FunctionDefinition :
        processFunction(definitions[lvi], null, currentModule);
        break;

      case N_ModuleDefinition :
// We now allow INSTANCEs in recursive sections.
//        checkIfInRecursiveSection(definitions[lvi], "An INSTANCE") ;
        processModuleDefinition(definitions[lvi], null, null, currentModule);
        break;

      case N_Module :
        // Modules can be nested, but inner ones need to keep a 
        // separate SymbolTable of their own.
        checkIfInRecursiveSection(definitions[lvi], "A MODULE ") ;
        SymbolTable oldSt = symbolTable; 
        symbolTable = new SymbolTable(moduleTable, errors, oldSt);
        context = new Context(moduleTable, errors);
        symbolTable.pushContext(context);
        ModuleNode mn = generateModule(definitions[lvi], currentModule);
        symbolTable.popContext();
        symbolTable = oldSt;

        // Add the inner module's name to the context of the outer module
        symbolTable.addModule(mn.getName(), mn);

        /*******************************************************************
        * Append the opDefsInRecursiveSection field of the inner module    *
        * to that of the current module.                                   *
        *******************************************************************/
        for (int i = 0; i < mn.opDefsInRecursiveSection.size(); i++) {
        currentModule.opDefsInRecursiveSection.addElement(
               mn.opDefsInRecursiveSection.elementAt(i));
         } ;
        // System.err.println(mn.getName() + " added to SymbolTable for " + currentModule.getName()); 
        break;

      case N_Instance :
// We now allow INSTANCEs in recursive sections.
//        checkIfInRecursiveSection(definitions[lvi], "An INSTANCE") ;
        generateInstance(definitions[lvi], currentModule, true);
        break;

      case N_Proof :
        checkIfInRecursiveSection(definitions[lvi], "A proof") ;
        break;

      case N_Theorem : 
        checkIfInRecursiveSection(definitions[lvi], "A THEOREM") ;
        processTheorem(definitions[lvi], currentModule);
        break; 

      case N_Assumption : 
        checkIfInRecursiveSection(definitions[lvi], "An ASSUME");
        processAssumption(definitions[lvi], currentModule);
        break;
       
      case N_UseOrHide : 
        checkIfInRecursiveSection(definitions[lvi], "A USE or HIDE");
        UseOrHideNode uohn = generateUseOrHide(definitions[lvi], 
                                                currentModule) ;
        uohn.factCheck();
          // Added 4 Mar 2009.
        if (uohn.facts.length + uohn.defs.length == 0) {
          errors.addError(definitions[lvi].getLocation(),
                          "Empty USE or HIDE statement.");
         };
        currentModule.addTopLevel(uohn) ;
        break;
       
      case SEPARATOR :
        /*******************************************************************
        * This code was originally                                         *
        *                                                                  *
        *   case 35                                                        *
        *   // Intended to handle "---------".  Kludge for a parser bug.   *
        *                                                                  *
        * I have no idea why 35 was used instead of SEPARATOR, and what    *
        * kind of parser bug mentioned was encountered.  The original      *
        * code did not import parser.TLAplusParserConstants where          *
        * SEPARATOR was used, so perhaps there was some reason why this    *
        * class could not be imported.                                     *
        *******************************************************************/
        break;  

      case N_Recursive :
        processRecursive(definitions[lvi], currentModule);
        break; 
      default :
        errors.addAbort(
          definitions[ lvi ].getLocation(),
          "Internal error: Syntax node of kind " + 
          definitions[ lvi ].getKind() + " unsupported " + 
          definitions[ lvi ].getImage(), true);
        break;
      }
    }

    checkForUndefinedRecursiveOps(currentModule) ;

Vector vec = currentModule.recursiveOpDefNodes ;
for (int i = 0 ; i < vec.size() ; i++) {
OpDefNode node = (OpDefNode) vec.elementAt(i);
// System.out.println("symbol " + node.getName() + ": recSect = " 
//                    + node.recursiveSection + ", inRecSect = " 
//                    + node.inRecursiveSection + ", letInLevel = "
//                    + node.letInLevel);
  } ;

    moduleNestingLevel -- ;
    return currentModule;

  } // generateModule

  // This method must be extended so that the Extends list hangs off of 
  // the ModuleNode to support a getExtends() method that might reasonably 
  // be in the API.
  private final void processExtendsList(TreeNode treeNodes[], ModuleNode cm)
  throws AbortException{
    Vector extendeeVector = new Vector(2);

    if (treeNodes != null) {
      // module names in the EXTENDS list are separated by commas; hence incr by 2
      for (int lvi = 1; lvi < treeNodes.length; lvi += 2) {
        // Try to find the ModuleNode for the module being EXTENDED in the symbolTable
        UniqueString extendeeID = treeNodes[lvi].getUS();
        ModuleNode extendee = symbolTable.resolveModule(extendeeID);

        // It must be an external module if it isn't in the symbolTable;
        // try to find it in moduleTable (it cannot be in both places)
        if (extendee == null) {
          extendee = moduleTable.getModuleNode(extendeeID);
          if (extendee == null) {
            errors.addAbort(treeNodes[lvi].getLocation(), 
                            "Could not find module " + extendeeID,
                            false);
          }
        }

        extendeeVector.addElement(extendee);

        Context context = this.getContext(extendeeID);
        if (context != null) {
          symbolTable.getContext().mergeExtendContext(context);
        }
        else {
          errors.addError(treeNodes[lvi].getLocation(),
                          "Couldn't find context for module `" + extendeeID
                          + "'.");
        }

        // copy nonlocal Assumes and Theorems
        cm.copyAssumes(extendee);
        cm.copyTheorems(extendee);
        cm.copyTopLevel(extendee);
      }
    }
    cm.createExtendeeArray(extendeeVector);
  } // processExtendsList

  // This method must be extended so that the variable declarations list 
  // hangs off of the module node to support the getVariableDecls method 
  // of the API.
  private final void processVariables(TreeNode treeNodes[], ModuleNode cm) {
    for (int lvi = 1; lvi < treeNodes.length; lvi += 2) {
      UniqueString us = treeNodes[ lvi ].getUS();

      if (us == S_at) {
        errors.addError(treeNodes[lvi].getLocation(),
                        "Attempted to declare '@' as a variable.");
      }

      // The next line has its side-effects in the constructor; in particular,
      // the new OpDeclNode is placed in the symbolTble there.
      new OpDeclNode(us, VariableDeclKind, 1, 0, cm, symbolTable, treeNodes[lvi]);
    }
  }



  private final OpDeclNode buildParameter(TreeNode treeNode, 
                                          int declKind,
                                          int declLevel,
                                          ModuleNode cm,
                                          boolean declare) {
    /***********************************************************************
    * This method was originally called only by the processParameters      *
    * method to build an OpDeclNode for a module-level CONSTANT            *
    * declaration.  For a declaration "CONSTANT foo(_), _+_" it would be   *
    * called twice, once with treeNode the node for "foo(_)", and once     *
    * with it equal to the node for "_+_".  The OpDeclNode is not returned *
    * because its constructor adds the node to symbolTable.                *
    *                                                                      *
    * It was modified by LL on 22 Mar 2007 for use in the generateNewSymb  *
    * method as well.  The modifications consisted of returning the        *
    * OpDeclNode and adding arguments to specify the kind and level of     *
    * the OpDeclNode.                                                      *
    *                                                                      *
    * Further modified by LL on 6 Apr 2007 for use in the                  *
    * processRecursive method as well.  The modification consisted of      *
    * adding the declare argument.  If true, it calls the OpDeclNode       *
    * constructor with symbol table symbolTable, so the symbol is added    *
    * to the current symbol table.  If false, it calls the constructor     *
    * with a null symbol table, so nothing is declared.  The               *
    * processRecursive method just uses the name and arity from the        *
    * returned OpDeclNode.                                                 *
    ***********************************************************************/
    UniqueString us = null;
    int arity = 0;
    TreeNode[] ss = treeNode.heirs();

    if      ( treeNode.isKind( N_IdentDecl ) ) {
      us = ss[0].getUS();
      arity = (ss.length - 1) / 2;
    }
    else if ( treeNode.isKind( N_PrefixDecl ) ) {
      us = ss[0].getUS();
      arity = 1;
    }
    else if ( treeNode.isKind( N_InfixDecl ) ) {
      us = ss[1].getUS();
      arity = 2;
    }
    else if ( treeNode.isKind( N_PostfixDecl ) ) {
      us = ss[1].getUS();
      arity = 1;
    }
    else {
      errors.addError(treeNode.getLocation(),
                      "Unknown parameter declaration `" + treeNode.getUS()
                      + "'.");
    }
//    SymbolNode symbolNode = 
     SymbolTable st = null ;
     if (declare) {st = symbolTable;};

     /**********************************************************************
     * Changed us to Operators.resolveSynonym(us) in the following so      *
     * constant declarations work with any synonym for an operator--e.g.,  *
     * with both (+) and \oplus.                                           *
     **********************************************************************/
     return new  OpDeclNode(Operators.resolveSynonym(us), declKind, declLevel, arity, cm, 
                            st, treeNode);
  }

  private final void processParameters(TreeNode treeNodes[], ModuleNode cm) {
    for (int lvi = 1; lvi < treeNodes.length; lvi +=2 ) {
      if (treeNodes[lvi].getUS() == S_at) {
        errors.addError(treeNodes[lvi].getLocation(),
                        "Attempted to declare '@' as a constant.");
       } ;
      OpDeclNode odn = 
         buildParameter(treeNodes[lvi], ConstantDeclKind, ConstantLevel, 
                        cm, true);
        /*******************************************************************
        * We throw away the OpDeclNode because, when it was constructed,   *
        * it was added to symbolTable, whose top context should be the     *
        * top-level context of the module.                                 *
        *******************************************************************/
    }
  }

  /**
   * Processes the LHS of an operator definition, in several ways,
   * depending on whether it is a prefix, infix, postfix, or a
   * parameter-free or parameter-ful function-notation operator. Also
   * creates context entries for the operator and its parameters.
   */
   /************************************************************************
   * Processes a syntactic node of type N_OperatorDefinition.  It is       *
   * called by generateModule (with defs = null) when processing an        *
   * outer-level definition and by processLetIn (with defs /= null) when   *
   * processing a LET definition.  It creates an OpDef node and puts it    *
   * in ModuleNode cm's set of definitions.                                *
   ************************************************************************/
  private final void processOperator(TreeNode treeNode, Vector defs, 
                                     ModuleNode cm) throws AbortException {
    TreeNode           syntaxTreeNode = treeNode;
    UniqueString       name     = null;
    int                arity    = 0;
    boolean            local    = syntaxTreeNode.zero() != null;
    TreeNode []        children = syntaxTreeNode.one();
    TreeNode []        ss       = children[0].heirs();
    FormalParamNode [] params   = null;
    Context            ctxt     = new Context(moduleTable, errors);
    boolean isRecursive = false ;
      /*********************************************************************
      * Will be set to true if this operator was declared in a RECURSIVE   *
      * statement.                                                         *
      *********************************************************************/
    // New context needed because parameter symbols may have to be
    // added if the operator being defined takes params
    symbolTable.pushContext( ctxt );
  
    // If the operator is an identifier (possibly with params), as
    // opposed to a prefix, infix, or postfix symbol
    if ( children[ 0 ].isKind( N_IdentLHS ) ) {
      if ( ss.length > 2 ) {
        // If the operator has arguments
        params = new FormalParamNode[ (ss.length-2) / 2 ];
        for ( int lvi = 2; lvi < ss.length; lvi += 2 ) {
          TreeNode sss[] = ss[ lvi ].heirs();
          if        ( ss[ lvi ].isKind( N_IdentDecl ) ) {
            // parameter is simple identifier
            name = sss[0].getUS();
            arity = (sss.length - 1 )/ 2;
          }
          else if ( ss[ lvi ].isKind( N_InfixDecl ) ) {
            // parameter is infix operator
            // Call of Operators.resolveSynonym added by LL on 27 Mar 2013
            name = sss[1].getUS();
            
            // Following added by LL on 27 Mar 2013
            // to handle parameters like _(+)_
            name = Operators.resolveSynonym(name);
            
            arity = 2;
          }
          else if ( ss[ lvi ].isKind( N_PrefixDecl ) ) {
            // parameter is prefix operator
            name = sss[0].getUS();
            arity = 1;
          }
          else {
            // parameter must be postfix operator
            // SZ Jul 13, 2009: added the message to the assert
            if(! ss[ lvi ].isKind( N_PostfixDecl )) 
            {
                throw new WrongInvocationException(MP.getMessage(EC.TLC_PARAMETER_MUST_BE_POSTFIX)); 
            }
            name = sss[1].getUS();
            arity = 1;
          }
          params[ (lvi-2)/2 ] = 
            new FormalParamNode(name, arity, ss[lvi], symbolTable, cm);
        }
      }
      else {
        // The operator has no arguments
        params = new FormalParamNode[0];
      }
      name = ss[0].getUS();
    }
    else if (children[ 0 ].isKind(N_PrefixLHS)) { // operator is a prefix operator
      // Process the parameter
      params = new FormalParamNode[1];
      params[0] = new FormalParamNode(ss[1].getUS(), 0, ss[1], symbolTable, cm);
  
      // Process the operator
      name = Operators.resolveSynonym(ss[0].getUS());
    }
    else if (children[ 0 ].isKind(N_InfixLHS)) { // operator is an infix operator
      params = new FormalParamNode[2];
      // Process the first param
      params[0] = new FormalParamNode(ss[0].getUS(), 0, ss[0], symbolTable, cm);
  
      // Process the second param
      params[1] = new FormalParamNode(ss[2].getUS(), 0, ss[2], symbolTable, cm);
  
      // Process the operator
      name = Operators.resolveSynonym(ss[1].getUS());
    }
    else if (children[ 0 ].isKind(N_PostfixLHS)) { // operator is a postfix operator
      // Process the parameter
      params = new FormalParamNode[1];
      params[0] = new FormalParamNode(ss[0].getUS(), 0, ss[0], symbolTable, cm);
  
      // Process the operator
      name = Operators.resolveSynonym(ss[1].getUS());
    }
    else {
      errors.addError(children[0].getLocation(),
                      "Unknown parameter declaration `" + 
                      children[0].getUS() + "'.");
    }

    /***********************************************************************
    * The following code added by LL on 1 April 2007 to handle             *
    * recursively defined operators.                                       *
    ***********************************************************************/
    OpDefNode odn = null ;
    /***********************************************************************
    * Check if this operator has already been declared or defined.  If     *
    * so, if it was declared in a RECURSIVE statement at this let/in       *
    * level and not yet defined, then set the OpDefNode's fields           *
    * appropriately, otherwise report an error.                            *
    ***********************************************************************/
    SymbolNode symbolNode = symbolTable.resolveSymbol(name) ;

    if (symbolNode != null) {
      /*********************************************************************
      * The symbol has already been defined or declared.  Check if it was  *
      * declared in a RECURSIVE statement.                                 *
      *********************************************************************/
      if (symbolNode instanceof OpDefNode) {odn = (OpDefNode) symbolNode;};
      if (   (odn != null) 
          && odn.inRecursive 
          && (! odn.isDefined) ) {
        if (odn.letInLevel == curLevel) {
          isRecursive = true;

          /*****************************************************************
          * Check that the parameters of the definition match the ones in  *
          * the RECURSIVE declaration.                                     *
          *****************************************************************/
          boolean paramsMatch = (odn.getParams().length == params.length) ;
          if (paramsMatch) {
            for (int i = 0 ; i < params.length ; i++) {
              paramsMatch = (params[i].getArity() == 0) ;
             };
           }; // if
          if (!paramsMatch) { 
            errors.addError(treeNode.getLocation(),
                            "Definition of " + odn.getName() + 
                            " has different arity than " + 
                            "its RECURSIVE declaration.");
           };

          odn.setParams(params) ;
            /***************************************************************
            * Here's where the params field of the OpDefNode is set for an *
            * operator declared in a RECURSIVE statement.                  *
            ***************************************************************/
          } // if (odn.letInLevel == curLevel)
        else {errors.addError(treeNode.getLocation(),
                              "Recursive operator " + name.toString() + 
                              " defined at wrong LET/IN level.") ;
              odn = null ;
         } // else
        } // if (odn != null) ...
      else { errors.addError(treeNode.getLocation(),
                             "Operator " + name.toString() + 
                              " already defined or declared.") ;
       }
     } // if (symbolNode != null)

    pushLS() ;
      /*********************************************************************
      * Start fresh processing of labels.                                  *
      *********************************************************************/
    // Generate expression that is the body of the operator
    ExprNode exp = generateExpression( children[2], cm );
  
    // Restore old context, popping off the context containing the parameters
    symbolTable.popContext();
  
    
    if (isRecursive) {endOpDefNode(odn, exp, syntaxTreeNode) ; } 
      else {
      // Create OpDefNode using symbolTable whose top context contains the 
      // parameter symbols
       /********************************************************************
       * This comment appears to be incorrect, because it looks like the   *
       * parameter symbols were just popped off symbolTable.               *
       ********************************************************************/
      odn = new OpDefNode(name, UserDefinedOpKind, params, local, 
                           exp, cm, symbolTable, syntaxTreeNode, true, null);
      symbolNode = odn ;
        /*******************************************************************
        * Keeping symbolNode for historical reasons--I'm too lazy to       *
        * rearrange the code to get rid of the redundant identifier.       *
        *******************************************************************/

      setOpDefNodeRecursionFields(odn, cm) ;

     } // else

    Hashtable ht = popLabelNodeSet() ;
      /*********************************************************************
      * Succeed or fail, we must execute popLabelNodeSet to match the      *
      * previous pushLS.                                                   *
      *********************************************************************/
    if (odn != null) {odn.setLabels(ht);} ;
      /*********************************************************************
      * If there was no error, then odn is an OpDefNode and we must set    *
      * it labels field.                                                   *
      *********************************************************************/
    cm.appendDef(symbolNode) ;
        /*******************************************************************
        * Add the new OpDefNode to the current module's set of             *
        * definitions.                                                     *
        *******************************************************************/
    // defs is non-null iff this definition is in the Let part of a 
    // Let-In expression
    if (defs != null) defs.addElement(symbolNode);
  } // processOperator   
    
  private final void processQuantBoundArgs(
                      TreeNode[]treeNodeA, // node whose children include 
                                           // the bounded quants
                      int offset,          // nodes to skip to get to first 
                                           // "quantifier"
                      FormalParamNode[][] odna, 
                      boolean []bt,        // set to true if arg is a tuple; 
                                           // otherwise false
                      ExprNode[] ena, 
                      ModuleNode cm)
    /***********************************************************************
    * Despite the incoherent and/or incorrect comments, here's what I      *
    * think is going on:                                                   *
    *                                                                      *
    *  - odna, ena, and bt have the same length N.                         *
    *                                                                      *
    *  - treeNodeA is an array of nodes containing a subsequence of        *
    *    N_QuantBound nodes of length N that starts at                     *
    *    treeNodeA[offset].                                                *
    *                                                                      *
    *  - odna, ena, and bt are set to the arguments for the OpApplNode     *
    *    constructor that produces an OpApplNode for the operator          *
    *    having this sequence of N_QuantBound nodes.                       *
    ***********************************************************************/

  throws AbortException {
    // For each quantifier, evaluate the bound in the context of the
    // current symbol table, i.e. before the quantified variables are
    // added to the new context, since the quantified vars may not
    // appear in the bounds.
    for (int lvi = 0; lvi < bt.length; lvi++ ) {
      // Make ss point to each N_QuantBound node in turn.
      TreeNode[] ss = treeNodeA[offset + 2 * lvi].heirs();
      // the last element in ss is expression for the quantifier bound
      ena[lvi] = generateExpression( ss[ ss.length - 1 ], cm );
    }

    // Now for each quantifier, process the variable names
    for (int lvi = 0; lvi < bt.length; lvi++ ) {
      TreeNode treeNode = treeNodeA[offset + 2 * lvi];  

      // The variable bound to the "quantifier"
      TreeNode[] ss = treeNode.heirs();

      if (ss[0].isKind(N_IdentifierTuple)) { // three elements only, go into node
        bt[lvi] = true;
        TreeNode[] sss = ss[0].heirs();
        odna[lvi] = new FormalParamNode[ sss.length / 2 ];

        for (int lvj = 0; lvj < sss.length / 2; lvj++ ) {
          odna[lvi][lvj] = new FormalParamNode(
                                sss[ 2*lvj+1 ].getUS(), 0, sss[ 2*lvj+1 ],
                                symbolTable, cm) ;
        }
      }
      else { // gotta be N_Identifier
        bt[lvi] = false;
        odna[lvi] = new FormalParamNode[ (ss.length - 1)/2 ];

        for ( int lvj = 0; lvj <  (ss.length - 1)/2 ; lvj++ ) {
          odna[lvi][lvj] = new FormalParamNode(
                                  ss[ 2*lvj ].getUS(), 0, ss[ 2*lvj ],
                                  symbolTable, cm);
        }
      }
    }
  }

  // Process a function definition
  private final void processFunction(TreeNode treeNode, Vector defs, ModuleNode cm)
  throws AbortException {
    TreeNode        syntaxTreeNode = treeNode;
    boolean         local      = syntaxTreeNode.zero() != null;
    TreeNode[]      ss         = syntaxTreeNode.one();  
       // Heirs to N_FunctionDefinition node
    int             ql         = (ss.length-4)/2;       
       // number of QuantBound's
    OpApplNode      oan;
    OpDefNode       odn = null;
    FormalParamNode[][] quants     = new FormalParamNode[ql][0];
    FormalParamNode[]   fcnDeclForRecursion = new FormalParamNode[1];
      /*********************************************************************
      * This is an array of length 1 instead of just an OpDeclNode         *
      * because it is needed in such an array to pass as an argument to    *
      * new OpApplNode.                                                    *
      *********************************************************************/
    boolean []      tuples     = new boolean[ql];
    ExprNode []     domains    = new ExprNode[ql];
    ExprNode []     lhs        = new ExprNode[1];
    Context         newContext = new Context(moduleTable, errors);
    boolean isRecursive = false ;
      /*********************************************************************
      * Will be set to true if this operator was declared in a RECURSIVE   *
      * statement.                                                         *
      *********************************************************************/

    // Fill arrays with quantifier-related information; must be called
    // in scope of *new* context, since it adds parameter symbols to
    // the context.
    symbolTable.pushContext(newContext);
    processQuantBoundArgs( ss, 2, quants, tuples, domains, cm ); 

    UniqueString name = ss[0].getUS() ;
    SymbolNode symbolNode = symbolTable.resolveSymbol(name) ;


    // This is in anticipation of the possibility that the function is
    // recursive.  We are creating a new bound symbol of the same name
    // as the function to stand in the body for the function.  The
    // arity of the bound symbol is 0 because a function formally has
    // arity 0 as an operator, even if it has several arguments as a
    // function.
    /***********************************************************************
    * If the function name is already defined (which should happen only    *
    * if it was declared in a RECURSIVE statement, then there is no need   *
    * to add this OpDeclNode to the symbol table.  As near as I can tell   *
    * (which might not be near enough), this OpDeclNode's entry in the     *
    * symbol table is needed only so the name will be declared in case     *
    * of a recursive call.  The check for whether a function call in the   *
    * body actually is recursive is made by calling the recursionCheck     *
    * method of the Function subclass to see if the OpApplNode is in the   *
    * Function object's funcStack.                                         *
    ***********************************************************************/
    SymbolTable st = null ;
    if (symbolNode == null) {st = symbolTable; } ;
      fcnDeclForRecursion[0] = 
        new FormalParamNode(name, 0, treeNode, st, cm);
    symbolTable.popContext();

    // Create OpApplNode to hold the function body; type is assumed to
    // be non-recursive function (OP_nrfs); if the body is recursive,
    // this will be discovered during generateExpression() for the
    // body
    oan = new OpApplNode(OP_nrfs, fcnDeclForRecursion, new ExprNode[0], 
                         quants, tuples, domains, syntaxTreeNode, cm);
                 // constructor 5

    /***********************************************************************
    * The following code added by LL on 19 April 2007 to handle            *
    * recursively defined operators.                                       *
    ***********************************************************************/
    if (symbolNode == null) {
      odn = new OpDefNode(ss[0].getUS(), UserDefinedOpKind, nullParam, local, 
                          oan, cm, symbolTable, syntaxTreeNode, true, null);
      setOpDefNodeRecursionFields(odn, cm) ;
     }
    else 
      {
      /*********************************************************************
      * The symbol has already been defined or declared.  Check if it was  *
      * declared in a RECURSIVE statement.                                 *
      *********************************************************************/
      if (symbolNode instanceof OpDefNode) {odn = (OpDefNode) symbolNode;};
      if (   (odn != null) 
          && odn.inRecursive 
          && (! odn.isDefined) ) {
        if (odn.letInLevel == curLevel) {
          isRecursive = true;
          /*****************************************************************
          * Check that the RECURSIVE declaration had no paramters.         *
          *****************************************************************/
          if (odn.getArity() == 0) {
            endOpDefNode(odn, oan, syntaxTreeNode) ;
            }
           else {
              /*************************************************************
              * RECURSIVE declaration had parameters.                      *
              *************************************************************/
              errors.addError(treeNode.getLocation(),
                              "Function " + odn.getName() + 
                              " has operator arguments in " + 
                              "its RECURSIVE declaration.");
            } ;
         } // if (odn.letInLevel == curLevel)
        else {errors.addError(treeNode.getLocation(),
                              "Recursive function " + name.toString() + 
                              " defined at wrong LET/IN level.") ;
              odn = null ;
         } // else
        } // if (odn != null) ...
      else { errors.addError(treeNode.getLocation(),
                             "Function name `" + name.toString() + 
                              "' already defined or declared.") ;
       } 
     } // else (symbolNode != null)            

    // Create OpDefNode to hold the function definition, including
    // reference to the function body ("oan")
    if (odn != null) {
      /*********************************************************************
      * There was no error, so the OpDefNode was created.                  *
      *********************************************************************/
      cm.appendDef(odn);

       // defs is non-null iff this function definition is in the Let
       // part of a Let-In expression.  If so, then we have to accumulate
       // these defs in a vector.
       if (defs != null) defs.addElement(odn);

       // Function body must be processed in the scope of the new
       // context, including the parms
       symbolTable.pushContext( newContext );

     }; // if (odn != null)

    // Keep stack of nested function defs to enable detection of recursion
    functions.push( ss[0].getUS(), oan );

    
    // Create semantic graph function body in the inner context including parameters
    pushLS() ; 
    pushFormalParams(flattenParams(quants)) ;
      /*********************************************************************
      * Push a new empty label set onto LS, and push the function          *
      * definition's formal parameters onto Last(LS).paramSeq for          *
      * processing the function body.                                      *
      *********************************************************************/
    lhs[0] = generateExpression( ss[ss.length - 1], cm ); 
    popFormalParams() ;
      /*********************************************************************
      * Pop the formal params from Last(LS).paramSeq, which should now be  *
      * empty.  This isn't really necessary, since we're going to pop the  *
      * LS stack below, but I hate to have a push without a pop.           *
      *********************************************************************/
    Hashtable ht = popLabelNodeSet() ;
      /*********************************************************************
      * The matching pop for the pushLS above.                             *
      *********************************************************************/
    if (odn != null) { odn.setLabels(ht); } ;
      /*********************************************************************
      * If there was no error and we created an OpDefNode, then set its    *
      * label set.                                                         *
      *********************************************************************/
    functions.pop();

    oan.setArgs( lhs );
    /***********************************************************************
    *  Test for odn != null added 2 Jul 2009 to avoid bug that caused      *
    *  popping of empty symbol table when the function name was            *
    *  already declared to be a variable.                                  *
    ***********************************************************************/
    if (odn != null){
    // Restore old context
    symbolTable.popContext();
    }
    
    // if the function body turned out to be non-recursive, then we
    // should null-out the fcnDefForRecursion ref put in place above,
    // since it is unnecessary for a nonrecursive func
    if (oan.getOperator().getName() == OP_nrfs) {
      oan.makeNonRecursive();
    }
  } // end processFunction() 

  private final ExprNode processLetIn(TreeNode treeNode, TreeNode[] children, 
                                      ModuleNode cm)
  throws AbortException {
    TreeNode[] syntaxTreeNode = children[1].heirs(); // extract LetDefinitions
    Vector   defVec = new Vector(4);
    Vector   instVec = new Vector(1);

    Context letCtxt = new Context(moduleTable, errors) ;
    symbolTable.pushContext(letCtxt);
      /*********************************************************************
      * Create a new sub-Context for the IN expression, containing the     *
      * LET definitions                                                    *
      *********************************************************************/

    /***********************************************************************
    * Increment curLevel.                                                  *
    ***********************************************************************/
    if (curLevel < MaxLetInLevel) { curLevel++ ; }
     else { errors.addAbort(treeNode.getLocation(),
                            "LETs nested more than " +  MaxLetInLevel + 
                            " deep.") ;
          } ;      
    unresolvedCnt[curLevel] = 0 ;
      /*********************************************************************
      * Will not have been initialized if we haven't yet reached this      *
      * LET/IN nesting depth.                                              *
      *********************************************************************/
      
    for (int lvi = 0; lvi < syntaxTreeNode.length; lvi++) {
      /*********************************************************************
      * Note: LL changed from an "if" and a sequence of "elseif"s to a     *
      * switch statement on 7 Apr 2007 when adding the N_Recursive case.   *
      *********************************************************************/
      switch (syntaxTreeNode[lvi].getKind()) {
        case N_OperatorDefinition :
          processOperator(syntaxTreeNode[ lvi ], defVec, cm);
          break ;

        case N_FunctionDefinition :
          processFunction(syntaxTreeNode[ lvi ], defVec, cm );
          break ;

        case N_ModuleDefinition :
          processModuleDefinition(syntaxTreeNode[lvi], defVec, instVec, cm);
          break ;

        case N_Recursive :
          processRecursive(syntaxTreeNode[ lvi ], cm) ;
          break ;

        default :
          errors.addAbort(syntaxTreeNode[ lvi ].getLocation(),
                           "Internal error: found unexpected syntax " +
                           "tree node in LET.") ;
       } // switch
     } // for

    checkForUndefinedRecursiveOps(cm) ;

    /***********************************************************************
    * Decrement curLevel.                                                  *
    ***********************************************************************/
    curLevel -- ;
    if (curLevel < 0) { curLevel = 0;} ;


    ExprNode body = generateExpression(children[3], cm);

    /***********************************************************************
    * Convert from Vector to array of SymbolNode, whose elements may be    *
    * OpDefNode or ThmOrAssumpDefNode objects.                             *
    ***********************************************************************/
    SymbolNode[] opDefs = new SymbolNode[defVec.size()];
    for (int i = 0; i < opDefs.length; i++) {
      opDefs[i] = (SymbolNode)defVec.elementAt(i);
    }

    InstanceNode[] insts = new InstanceNode[instVec.size()];
    for (int i = 0; i < insts.length; i++) {
      insts[i] = (InstanceNode)instVec.elementAt(i);
    }
    LetInNode letIn = new LetInNode(treeNode, opDefs, insts, body, letCtxt);
    symbolTable.popContext();
    return letIn;
  } // end processLetIn

  private final ExprNode generateExpression(TreeNode treeNode, ModuleNode cm)
   throws AbortException {
    /***********************************************************************
    * Must return an ExprNode that represents an expression, and not a     *
    * labeled ASSUME/PROVE                                                 *
    ***********************************************************************/
    return generateExpressionOrLAP(treeNode, cm, false) ;
   }

  private final ExprNode generateExpressionOrLAP(
                 TreeNode treeNode, ModuleNode cm, boolean allowLabeledAP)
    /***********************************************************************
    * Can return a LabelNode labeling an ASSUME/PROVE iff allowLabeledAP   *
    * = true.  Otherwise, it can return only an ExprNode that represents   *
    * an expression.                                                       *
    ***********************************************************************/
  throws AbortException {
    TreeNode[]        children = treeNode.heirs();
    TreeNode[]        ss       = null; // grandchildren
    SymbolNode        opn      = null;
    TreeNode          op       = null;
    GenID             genID;
    ExprOrOpArgNode[] sns;             // a ExprNode list used for arguments
   
    switch (treeNode.getKind()) {

    case N_Real :
      return new DecimalNode(children[0].getImage(),children[2].getImage(), treeNode);

    case N_Number :
      return new NumeralNode( children[0].getImage(), treeNode);

    case N_String :
      return new StringNode( treeNode, true);

    case N_ParenExpr :
      return generateExpression( children[1], cm );

    case N_InfixExpr :
      genID = generateGenID(children[1], cm);

      sns = new ExprOrOpArgNode[2];
      opn = symbolTable.resolveSymbol(Operators.resolveSynonym(genID.getCompoundIDUS()));
      if ( opn == null ) {
        errors.addError(treeNode.getLocation(),
                        "Couldn't resolve infix operator symbol `" + 
                        genID.getCompoundIDUS() + "'." );
        return null;
      }

      sns[0] = generateExpression( children[0], cm );
      sns[1] = generateExpression( children[2], cm );
      return new OpApplNode(opn, sns, treeNode, cm);

    case N_PrefixExpr :
      // 1 get gen operator node
      ss = children[0].heirs();

      // 2 get rightmost part of the possibly compound Op itself;
      op = ss[1];
      genID = generateGenID(children[0], cm, true);
      sns = new ExprOrOpArgNode[1];
      opn = symbolTable.resolveSymbol(Operators.resolveSynonym(genID.getCompoundIDUS()));

      if ( opn == null ) {
        errors.addError(treeNode.getLocation(), 
                        "Couldn't resolve prefix operator symbol `" + 
                        genID.getCompoundIDUS() + "'." );
        return null;
      } 

      sns[0] = generateExpression( children[1], cm );
      return new OpApplNode(opn, sns, treeNode, cm);    // constructor 2 

    case N_PostfixExpr :
      genID = generateGenID(children[1], cm);

      sns = new ExprNode[1];
      opn = symbolTable.resolveSymbol(Operators.resolveSynonym(genID.getCompoundIDUS()));
      if ( opn == null ) {
        errors.addError(treeNode.getLocation(), "Couldn't resolve postfix " +
                        "operator symbol `" + genID.getCompoundIDUS() + "'.");
        return null;
      }

      sns[0] = generateExpression( children[0], cm );
      return new OpApplNode(opn, sns, treeNode, cm);  // constructor 2 

    case N_Times : // or cartesian product
      sns = new ExprNode[ (children.length+1)/2 ];  

      for (int lvi = 0; lvi < sns.length; lvi ++ ) {
        sns[ lvi ]  = generateExpression( children[ 2 * lvi ], cm );
      }
      return new OpApplNode(OP_cp, sns, treeNode, cm);  // constructor 3 

    case N_SetEnumerate :
      int size = (children.length-1) / 2;
      sns = new ExprNode [size];
      for ( int lvi = 0; lvi < size; lvi++ ) {
        sns[lvi] = generateExpression( children[ 2 * lvi + 1 ], cm );
      }
      return new OpApplNode(OP_se, sns, treeNode, cm);  // constructor 3 

    case N_GeneralId :
      // This is a zero-ary operator; it should show in the syntax
      // tree as an OpApp, but it does not.  Hence, an OpApplication
      // node with zero arguments must be constructed for it
      // if we get here, the GeneralID really is an OpApplication with 0
      // primary arguments, but with any number of prefix arguments

      // process the generalized identifier, complete with its
      // embedded argument lists (if any)

      /*********************************************************************
      * If the N_GeneralId represents the identifier "@", then check for   *
      * errors and return an AtNode if none.                               *
      *********************************************************************/
      SyntaxTreeNode sTreeNode = (SyntaxTreeNode) treeNode ;
      if (   (sTreeNode.heirs()[1].getKind() == IDENTIFIER)
          && (sTreeNode.heirs()[1].getUS() == AtUS)
          && (((SyntaxTreeNode) sTreeNode.heirs()[0]).heirs().length == 0) ) {
        if (excStack.empty() || excSpecStack.empty()) {
          // if either stack is empty, then @ used in improper EXCEPT context
          errors.addError(sTreeNode.getLocation(),
                          "@ used where its meaning is not defined.");
          return nullOAN ;
        }
        else { 
          // So, the context for @ is proper, then construct the 
          // AtNode and return it
          return new AtNode((OpApplNode)excStack.peek(),
                            (OpApplNode)excSpecStack.peek());
        }
      } ;

      ExprNode retVal = 
         (ExprNode) selectorToNode(genIdToSelector(sTreeNode), 
                                    0, false, false, cm) ;

      /*********************************************************************
      * A function definition generates an OpDefNode whose body is an      *
      * OpApplNode whose operator is either $RecursiveFcnSpec or           *
      * $NonRecursiveFcnSpec, the latter when the definition is            *
      * recursive.  However, in SANY1 the definition                       *
      *                                                                    *
      *    f[x \in S] == ...                                               *
      *                                                                    *
      * was found to be recursive only if a subexpression f[...] occurs    *
      * in the body.  It was not marked as recursive if another instance   *
      * of f occurs, such as Foo(f).  To fix this, we need to check if     *
      * this genID is actually the Identifier of a function currently      *
      * being defined.  The following call to functions.recursionCheck     *
      * does that.                                                         *
      *********************************************************************/
      if (retVal.getKind() == OpApplKind) {
        functions.recursionCheck(
           ((OpApplNode) retVal).getOperator().getName()) ;
       } ;

      return retVal ;
 /**************************  old version
      genID = generateGenID(treeNode, cm);

      // if the symbol is "@" then check for errors and 
      // return an AtNode if none.
      if (genID.getCompoundIDUS() == S_at) {
        if (excStack.empty() || excSpecStack.empty()) {
          // if either stack is empty, then @ used in improper EXCEPT context
          errors.addError(treeNode.getLocation(),
                          "@ used where its meaning is not defined.");
        }
        else { 
          // So, the context for @ is proper, then construct the 
          // AtNode and return it
          return new AtNode((OpApplNode)excStack.peek(),
                            (OpApplNode)excSpecStack.peek());
        }
      }
      else if (genID.getFullyQualifiedOp() == null 
                 || genID.getArgs() == null) {
        // If it is not an "@" symbol, it may still be an unresolved symbol
        return nullOAN;
      }
      else if (genID.getFullyQualifiedOp().getKind() == ModuleKind) {
        errors.addError(
          treeNode.getLocation(),
          "Module name '" + genID.getFullyQualifiedOp().getName() +
          "' used as operator.");
        return nullOAN;
      }
      else {
        // but if there are no problems then we are in a situation in
        // which return the appropriate OpApplNode an N_GenID node in
        // the syntax tree really stands for an OpApplication

//      *********************************************************************
//      * Modified on 20 Apr 2007 by LL to correct the following bug.        *
//      *                                                                    *
//      * A function definition generates an OpDefNode whose body is an      *
//      * OpApplNode whose operator is either $RecursiveFcnSpec or           *
//      * $NonRecursiveFcnSpec, the latter when the definition is            *
//      * recursive.  However, the definition                                *
//      *                                                                    *
//      *    f[x \in S] == ...                                               *
//      *                                                                    *
//      * was found to be recursive only if a subexpression f[...] occurs    *
//      * in the body.  It was not marked as recursive if another instance   *
//      * of f occurs, such as Foo(f).  To fix this, we need to check if     *
//      * this genID is actually the Identifier of a function currently      *
//      * being defined.  The call to functions.recursionCheck was added     *
//      * here to do that.                                                   *
//      *********************************************************************
      SymbolNode symNode = genID.getFullyQualifiedOp() ;

      if (symNode.getKind() == ThmOrAssumpDefKind) {
        errors.addError(treeNode.getLocation(),
                        "Theorem or Assumption name used as expression.") ;
       };
      OpApplNode retVal = 
       // return 
         new OpApplNode(symNode, genID.getArgs(), 
                              treeNode, cm);
      functions.recursionCheck(symNode.getName());
      return retVal ;
      }

 ******************************* old version ******************/
    case N_OpApplication:
      // for an operator with arguments
      // Note: in neither case can this be an operator passed as an argument; 
      // the opAppl argument forces the return of an Operator application
      // operators passed as arguments generate OpArg nodes, and that 
      // can happen only in certain contexts, not in every context where an 
      // expression can occur, which is the context we are in here

      SyntaxTreeNode genIdNode  = (SyntaxTreeNode) treeNode.heirs()[0] ;
      SyntaxTreeNode opApplNode = (SyntaxTreeNode) treeNode.heirs()[1] ;

      /*********************************************************************
      * First a check.  It appears that the children of an OpApplication   *
      * node must be a GeneralId node and an OpArgs node, but let's be     *
      * sure.                                                              *
      *********************************************************************/
      if (   (genIdNode.getKind() != N_GeneralId) 
          || (opApplNode.getKind() != N_OpArgs)) {
          errors.addAbort(
            treeNode.getLocation(),
            "Internal error: OpAppl node with unexpected children.",
            true);
        } ;

      Selector sel = genIdToSelector(genIdNode) ;
      sel.args[sel.args.length - 1] = opApplNode ;
      sel.selSTN = (SyntaxTreeNode) treeNode ;
        /*******************************************************************
        * For error reporting, make the syntax tree node of the selector   *
        * include both the general ID node and its argument.               *
        *******************************************************************/
      return (ExprNode) selectorToNode(sel, 0, false, false, cm) ;

/***************** old version *********************
      return generateOpAppl(treeNode, cm);
************************/

    case N_Tuple :
      size = (children.length - 1) / 2;
      sns = new ExprNode [size];
      for ( int lvi = 0; lvi < size; lvi++ ) {
        sns[lvi] = generateExpression( children[ 2 * lvi + 1 ], cm );
      }
      return new OpApplNode(OP_tup, sns, treeNode, cm); // Constructor 3 

    case N_FcnAppl :  // Apparent function application
      // Number of arguments to the apparent func app
      int numArgs = (children.length - 2) / 2;

      // Function appl involves two semantic nodes: 1 for function,
      // and 1 for arg or args tuple.
      sns = new ExprNode[2];

      // Generate expression tree for the function itself
      sns[0] = generateExpression( children[0], cm );  

      if (sns[0] == null) {return null;} ;
        /*******************************************************************
        * sns[0] can be null if the parsing the function generates an      *
        * error (which is the case if the function is missing).            *
        * Added by LL on 29 Feb 2008                                       *
        *******************************************************************/
        
      // If the function is an OpApplNode (and could it be otherwise?)
      if (sns[0].getKind() == OpApplKind) { 
        // Note if this is a recursive function, and change the top level
        functions.recursionCheck(((OpApplNode)sns[0]).getOperator().getName());
      }

      // We next check that the number of arguments to a user-defined
      // function is correct, if possible.

      // Retrieve the expression that represents the function being
      // applied, i.e. the 1st arg to $FcnApply
      ExprOrOpArgNode fcn = sns[0];

      // The entire next conditional is for one purpose: to make sure
      // that a function symbol is applied to the right number of
      // arguments, when it is possible to do that during semantic
      // analysis.  This means that if a function is declared with,
      // say, 3 parameters, e.g. "f[a,b,c] == {a,b,c}", then it is
      // never used with 2 or 4 arguments.  However, it can appear
      // with zero arguments as the expression "f" (not as "f[]"), and
      // it can appear with one argument, as in "f[e]", because e
      // might be a 3-tuple value.  (Whether it always is or not
      // cannot be determined at the time of semantic analysis.)
      // Furthermore a function declared with exactly one parameter
      // can appear with any number of argument expressions because,
      // e.g. f[1,2,3,4] is considered just an alternate way of
      // writing f[<<1,2,3,4>>], so there is really just one argument
      // value.

      // If it is an OpApplNode (as opposed to, say, an OpDeclNode)
      if ( fcn instanceof OpApplNode ) {
        // Retrieve the function being applied
        SymbolNode funcOperator = ((OpApplNode)fcn).getOperator();

        // If the function being applied is a user-defined function
        // (as opposed to OpDeclNode, FormalParamNode, builtin
        // operator, or expression)
        if (funcOperator instanceof OpDefNode &&  
            funcOperator.getKind() == UserDefinedOpKind) {
          // Retrieve the function body expression
          ExprOrOpArgNode funcBody = ((OpDefNode)funcOperator).getBody();

          // if the function body is an OpApplNode (as opposed to,
          // say, NumeralNode, DecimalNode, etc.)
          if (funcBody instanceof OpApplNode && 
              (((OpApplNode)funcBody).getOperator().getName()==OP_nrfs  ||
               ((OpApplNode)funcBody).getOperator().getName()==OP_rfs )) {

            // find out how many arguments it is SUPPOSED to have
            int numParms = ((OpApplNode)funcBody ).getNumberOfBoundedBoundSymbols();
                                                  
            // If the function appears with numArgs >= 2 argument
            // expressions, it must be declared with exactly numArgs
            // parameters; and a function with numParms parameters in
            // its definition should be applied to exactly numParms
            // expressions, or 1 expression (representing arguments in
            // tuple form), or 0 expressions (representing the
            // function itself).  Note: one cannot define a function
            // with 0 arguments in TLA+.
            if ( numArgs >= 2 && numParms != numArgs ) {
              errors.addError(treeNode.getLocation(), 
                              "Function '" + 
                                ((OpApplNode)sns[0]).getOperator().getName() +
                              "' is defined with " + numParms +
                              " parameters, but is applied to " + 
                              numArgs + " arguments.");
              return nullOAN;
            } // end if
          } // end if
        } // end if
      } // end if

      // Assert.check(numArgs > 0);
      if (numArgs == 1) {
        sns[1] = generateExpression(children[2], cm);
      }
      else {
        // If there is more than one arg we have to create a tuple for the arguments.
        ExprOrOpArgNode[] exprs = new ExprNode[ numArgs ];  // One for each of the arguments

        // For each argument...
        for (int lvi = 0; lvi < numArgs; lvi++) {
          // Create the expression for that argument
          exprs[lvi] = generateExpression( children[ 2+2*lvi ], cm );
        }
        // Create an application of $Tuple
        sns[1] = new OpApplNode(OP_tup, exprs, treeNode, cm);
      }
      // Create the function application node.
      return new OpApplNode(OP_fa, sns, treeNode, cm);

    case N_UnboundOrBoundChoose :
      return processChoose(treeNode, children, cm );

    case N_BoundQuant :
      return processBoundQuant(treeNode, children, cm);

    case N_UnboundQuant :
      return processUnboundQuant( treeNode, children, cm );

    case N_IfThenElse :
      sns = new ExprNode[3];
      sns[0] = generateExpression( children[1], cm );
      sns[1] = generateExpression( children[3], cm );
      sns[2] = generateExpression( children[5], cm );
      return new OpApplNode(OP_ite, sns, treeNode, cm);

    case N_Case :
      return processCase(treeNode, children, cm);

    case N_DisjList:
    case N_ConjList:
      sns = new ExprNode[ children.length ];
      for (int lvi = 0; lvi< sns.length; lvi++ ) {
        sns[lvi] = generateExpression( children[lvi].heirs()[1], cm ); 
      }
      if ( treeNode.isKind(N_DisjList ) )
        return new OpApplNode(OP_dl, sns, treeNode, cm);
      else
        return new OpApplNode(OP_cl, sns, treeNode, cm);

    case N_RecordComponent : // really RcdSelect in the API
      sns = new ExprNode[2];
      sns[0] = generateExpression( children[0], cm );
      sns[1] = new StringNode(children[2], false);
      return new OpApplNode(OP_rs, sns, treeNode, cm);

    case N_SetOfFcns:   /* [S -> T] */
      sns = new ExprNode[2];
      sns[0] = generateExpression( children[1], cm );
      sns[1] = generateExpression( children[3], cm );

      return new OpApplNode(OP_sof, sns, treeNode, cm);

    case N_SubsetOf :
      return processSubsetOf( treeNode, children, cm );

    case N_SetOfAll :
      return processSetOfAll( treeNode, children, cm );

    case N_RcdConstructor:
      return processRcdForms( OP_rc, treeNode, children, cm );

    case N_SetOfRcds:
      return processRcdForms( OP_sor, treeNode, children, cm );

    case N_FcnConst:
      return processFcnConst( treeNode, children, cm );

    case N_ActionExpr:
    case N_FairnessExpr:
      return processAction( treeNode, children, cm );

    case N_Except:
      return processExcept( treeNode, children, cm );

    case N_LetIn:
      return processLetIn( treeNode, children, cm );

    case N_Lambda:
      errors.addError(
        treeNode.getLocation(),
        "LAMBDA expression used where an expression is required." );
      return null;

    case N_Label:
      LabelNode ln = generateLabel(treeNode, cm);
      if (ln.isAssumeProve && !allowLabeledAP) {
        errors.addError(
          treeNode.getLocation(),
          "Labeled ASSUME/PROVE used where an expression is required." );
       }
      return ln ;

    default:
      errors.addError(treeNode.getLocation(),
                      "Unsupported expression type `" + 
                      treeNode.getImage() + "'.");
      return null;

    } // end switch

  } // end generateExpression()

/***************************************************************************
* The following variables are used in the processing of ASSUME/PROVE       *
* nodes, and the labels that lie within them.                              *
***************************************************************************/
  private int assumeProveDepth = 0 ;
    /***********************************************************************
    * The nesting depth of ASSUME/PROVEs within which the node corrently   *
    * being processed lies.  In                                            *
    *                                                                      *
    *   THEOREM ASSUME P PROVE Q                                           *
    *                                                                      *
    * the nodes for P and Q are at depth 1 (not 0).                        *
    ***********************************************************************/

  private ThmOrAssumpDefNode currentGoal = null ;
  private int currentGoalClause ;
    /***********************************************************************
    * currentGoal is the named theorem or proof-step node within           *
    * which lies the current node that is being processed, or null if      *
    * we're not inside such a step.  If currentGoal != null, and we're     *
    * within an ASSUME/PROVE step (which is true iff assumeProveDepth >    *
    * 0), then then currentGoalClause equals the clause of within which    *
    * the node being processed lies.  (If we're processing Q in ASSUME P   *
    * PROVE Q, then Q = 1.)                                                *
    ***********************************************************************/

  private static final int maxAPDepth = 100 ;
    /***********************************************************************
    * Maximum allowed nesting depth of ASSUME/PROVES. 100 ought to         *
    * suffice.                                                             *
    ***********************************************************************/

  private boolean[] inScopeOfAPDecl = new boolean[maxAPDepth] ;
    /***********************************************************************
    * For all i \leq assumeProveDepth, inScopeOfAPDecl[i] = true iff the   *
    * node currently being processed lies within a declaration made at     *
    * assumeProveDepth = i.  Thus in                                       *
    *                                                                      *
    *   THEOREM ASSUME NEW x \in S,                                        *
    *                  P,                                                  *
    *                  ASSUME R , ACTION A PROVE T                         *
    *           PROVE  Q                                                   *
    *                                                                      *
    * inScopeOfAPDecl[1] equals false when S is being processed and        *
    * equals true when P, Q, R, and T are being processed.                 *
    *                                                                      *
    * inScopeOfAPDecl[2] equals false when R is being processed and true   *
    * when T is being processed.                                           *
    ***********************************************************************/


  private boolean noLabelsAllowed() {
    /***********************************************************************
    * This returns true if we are inside an ASSUME/PROVE node where a      *
    * label is not allowed because we are in the scope of a declaration    *
    * from an inner ASSUME/PROVE.                                          *
    ***********************************************************************/
    for (int i = 2; i <= assumeProveDepth; i++) {
      if (inScopeOfAPDecl[i]) { return true ; } ;
      } ;
    return false ;
   }


  private final boolean illegalLabelRef(LabelNode ln, SyntaxTreeNode stn) 
    throws AbortException {
    /***********************************************************************
    * True iff we are currently in a point where a reference to this       *
    * label is illegal because it lies inside an ASSUME/PROVE clause from  *
    * outside the scope of a symbol it may contain.  See the comments in   *
    * AssumeProveNode.java for an explanation of this method.              *
    ***********************************************************************/
    ThmOrAssumpDefNode goal = ln.goal ;
    if (goal == null) { return false ; } ;
    if (   (goal.getBody() == null)
        || (goal.getBody().getKind() != AssumeProveKind)) {
       errors.addAbort(
         stn.getLocation(),
         "Internal error: Expecting label to be in AssumeProveNode, " +
         "but it's not.") ;
      } ;
    AssumeProveNode ap = (AssumeProveNode) goal.getBody() ;
    return    ap.inScopeOfDecl[ln.goalClause]
           && (goal.isSuffices() == ap.inProof) ;
   } // illegalLabelRef

  private final boolean illegalAPPosRef(AssumeProveNode ap, int pos) {
    /***********************************************************************
    * True iff it is illegal for the node currently being processed to     *
    * access the clause number pos of AssumeProve node ap because it is    *
    * not in the scope of symbols declared in previous ASSUME clauses of   *
    * ap.  See the comments in AssumeProveNode.java for an explanation of  *
    * this method.                                                         *
    ***********************************************************************/
    return    ap.inScopeOfDecl[pos-1]
           && (   (ap.getGoal() == null)
               || (ap.getGoal().isSuffices() == ap.inProof)) ;
    }
  

// XXXX Currently, this handles both label and positional subexpression
// specifiers.  To handle positional ones, we need to know what
// the position is.
//  private final boolean withinScopeOf(SemanticNode goal) {
  /*************************************************************************
  * Returns true iff the node currently being processed lies within the    *
  * scope of (the declarations made in the ASSUME clauses) of goal, which  *
  * will be a TheoremNode or a proof-step node.                            *
  *                                                                        *
  * XXXXX Dummy implementation for now.                                    *
  *************************************************************************/
//  return true;
//    if (goal == null) {return true;} ;
//    return false ;  
//    }         

  // The following objects added 10 Feb 2011 by LL are used to check that
  // a []ASSUME does not lie within the scope of (the assumptions of)
  // an ordinary ASSUME.  It does this by declaring the dummy OpDeclNode
  // InAssumeDummyNode as if it were declared within the ASSUME and then
  // checking if it's defined where the []ASSUME is used.
  private final static UniqueString S_InAssume = UniqueString.uniqueStringOf("$$InAssume");
  private final static OpDeclNode InAssumeDummyNode = 
     new OpDeclNode(S_InAssume, 0, 0, 0, null, null, null) ;

  private final AssumeProveNode 
                   generateAssumeProve(TreeNode treeNode, ModuleNode cm)
    /***********************************************************************
    * Added by LL on 17 Mar 2007.                                          *
    ***********************************************************************/
     throws AbortException { 
       // The following flag is used to record if this is a
       // Following code added on 9 Nov 2009 so that the goal
       // field of the AssumeProveNode is null unless this is
       // a top-level Assume/Prove.
       ThmOrAssumpDefNode cg = null ;
       if (assumeProveDepth == 0) {
           cg = currentGoal;
       } ;
       assumeProveDepth++ ;
       AssumeProveNode apn = new AssumeProveNode(treeNode, cg) ;
       TreeNode[] children = treeNode.heirs();
       int numOfChildren = children.length;
       if (numOfChildren % 2 != 0) { 
           throw new WrongInvocationException("AssumeProve has odd number of children"); } ;
       int numOfAssumptions = (numOfChildren - 2) / 2 ;
       // Check if this is a []ASSUME and that the PROVE matches
       // the ASSUME.  
       boolean isBoxAssumeProve = false;
       String proveString = children[children.length -2].getImage();
       if (children[0].getImage().equals("[]ASSUME")) {
           isBoxAssumeProve = true;
           if (!proveString.equals("[]PROVE")) {
               errors.addError(children[0].getLocation(), 
               "[]ASSUME matched by PROVE instead of []PROVE");
           } 
       } else {
           if (!proveString.equals("PROVE")) {
               errors.addError(children[0].getLocation(), 
               "ASSUME matched by []PROVE instead of PROVE");
           } 
       }
       apn.setIsBoxAssumeProve(isBoxAssumeProve);
       
       apn.assumes = new LevelNode[numOfAssumptions] ;
       boolean inDeclScope = false ;
         /******************************************************************
         * Set true when after we've processed a declaration.              *
         ******************************************************************/
       apn.inScopeOfDecl = new boolean[numOfAssumptions + 1] ;
       apn.inScopeOfDecl[0] = false ; 
       inScopeOfAPDecl[assumeProveDepth] = false ;
       if (assumeProveDepth != 1) {
         /******************************************************************
         * The context is pushed by the top-level caller of                *
         * generateAssumeProve, which is processTheorem.                   *
         ******************************************************************/
         symbolTable.pushContext(new Context(moduleTable, errors)) ;
         /******************************************************************
         * I don't understand exactly what's going on here, but this       *
         * seems to be the magic incantation for starting a new context    *
         * into which declarations among the assumptions should be put     *
         * for interpreting expressions later in the assumption list and   *
         * in the "prove" expression.                                      *
         ******************************************************************/
        } // if
       
       if (isBoxAssumeProve) {
           if (symbolTable.resolveSymbol(S_InAssume) != null) {
               errors.addError(children[0].getLocation(), 
               "[]ASSUME used within the scope of an ordinary ASSUME's assumptions"); 
           }
       } else {
           if (symbolTable.resolveSymbol(S_InAssume) == null) {
               symbolTable.addSymbol(S_InAssume, InAssumeDummyNode); 
           } 
       }
       
       if (assumeProveDepth == 1) {currentGoalClause = 0 ; } ;
       for (int i = 0 ; i < numOfAssumptions ; i++) {
         /******************************************************************
         * The current assumption is assumption number i+1 (in human       *
         * numbering).                                                     *
         ******************************************************************/
         apn.inScopeOfDecl[i+1] = apn.inScopeOfDecl[i] ; 
         TreeNode tn = children[2*i + 1] ;
         switch (tn.getKind()) {
           case N_AssumeProve :
             apn.assumes[i] = generateAssumeProve(tn, cm) ;
             break ;
           case N_NewSymb :
             apn.assumes[i] = generateNewSymb(tn, cm) ;
             apn.inScopeOfDecl[i+1] = true ;
             inScopeOfAPDecl[assumeProveDepth] = true ;
             OpDeclNode[] odn = new OpDeclNode[1] ;
             odn[0] = ((NewSymbNode) apn.assumes[i]).getOpDeclNode() ;
             break ;
           default :
             /**************************************************************
             * Should be an expression node or a labeled ASSUME/PROVE.     *
             **************************************************************/
//             apn.assumes[i] = generateExpression(tn, cm) ;
             apn.assumes[i] = generateExpressionOrLAP(tn, cm, true) ;
             break ;
           } ; // end switch
         if (assumeProveDepth == 1) {
           currentGoalClause = currentGoalClause + 1;
          } ;
        } ; // end for 

       apn.prove = generateExpression(children[numOfChildren - 1], cm) ;

       if (assumeProveDepth != 1) {
         symbolTable.popContext();
           /****************************************************************
           * Restore the current context, removing the declarations by     *
           * the assumptions.  assumption list.                            *
           ****************************************************************/
         } ;
       assumeProveDepth-- ;
       return apn ; }

  private final NewSymbNode generateNewSymb(TreeNode treeNode, ModuleNode cm)
    /***********************************************************************
    * Added by LL on 21 Mar 2007.                                          *
    ***********************************************************************/
    throws AbortException { 
      TreeNode[] children = treeNode.heirs();
      int numOfChildren = children.length;

      /*********************************************************************
      * Determine if this node should have a non-null "set" field, which   *
      * is the case iff the declaration ends with "\in S", in which case   *
      * set the set field to the ExprNode for S.                           *
      *********************************************************************/
      ExprNode set = null ;
      if (children[numOfChildren-2].getKind() == IN) {
        set = generateExpression(children[numOfChildren-1], cm) ;} ;
      
      int declKind ;
      int declLevel ;
      /*********************************************************************
      * Set declKind to the kind of the NewSymbNode object's OpDeclNode.   *
      * Set declLevel to its level.                                        *
      *                                                                    *
      * Start by setting i to 1 or 0 depending on whether the declaration  *
      * begins with a NEW token.                                           *
      *********************************************************************/
      int i = 0 ;
      if (children[0].getKind() == NEW) {i = 1;};

      /*********************************************************************
      * Set declKind, and leave i so that children[i+1] is the syntax      *
      * tree node describing the declared symbol and its arity.            *
      *                                                                    *
      * We do this by seeing if the next token is "CONSTANT", "VARIABLE",  *
      * etc.  If it isn't, then the declaration begins "NEW id", so it's   *
      * a CONSTANT declaration and i must be set to 0.                     *
      *********************************************************************/
      switch (children[i].getKind()) {
        case CONSTANT :
               declKind  = NewConstantKind ;
               declLevel = ConstantLevel;
               break ;
        case VARIABLE :
               declKind  = NewVariableKind ;
               declLevel = VariableLevel;
               break ;
        case STATE :
               declKind  = NewStateKind ;
               declLevel = VariableLevel;
               break ;
        case ACTION :
               declKind  = NewActionKind ;
               declLevel = ActionLevel;
               break ;
        case TEMPORAL :
               declKind  = NewTemporalKind ;
               declLevel = TemporalLevel;
               break ;
        default :
               declKind  = NewConstantKind ;
               declLevel = ConstantLevel;
               i = 0 ;
       }; // switch
      return new NewSymbNode(
                   buildParameter(children[i+1], declKind, declLevel, cm, true),
                   set,
                   treeNode) ;
    }   

  private final ExprNode 
       processChoose(TreeNode treeNode, TreeNode[] children, ModuleNode cm) 
  throws AbortException {
    ExprNode[]   semanticNode   = new ExprNode[1];
    TreeNode[]   syntaxTreeNode = children[2].heirs();
    OpApplNode   result;

    symbolTable.pushContext( new Context(moduleTable, errors) );

    if (syntaxTreeNode == null || syntaxTreeNode.length == 0) {
      // unbounded case
      FormalParamNode[] odn;
      boolean      tuple;

      // either Tuple or single identifier
      if (children[1].isKind( N_IdentifierTuple)) {
        syntaxTreeNode = children[1].heirs();
        odn = new FormalParamNode[ syntaxTreeNode.length / 2 ];
        for (int lvj = 0; lvj < syntaxTreeNode.length / 2; lvj++ ) {
          odn[lvj] = new FormalParamNode(
                          syntaxTreeNode[ 2*lvj+1 ].getUS(), 0, 
                          syntaxTreeNode[ 2*lvj+1 ], symbolTable, cm);
        }
        tuple = true;
      }
      else {
        odn = new FormalParamNode[1];
        odn[0] = new FormalParamNode(children[1].getUS(), 0, children[0],
                                     symbolTable, cm);
        tuple = false;
      } 
      pushFormalParams(odn) ;
        /*******************************************************************
        * Push formal parameters on Last(LS).paramSeq for processing the   *
        * body.                                                            *
        *******************************************************************/
      semanticNode[0] = generateExpression( children[4], cm );
      popFormalParams() ;

      result =  new OpApplNode(OP_uc, semanticNode, odn, treeNode, cm);
    }
    else {
      // bounded case
      FormalParamNode[][] odna   = new FormalParamNode[1][0];
      boolean[]      tuples = new boolean[1];
      ExprNode[]     exprs  = new ExprNode[1]; 

      // syntaxTreeNode can be reused further down.
      exprs[0] = generateExpression(syntaxTreeNode[1], cm);

      if ( children[1].isKind( N_IdentifierTuple ) ) {
        syntaxTreeNode = children[1].heirs();
        odna[0] = new FormalParamNode[ syntaxTreeNode.length / 2 ];
        for (int lvj = 0; lvj < syntaxTreeNode.length / 2; lvj++ ) {
          odna[0][lvj] = 
            new FormalParamNode(
                  syntaxTreeNode[ 2*lvj+1 ].getUS(), 0,
                  syntaxTreeNode[2*lvj+1], symbolTable, cm);
        }
        tuples[0] = true;
      }
      else {
        odna[0] = new FormalParamNode[1];
        odna[0][0] = new FormalParamNode(children[1].getUS(), 0,
                                         children[1], symbolTable, cm);
        tuples[0] = false;
      } 
      pushFormalParams(flattenParams(odna)) ;
        /*******************************************************************
        * Push the bound variables on Last(LS).paramSeq and process the    *
        * body of the CHOOSE.                                              *
        *******************************************************************/
      semanticNode[0] = generateExpression( children[4], cm );
      popFormalParams() ;

      result = new OpApplNode(OP_bc, null, semanticNode, odna, 
                              tuples, exprs, treeNode, cm);
    }
    symbolTable.popContext();
    return result;
  }

  private final ExprNode processBoundQuant(TreeNode treeNode, 
                                           TreeNode[] children,
                                           ModuleNode cm) 
  throws AbortException {
    // Create data structures for all parameters
    int            length = (children.length - 2) / 2;
    FormalParamNode[][] odna   = new FormalParamNode[length][0];
    boolean[]      bt     = new boolean[length];
    ExprNode[]     ea     = new ExprNode[ length ];

    // then process parameters
    symbolTable.pushContext( new Context(moduleTable, errors) );
    processQuantBoundArgs( children, 1, odna, bt, ea, cm );

    // process expression
    ExprNode semanticNode[] = new ExprNode[1];
      pushFormalParams(flattenParams(odna)) ;
        /*******************************************************************
        * Push the bound variables on Last(LS).paramSeq and process the    *
        * body of the quantified expression.                               *
        *******************************************************************/
    semanticNode[0] = generateExpression( children[ children.length - 1 ], cm );
    popFormalParams() ;

    symbolTable.popContext();

    // then return new node.
    // which variety? look under first child.
    boolean isExists =    children[0].getUS().equals( S_e ) 
                       || children[0].getUS().equals( S_ex );
    if (isExists) {
      return new OpApplNode(OP_be, null, semanticNode, odna, 
                            bt, ea, treeNode, cm);
    }
    else {
      return new OpApplNode(OP_bf, null, semanticNode, odna, 
                            bt, ea, treeNode, cm);
    }
  }

  private final ExprNode processUnboundQuant(TreeNode treeNode, 
                                             TreeNode[] children,
                                             ModuleNode cm)
  throws AbortException  {
   // which variety? look under first child.
   UniqueString us = children[0].getUS();
   UniqueString r_us;
   int level;

   if      ( us.equals (S_e ) ) { r_us = OP_ue; level = 0; } // \E
   else if ( us.equals (S_ex) ) { r_us = OP_ue; level = 0; } // \exists
   else if ( us.equals (S_f ) ) { r_us = OP_uf; level = 0; } // \A
   else if ( us.equals (S_fx) ) { r_us = OP_uf; level = 0; } // \always
   else if ( us.equals (S_te) ) { r_us = OP_te; level = 1; } // \EE
   else                         { r_us = OP_tf; level = 1; } // \AA

   // Process all identifiers bound by thus quantifier
   int length = ( children.length - 2 ) / 2;
   FormalParamNode odn[] = new FormalParamNode[ length ];
   symbolTable.pushContext( new Context(moduleTable, errors) );

   for ( int lvi = 0; lvi < length; lvi ++ ) {
     odn[lvi] = new FormalParamNode(
                      children[2*lvi +1].getUS(), 0, 
                      children[2*lvi +1], symbolTable, cm);
   }

   // now the expression
   ExprNode semanticNode[] = new ExprNode[1];
   pushFormalParams(odn) ;
     /**********************************************************************
     * Push formal parameters on Last(LS).paramSeq for processing the      *
     * body.                                                               *
     **********************************************************************/
   semanticNode[0] = generateExpression(children[children.length-1], cm);
   popFormalParams() ;

   // wrap up.
   symbolTable.popContext();
   return new OpApplNode(r_us, semanticNode, odn, treeNode, cm);
  }

  private final ExprNode processCase(TreeNode treeNode, TreeNode[] children, ModuleNode cm) 
  throws AbortException {
    // number of arms to CASE-expr, not counting the CASE nodse itself
    // or the []-separators
    int armCount = children.length/2;          
    ExprNode[] casePairs = new ExprNode[armCount];
    
    for (int lvi = 0; lvi < armCount; lvi++) {
      TreeNode caseArm = children[2*lvi+1];
      TreeNode[] ss = caseArm.heirs();
      ExprNode[] sops = new ExprNode[2];
      if (!caseArm.isKind(N_OtherArm)) {
        sops[0] = this.generateExpression(ss[0], cm);
      }
      sops[1] = this.generateExpression(ss[2], cm);
      casePairs[lvi] = new OpApplNode(OP_pair, sops, caseArm, cm);
    }
    return new OpApplNode(OP_case, casePairs, treeNode, cm);
  }

  private final ExprNode processSubsetOf(TreeNode treeNode, 
                                         TreeNode children[],
                                         ModuleNode cm ) 
  throws AbortException { 
    // cfr. unbounded choose
    ExprNode[]     ops    = new ExprNode[1];
    FormalParamNode[][] odna   = new FormalParamNode[1][0];
    boolean[]      tuples = new boolean[1];
    ExprNode[]     exprs  = new ExprNode[1];

    exprs[0] = generateExpression( children[3], cm  );

    symbolTable.pushContext( new Context(moduleTable, errors) );

    if ( children[1].isKind( N_IdentifierTuple ) ) {
      TreeNode[] ss = children[1].heirs();
      odna[0] = new FormalParamNode[ ss.length / 2 ];
      for (int lvj = 0; lvj < ss.length / 2; lvj++ ) {
        odna[0][lvj] = new FormalParamNode(
                             ss[ 2*lvj+1 ].getUS(), 0, ss[ 2*lvj+1 ],
                             symbolTable, cm);
      }
      tuples[0] = true;
    }
    else {
      odna[0] = new FormalParamNode[1];
      odna[0][0] = new FormalParamNode(
                         children[1].getUS(), 0, children[1], 
                         symbolTable, cm);
      tuples[0] = false;
    }

    pushFormalParams(flattenParams(odna)) ;
      /*********************************************************************
      * Push the bound variables on Last(LS).paramSeq and process the      *
      * body of the CHOOSE.                                                *
      *********************************************************************/
    ops[0] = generateExpression( children[5], cm  );
    popFormalParams() ;

    symbolTable.popContext();
    return new OpApplNode(OP_sso, null, ops, odna, tuples, exprs, 
                          treeNode, cm);
  }

  private final ExprNode processSetOfAll(TreeNode treeNode,
                                         TreeNode children[],
                                         ModuleNode cm) 
  throws AbortException {
    ExprNode[]     ops    = new ExprNode[1];
    int            length = (children.length - 3) / 2;
    FormalParamNode[][] odna   = new FormalParamNode[length][0];
    boolean[]      tuples = new boolean[length];
    ExprNode[]     exprs  = new ExprNode[length];

    symbolTable.pushContext(new Context(moduleTable, errors));
    processQuantBoundArgs(children, 3, odna, tuples, exprs, cm);

    pushFormalParams(flattenParams(odna)) ;
      /*********************************************************************
      * Push the bound variables on Last(LS).paramSeq and process the      *
      * body of the CHOOSE.                                                *
      *********************************************************************/
    ops[0] = generateExpression( children[1], cm  );
    popFormalParams() ;

    symbolTable.popContext();

    return new OpApplNode(OP_soa, null, ops, odna, tuples, exprs,
                          treeNode, cm);
  }

  private final ExprNode processFcnConst(TreeNode treeNode,
                                         TreeNode children[], ModuleNode cm) 
  throws AbortException { 
    ExprNode[]     ops    = new ExprNode[1];
    int            length = (children.length - 3) / 2;    // number of args to function constant
    FormalParamNode[][] odna   = new FormalParamNode[length][0];
    boolean[]      tuples = new boolean[length];
    ExprNode[]     exprs  = new ExprNode[length];

    symbolTable.pushContext( new Context(moduleTable, errors) );
    processQuantBoundArgs( children, 1, odna, tuples, exprs, cm );

    pushFormalParams(flattenParams(odna)) ;
      /*********************************************************************
      * Push the bound variables on Last(LS).paramSeq and process the      *
      * body of the CHOOSE.                                                *
      *********************************************************************/
    ops[0] = generateExpression( children[children.length-2], cm  );
    popFormalParams() ;

   symbolTable.popContext();

    return new OpApplNode(OP_fc, null, ops, odna, tuples, exprs,
                          treeNode, cm);
  }

  /**
   * This method processes both the RecordConstructor construct and the
   * SetOfRecords operator.  The two are essentially identical except for 
   * which builtin operator is used.
   */
  private final ExprNode processRcdForms(UniqueString operator,
                                         TreeNode treeNode,
                                         TreeNode children[],
                                         ModuleNode cm) 
  throws AbortException {
    // handles RcdConstructor or SetOfRcds 
    int length = (children.length - 1) / 2;

    // Create an array of pairs to handle all of the fields mentioned in the form
    ExprNode[] fieldPairs = new ExprNode[length];
    // Create an array of Unique Strings to check uniqueness of fields. Not very efficient
    // but a HashTable may be overkill most of the time.
    // Remember a label is a string.
    UniqueString [] labels = new UniqueString[length]; 

    // For each field in the RcdConstructor or SetOfRecords
    for ( int lvi = 0; lvi < length; lvi++ ) {
      TreeNode syntaxTreeNode[] = children[ 2*lvi + 1].heirs();

      // Create a pair of SemanticNodes to represent one record component
      ExprNode sops[] = new ExprNode[2];

      // The first one gets a new StringNode indicating the field name
      sops[0] = new StringNode(syntaxTreeNode[0], false);
      labels[ lvi ] = ((StringNode) sops[0]).getRep();
      for ( int cmpIndex=0; cmpIndex < lvi; cmpIndex++) {
        if ( labels[lvi].compareTo(labels[cmpIndex]) == 0) {
          errors.addError(syntaxTreeNode[0].getLocation(),
          "Non-unique fields in constructor.");
        }
      }

      // The second one gets the expression indicating the field value (or set of values)
      sops[1] = generateExpression( syntaxTreeNode[2], cm  );

      // Put the $Pair OpApplNode into the fieldPairs array
      fieldPairs[lvi] = new OpApplNode(OP_pair, sops, children[2*lvi+1], cm);
    }
    // Create the top-level OpApplNode, for either the SetOfRecords op
    // or the RcdConstructor op.
    return new OpApplNode(operator, fieldPairs, treeNode, cm);
  }

  private final ExprNode processAction(TreeNode treeNode, TreeNode children[], ModuleNode cm) 
  throws AbortException {
    UniqueString match = children[0].getUS();
    if      ( match.equals( S_a ) )
      match = OP_aa;
    else if ( match.equals( S_brack ) )
      match = OP_sa;
    else if ( match.equals( S_sf) )
      match = OP_sf;
    else if ( match.equals( S_wf) )
      match = OP_wf;

    ExprNode ops[] = new ExprNode[2];
    ops[0] = generateExpression( children[1], cm  );
    ops[1] = generateExpression( children[3], cm  );
    return new OpApplNode( match, ops, treeNode, cm);
  }

  private final ExprNode processExcept(TreeNode treeNode, TreeNode[] children, ModuleNode cm) 
  throws AbortException {
    int              numExcepts = (children.length-3)/2 ;     // number of ExceptSpec's;
    ExprNode[]       operands   = new ExprNode[numExcepts+1]; // 1 for each ExceptionSpec +  first expr
    OpApplNode       excNode;                                 // Holds OpApplNode for $Except operator
    OpApplNode       excSpecNode;                             // Holds $Pair node for ExceptSpec

    // The first operand of the $Except operator is the expression to
    // which the exceptions apply Note this first operand is generated
    // BEFORE the $Except node is stacked in the next couple of lines,
    // because an @ in the first expression does NOT refer to the
    // $Except node currently being generated, but to the next outer
    // $Except node.
    operands[0] = generateExpression( children[ 1 ], cm  );  

    // Create the $Except OpApplNode that will be returned by this
    // method.  We create it now, and fill out its contents later,
    // because we need a reference to it in order to process @ properly.
    excNode = new OpApplNode( OP_exc, operands, treeNode, cm);

    // for each of the ExceptSpecs produce another element of the operands array
    for ( int excSpecIx = 0; excSpecIx < numExcepts; excSpecIx++ ) {
      TreeNode[] syntaxTreeNode = children[3 + 2*excSpecIx].heirs();  // extract ExceptSpec 
      ExprNode[] sops           = new ExprNode[2];                    // Each ExceptionSpec is a $Pair
      int        slength        = syntaxTreeNode.length - 3;          // # of ExceptComponents in ExceptSpec
      ExprNode[] ssops          = new ExprNode[ slength ];            // to store ExceptComponents

      // Process the LHS of the ExceptSpec

      // for each ExceptComponent of the form .h or [i] or [i,j,k] add
      // an arg to $SEQ node and add build up the syntax tree for
      // exceptionTarget
      for ( int excCompIx = 0; excCompIx < slength ; excCompIx++ ) {
        // the heirs of an ExceptComponent
        TreeNode subSyntaxTreeNode[] = syntaxTreeNode[ 1 + excCompIx ].heirs();

        if (subSyntaxTreeNode[0].getUS().equals( S_brack ) ) {
          // The first heir is "[" , indicates one or more fcn args;
          // add expressions as function args
          if ( subSyntaxTreeNode.length > 3 ) {
            // if so, must generate a tuple for comma list of fcn args
            int        sslength = (subSyntaxTreeNode.length-1)/2; // number of func args in comma list
            ExprNode[] sssops   = new ExprNode[ sslength ];       // holds the comma list of fcn args

            // for each of multiple function args in the ExceptComponent
            for (int fArgIx=0; fArgIx < sslength; fArgIx++ ) {
              sssops[ fArgIx ] = generateExpression( subSyntaxTreeNode[1+ 2*fArgIx], cm);
            }

            // add one ExceptComponent to vector of ExceptComponents
            ssops[ excCompIx ] = 
              new OpApplNode(OP_tup, sssops, syntaxTreeNode[2*excCompIx+1], cm);
          }
          else {
            // add one ExceptComponent to vector of ExceptComponents
            ssops[ excCompIx ] = generateExpression( subSyntaxTreeNode[1], cm );
          }
        }
        else {
          // otherwise a "." indicates record selection; add a
          // StringNode operand as record selector add one
          // ExceptComponent to vector of ExceptComponents
          ssops[ excCompIx ] = new StringNode(subSyntaxTreeNode[1], false);
        }
      } // end for (each ExceptionComponent)

      // Create OpAppl for $SEQ applied to array of ExceptComponents
      // following record or func expr or !
      // This is the LHS of an ExceptionSpec
      sops[0] = new OpApplNode(OP_seq, ssops, children[3 + 2*excSpecIx], cm);

      // Process the RHS of the ExceptionSpec

      // Create exceptSpec node now, so that it can be available in
      // case the RHS expression of this ExceptSpec contains an @
      excSpecNode = new OpApplNode(OP_pair, sops, children[3+2*excSpecIx], cm);

      // Push the except node and the except spec node on stacks so
      // that the RHS of the ExceptSpec, which might contain an @, can
      // be evaluated in their "context".
      excSpecStack.push(excSpecNode);
      excStack.push(excNode);

      // Generate the expression constituting the RHS of the
      // ExceptionSpec allow @ in the context of this expression.
      sops[1] = generateExpression(syntaxTreeNode[syntaxTreeNode.length-1], cm );

      // Pop them back off
      excSpecStack.pop();
      excStack.pop();

      // Store excSpecNode as another operand of $Except
      operands[ excSpecIx+1 ] = excSpecNode;
    } // end for (each ExceptionSpec)

    return excNode;
  } // end processExcept()

  /**
   * This method generates an expression tree or an OpArgNode as an
   * argument to an OpApplNode
   * 
   *    mainOp      is the operator under that node
   *    mainSTN     is the "parent" OpApplNode, used in case an error message 
   *                must be generated
   *    argPosition is the argument position (counting from 0) that treeNode 
   *                represents
   *    argRoot     is the argument syntax tree that either becomes an 
   *                ExprNode or an OpArgNode
   *    mn          is the module these expressions are part of
   */
  private ExprOrOpArgNode generateExprOrOpArg(SymbolNode mainOp, 
                                              TreeNode   mainSTN, 
                                              int        argPosition,
                                              TreeNode   argRoot, 
                                              ModuleNode mn) 
  throws AbortException {
    SymbolNode argOp  = null;  
      // the SymbolNode that heads the argRoot expression
    int        argArity;           
      // number of actual arguments under argRoot
    int        arityExpected;      
      // arity that mainOp expects of argument number <argPosition>

    if ( mainOp == null) {
      errors.addError(
         mainSTN.getLocation(),
         "Unable to generate expression or operator argument; " + 
         "this is probably because of previously reported errors." );
      return nullOAN;
    }

    // Are we sure the "operator" is not a ModuleNode?
    if (mainOp instanceof ModuleNode) {
      errors.addError(mainSTN.getLocation(), 
                      "Module name '" + mainOp.getName() + 
                      "' used as operator.");
      return nullOAN;
    }

    // Are there too many arguments to mainOp?
    if (argPosition+1 > mainOp.getArity()) {
      errors.addError(mainSTN.getLocation(), 
                      "Too many arguments for operator '" +
                      mainOp.getName() + "'.  There should be only " + 
                      mainOp.getArity() + "." ); 

      return nullOAN;
    }

    // For user-defined mainOp check the FormalParamNodes array
    // associated with the mainOp to find out whether it expects an
    // operator argument or an ordinary expression argument in
    // position number argPosition.  (Only UserDefined ops can have
    // other multi-arg ops passed to them as params, so we can just
    // assign arityExpected = 0 in other cases.)
    /***********************************************************************
    * In SANY2, mainOp can also be a ModuleInstanceKind, so the if test    *
    * was modified appropriately.                                          *
    ***********************************************************************/
    if (   (mainOp.getKind() == UserDefinedOpKind)
        || (mainOp.getKind() == ModuleInstanceKind)) {
      arityExpected = 
           ((OpDefNode)mainOp).getParams()[argPosition].getArity();
     } else {
      arityExpected = 0;
     };

    // if mainOp expects zero arguments, then it expects an ordinary
    // expression arg in this position, so generate an expression.
    // Any errors will be found in the generateExpression method.
    if ( arityExpected == 0 ) {
      return generateExpression( argRoot, mn );
    }
    else {
      // otherwise, we are expecting an OpArg or Lambda
      /*********************************************************************
      * The following test was originally                                  *
      *                                                                    *
      *   if (argRoot.getImage().equals("N_OpApplication"))                *
      *                                                                    *
      * However, that was not sufficient, because there are lots of other  *
      * nodes that represent expressions.  At best, these caused weird     *
      * error messages.  At worst, as in the case of a number or string,   *
      * they caused an array out of bounds exception when generateGenID    *
      * was called a few lines later.  I hope that the following test      *
      * covers all the cases in which this should be called with argRoot   *
      * not an expression.                                                 *
      *                                                                    *
      * Change made by LL on 9 May 2007.                                   *
      *********************************************************************/
      if ( !(   argRoot.getImage().equals("N_GeneralId")
             || argRoot.getImage().equals("N_GenInfixOp")
             || argRoot.getImage().equals("N_GenNonExpPrefixOp")
             || argRoot.getImage().equals("N_GenPostfixOp")
             || argRoot.getImage().equals("N_GenPrefixOp")   
             || argRoot.getImage().equals("N_Lambda")   )) {
        errors.addError(
          argRoot.getLocation(),
          "An expression appears as argument number " + (argPosition+1) +
          " (counting from 1) to operator '" + mainOp.getName() +
          "', in a position an operator is required.");
        return nullOAN;
       } // end if
      
      if (argRoot.getKind() == N_Lambda) {
        /*******************************************************************
        * The argument is a lambda expression.                             *
        *******************************************************************/
        argOp = generateLambda(argRoot, mn) ;
        if (arityExpected == argOp.getArity()) 
           {return new OpArgNode(argOp, argRoot, mn);} // if
        else { errors.addError(
                mainSTN.getLocation(),
                "Lambda expression with arity " + argOp.getArity() + 
                " used as argument " + (argPosition+1) + 
                " of operator `" + mainOp.getName() +
                "', \nbut an operator of arity " + arityExpected 
                                + " is required.");
               return nullOpArg;
        } // else
       } // if (argRoot.kind == N_Lambda) 
      else { 
        /*******************************************************************
        * The argument is not a lambda expression.                         *
        *******************************************************************/

        /*******************************************************************
        * If the argument is a GeneralId node, then we use                 *
        * genIdToSelector and selectorToNode to generate the OpArg node.   *
        *******************************************************************/
        if (argRoot.getKind() == N_GeneralId) {
          return (ExprOrOpArgNode)
                 selectorToNode(genIdToSelector((SyntaxTreeNode) argRoot), 
                                 arityExpected, false, false, mn);
          } ;
       
        /*******************************************************************
        * If the argument is not a GeneralId node, we use the code from    *
        * SANY1 to generate the OpArg node.                                *
        *******************************************************************/
        GenID genID = generateGenID(argRoot, mn);
        argOp = genID.getFullyQualifiedOp(); ;
  
        // If the symbol has not been defined, then indicate an error and
        // return a nullOAN, allowing semantic analysis to continue
        if (argOp == null) 
          return nullOAN;
  
        argArity = argOp.getArity();
        if ( arityExpected == argArity && genID.getArgs().length == 0) {
          return new OpArgNode(genID.getFullyQualifiedOp(), argRoot, mn);
          }
         else if (genID.getArgs().length > 0) {
          // expression (with or without correct number of args) being 
          // used where operator should be    
          errors.addError(
             mainSTN.getLocation(), 
             "Expression used in argument position " + (argPosition+1) + 
             " (counting from 1) of operator `" + mainOp.getName() +
             "', whereas an operator of arity " + arityExpected + 
             " is required.");
          return nullOpArg;
         }
        else {
        // operator of the wrong arity is being passed as argument
          errors.addError(
             mainSTN.getLocation(),
             "Operator with incorrect arity passed as argument. " + 
             "\nOperator '" + argOp.getName() + "' of arity " + argArity + 
             " is argument number " + (argPosition+1) + 
             " (counting from 1) to operator `" + mainOp + 
             "', \nbut an operator of arity " + arityExpected + 
             " was expected.");
          return nullOpArg;
        }
     } // else of non-Lambda expression case
   }  // end else of if (arityExpected == 0)
  } // end generateExprOrOpArgOrLambda

  /**
   *  Process the General ID syntax tree, i.e. the part that contains
   *  an expression of the form A(x,y)!B!C(u,v,w)!D (with no params to
   *  D) and represents an operator.  A General ID occurs in the
   *  syntax in only a few places: as an operator in an operator
   *  application; as an operator used as an operand to another
   *  operator, and as an operator being substituted for a suitable
   *  constant in module instantiation.
   *
   *  Returns a GenID object, which must be further processed.
   */
  private GenID generateGenID(TreeNode syntaxTreeNode, ModuleNode mn) throws AbortException {
    return generateGenID(syntaxTreeNode, mn, false);
  }

  /*************************************************************************
  * It appears that this is called with unaryNegKludge = true only when    *
  * processing a prefix operator.                                          *
  *************************************************************************/
  private GenID generateGenID(TreeNode syntaxTreeNode, ModuleNode mn, boolean unaryNegKludge)
  throws AbortException {
    GenID      genID;             // Holds components of the generalized ID for this operator
    TreeNode[] children = syntaxTreeNode.heirs(); // To contain N_IdPrefix node and the main operator
    TreeNode[] prefix = null;     // Contains array of prefix elements
                                  // This is the array of N_IdPrefixElements for the operator, 
                                  // i.e. A!B(3)!C has 2 N_IdPrefixElements, A and B(3).
    TreeNode[] prefixElt;         // a prefixElement; 2- or 3-elem array: [op, (args), "!"]
    TreeNode[] allArgs  = null;   // to collect arg arrays from prefix
    TreeNode[] argsList = null;   // Will hold an arg list tree

    if (children == null || children.length <= 0) {
      // almost certainly an @ used outside of EXCEPT, which is detected elsewhere
      return null;
    }

    prefix = children[0].heirs();

    // Allocate object to hold the Generized ID that is part of this OpAppl
    genID = new GenID(syntaxTreeNode);

    // Number of elements in the prefix
    int len = prefix.length;

    // Allocate array of SyntaxTreeNodes, one for each prefix element
    allArgs = new SyntaxTreeNode[ len ]; 

    // Process all of the prefix elements; construct the compound
    // identifier (with embedded !-characters), and also accumulate an
    // array of argument arrays (allArgs) for each prefix element
    for (int i = 0; i < len; i++ ) {
      // prefixElt becomes a 2- or 3-element array containing
      // [operator, args (optional), and "!"]
      prefixElt = prefix[i].heirs();    
        
      // Append the next part of compound identifier name and a "!"
      genID.append(prefixElt[0].getImage());
      genID.append("!");

      // allArgs[i] = array of arg syntax trees for next prefix
      // element (if any) or "!" (if not)
      allArgs[i] = prefixElt[1];          // Note: whether this is args or a "!" is checked below
    }

    // Append the primary (rightmost) operator name to compoundID;
    // calling "finalAppend" signals that the appending is finished,
    // i.e. that the string can be converted to a UniqueString and to
    // a SymbolNode inside the genID object
    genID.finalAppend(children[1].getImage(), unaryNegKludge);

    // for each argument in each potential argument list in the prefix, 
    // generate the expression or opArg corresponding to it

    // for each argument list in prefix
    int iarg = 0;
    for (int i = 0; i < allArgs.length ; i++ ) {
      // if there is an actual arg list here (instead of a "!" or null)
      if ( allArgs[i] != null && allArgs[i].isKind( N_OpArgs ) ) {
        // pick up array of arg list syntax elements
        argsList = allArgs[ i ].heirs();

        // The odd numbered syntax elements are the args expressions;
        // the even numbered ones are parens and commas.
        for (int ia = 1; ia < argsList.length; ia += 2) {
          // Each arg may be an ordinary expression, or it may be an OpArg; 
          //   produce appropriate semantic tree or node for it.
          // Note that operators can be used in place of expressions in only two contexts:
          //   as argument to suitable user-defined ops, and in the RHS of a substitution 
          //   in module instantiation
          genID.addArg(generateExprOrOpArg(genID.getFullyQualifiedOp(), syntaxTreeNode,
                                           iarg, argsList[ia], mn));
          iarg++;
        }
      }
    }

    // "finalize the GenID object (i.e. convert argument vector to array)
    genID.finalizeID();
    return genID;
  }

  /*************************************************************************
  * Added by LL on 27 March 2007.                                          *
  *                                                                        *
  * A lambda expression is represented as an OpDefNode.  Since it is       *
  * always used only as an operator argument, this OpDefNode will appear   *
  * in an OpArgNode.                                                       *
  *************************************************************************/
  private final OpDefNode generateLambda(TreeNode syntaxTreeNode, 
                                         ModuleNode cm)
  throws AbortException { 
    TreeNode []  children = syntaxTreeNode.heirs();
    int          arity    = (children.length - 2) / 2 ;
      /*********************************************************************
      * children = <<"LAMBDA", arg_1, ",", ...  , "," , arg_arity, ":",    *
      *               body>>                                               *
      * so   children.length = 3 + arity + arity-1                         *
      * so   arity = (children.length - 2) / 2.                            *
      *********************************************************************/
    Context      ctxt     = new Context(moduleTable, errors);
    symbolTable.pushContext( ctxt );
      /*********************************************************************
      * The context ctxt will hold the parameters of the lambda            *
      * expression, which may appear in its body.                          *
      *********************************************************************/
    FormalParamNode [] params   = new FormalParamNode[arity] ;
    int argPos = 1 ;
      /*********************************************************************
      * children[argPos] is the next parameter's identifier node.          *
      *********************************************************************/
    for (int i = 0 ; i < arity ; i++) {
      /*********************************************************************
      * Set params[i] to the FormalParamNode for the i-th formal           *
      * parameter.                                                         *
      *********************************************************************/
      params[i] = new FormalParamNode(children[argPos].getUS(),
                                      0,  // parameters of a lambda expression
                                          // have arity 0.
                                      children[argPos],
                                      symbolTable,
                                      cm) ;
      argPos = argPos + 2 ;
      } // for
    
//    /***********************************************************************
//    * Convert the FormalParamNode array params to the OpDeclNode array     *
//    * odn.                                                                 *
//    ***********************************************************************/
//    OpDeclNode[] odn = new OpDeclNode[params.length] ;
//    for (int i = 0; i < params.length; i++) {
//      odn[i] = new OpDeclNode(params[i].getName(),
//                              BoundSymbolKind,
//                              ConstantLevel,
//                              params.length,  // arity
//                              cm,             // ModuleNode                     
//                              null,           // SymbolTable
//                              params[i].stn); // TreeNode
//      }; // for
    pushFormalParams(params) ;
        /*******************************************************************
        * Push formal parameters on Last(LS).paramSeq for processing the   *
        * body
        *******************************************************************/
    ExprNode body = generateExpression( children[children.length - 1], cm );
      /*********************************************************************
      * Generate the lambda expression's body.                             *
      *********************************************************************/
    popFormalParams() ;

    symbolTable.popContext();
      /*********************************************************************
      * Restore original context.                                          *
      *********************************************************************/
    return new OpDefNode(
               S_lambda,          // The operator name is "LAMBDA"
               UserDefinedOpKind, // The node kind for a lambda expression
               params,            // the array of formal parameters
               false ,            // localness, which is meaningless
               body,              // the body (an expression node)
               cm,                // the module
               null,              // the symbol table, which is null for an
                                  // OpDefNode representing a lambda expression.
               syntaxTreeNode,
               true,              // Is defined.  Its value should not matter.
               null ) ;           // Source
  } // generateLambda

  /**
   * Generates an OpApplNode or an OpArgNode for a SyntaxTreeNode,
   * according to whether the value of "typeExpected" is either opAppl
   * or opArg.
   */
  private final ExprNode generateOpAppl(TreeNode syntaxTreeNode, ModuleNode cm)
  throws AbortException {
    TreeNode     primaryArgs = null;     
      // points to syntax tree of primary arg list (if any); otherwise null
    boolean      isOpApp     = syntaxTreeNode.isKind( N_OpApplication ) ;
      // true ==> to indicate this is an OpAppl; must have primary args
      // false ==> operator used as an argument (OpArg); has no primary args
    int          primaryArgCount = 0;    
      // total # of arguments, including those of prefix, if any
    int          len;                    
      // number of prefix elements
    TreeNode[]   children    = syntaxTreeNode.heirs(); 
      // temp used for finding the prefix
    TreeNode []  prefix;                 
      // array of prefix elements
    TreeNode[]   allArgs     = null;     
      // to collect arg arrays from both prefix and the main op (if any)
    TreeNode []  prefixElt;              
      // a prefixElement; 2 or 3 elem array: [op, (args), "!"]
    UniqueString symbol;                 
      // UniqueString name of the fully-qualified operator
    SymbolNode   fullOperator;           
      // The SymbolNode for the fully-qualified operator
    int          iarg        = 0;        
      // loop counter for actual args (as opposed to 
      //   arg syntax elements like commas and parens)
    TreeNode[]   argsList    = null;     
      // Will hold an array of arg syntax trees for primary operator
    ExprOrOpArgNode[] args   = null;     
      // Will hold an array of arg semantic trees for primary operator

    // Process the Generized ID that is the operator for this OpAppl
    GenID genID = generateGenID(children[0], cm);

    // Set up pointers to OpAppl's primary args
    primaryArgs = children[1];  
      // Array of argument list syntax elements for the main
      // (rightmost) operator, including parens and commas;
      //   should be an N_OpArgs node

    // calc number of primary args; 
    // args are interspersed w/ parens & commas--hence the /2
    primaryArgCount = primaryArgs.heirs().length / 2; 

    if (genID == null || genID.getFullyQualifiedOp() == null) {
      // if operator is @ or an unresolved symbol; error has already
      // been generated inside genID
      return nullOAN;
    }

    args = new ExprOrOpArgNode[primaryArgCount]; 
      // Array to hold semantic trees for primary args

    // pick up array of arg list syntax elements
    argsList = primaryArgs.heirs();

    // The odd numbered syntax elements are the args expressions; the
    // even numbered ones are parens and commas.
    // for each arg in this arg list ...
    for ( int ia = 1; ia < argsList.length; ia += 2 ) {
      // Each arg may be an ordinary expression, or it may be an OpArg; 
      //   produce appropriate semantic tree or node for it.
      // Note that operators can be used in place of expressions 
      // in only two contexts:
      //   as argument to suitable user-defined ops, and in the RHS 
      // of a substitution in module instantiation
      args[iarg] = generateExprOrOpArg(genID.getFullyQualifiedOp(), 
                                       syntaxTreeNode,
                                       iarg, argsList[ia], cm);
      iarg++;   // count the actual args
    } // end for

    // Concatenate the list of args in the GenID object to the 
    // primary arg list just created
    Vector            genIDArgList = genID.getArgsVector();
    ExprOrOpArgNode[] finalArgList = 
                        new ExprOrOpArgNode[genIDArgList.size() + iarg];

    // Copy the args from the prefix
    for (int i = 0; i < genIDArgList.size(); i++) {
      finalArgList[i] = (ExprOrOpArgNode)(genIDArgList.elementAt(i));
    }
    // Copy the primary args
    for (int i = 0, j = genIDArgList.size(); i < iarg; i++, j++ ) {
      finalArgList[j] = args[i];
    }

    // return an OpApplNode constructed from the fully-qualified
    // operator and the final arg list
    return new OpApplNode(genID.getFullyQualifiedOp(), finalArgList, 
                          syntaxTreeNode, cm);
  } // end generateOpAppl()

  /**
   * Process a named, parameterixed instantiation, e.g. of the form
   * D(p1,...pn) = INSTANCE M WITH a1 <- e1 ,..., ar <- er
   */
  /*************************************************************************
  * Note: the returned value does not seem to be used.                     *
  *************************************************************************/
  private final OpDefNode processModuleDefinition(
                  TreeNode treeNode,
                  Vector defs,  
                    /*******************************************************
                    * This is non-null when called from inside a LET, in   *
                    * which case the OpDef node is appended to defs.  If   *
                    * null, the OpDef node is appended to the              *
                    * module-level lists of such nodes.                    *
                    *******************************************************/
                  Vector insts,
                    /*******************************************************
                    * If non-null, then a vector of InstanceNode objects   *
                    * to which the current instance node is to be          *
                    * appended.  If null, cm.appendInstance is called to   *
                    * put the InstanceNode onto the module-level lists of  *
                    * such nodes.                                          *
                    *******************************************************/
                  ModuleNode cm)
  throws AbortException {
    // Start with a LHS for an instance: we must extract from it name
    // and possibly parameters. Then we need the external Context of
    // the module and to extract all non-local, non-builtin
    // symbols. Then build the proper symbol list and add it.
  
    // We must remember to identify explicitly whether or not the new
    // nodes would be local.
  
    // assert treeNode.isKind(N_ModuleDefinition)    
    // 
    // Note that this code does nothing about THEOREMS and ASSUMES in
    // modules being instantiated
    boolean      localness = treeNode.zero() != null;
    TreeNode[]   children  = treeNode.one()[0].heirs(); // heirs of IdentLHS
    UniqueString name      = children[0].getUS();

    // processing of LHS of the definition, i.e. the name and parameters
    FormalParamNode[] args = nullParam;
    Context parmCtxt = null;

    // If the operator being defined as a module instance has any parameters
    if (children.length > 1) {
      // Create new array of FormalParamNodes for the new operator
      args = new FormalParamNode[ children.length /2 -1 ];

      // Push a new context in current module's SymbolTable
      parmCtxt = new Context(moduleTable, errors);
      symbolTable.pushContext(parmCtxt);

      // For each formal parameter declared for the op being defined
      for (int i = 0; i < args.length; i++) {
        TreeNode     child = children[2 + 2 * i];
        UniqueString id    = null;
        int          count = 0;
  
        if ( child.isKind(N_IdentDecl)) {
          id = child.heirs()[0].getUS();
          count = (child.heirs().length -1)/ 2;
        }
        else if ( child.isKind(N_InfixDecl)) {
          id = child.heirs()[1].getUS();
          count = 2;
        }
        else if ( child.isKind(N_PrefixDecl)) {
          id = child.heirs()[0].getUS();
          count = 1;
        }
        else if ( child.isKind(N_PostfixDecl)) {
          id = child.heirs()[1].getUS();
          count = 1;
        }
        else {
          errors.addAbort(
            treeNode.getLocation(),
            "Internal error: Error in formal params part of parse tree.",
            true);
        }
 
        // If there was no error
        if ( id != null ) {
          // Create a new FormalParamNode for the defined Op and put 
          // it in the SymbolTable
          args[i] = new FormalParamNode(id, count, child, symbolTable, cm);
        } // end if
      } // end for
    } // end if

    // processing RHS of the definition, starting with identification
    // of module being instantiated, followed by processing of the
    // WITH clause (if any)
    children = treeNode.one()[2].heirs(); // heirs of NonLocalInstance

    // Find the Context and ModuleNode for the module being instantiated
    Context instanceeCtxt = this.getContext(children[1].getUS());
    ModuleNode instanceeModule = symbolTable.resolveModule(children[1].getUS());

    if (instanceeCtxt == null) {
      errors.addError(
        children[1].getLocation(),
        "Module " + children[1].getImage() + " does not have a context.");
      return nullODN;
    }

    if (instanceeModule == null) {
      errors.addError(children[1].getLocation(),
                      "Module name " + children[1].getImage() + 
                      " is not known" + " in current context.");
      return nullODN;
    }

    /*
     * Set isInstantiated field of instancee.  Added by LL 23 July 2013
     */
    instanceeModule.setInstantiated(true) ;


    // Create a SubstInNode that will be used to wrap each definition
    // body in the module being defined. "children" is the array of
    // explicit substitution clauses used in the module definition.
    // Both instanceeCtxt and symbolTable are involved here since for
    // each substitution c <- e, c must be resolved in the
    // instanceeCtxt, and e must be interpreted in symbolTable
    SubstInNode substIn = processSubst(treeNode, children, symbolTable,
                                       instanceeCtxt, instanceeModule, cm);

    // We are done with the local context (if one was created because
    // of parameters)
    if (parmCtxt != null) symbolTable.popContext();
  
    // Create a vector of all of the OpDefNodes in the instancee module
    /***********************************************************************
    * I have no idea why the module's getOpDefs method isn't used here.    *
    ***********************************************************************/
    Vector elts = instanceeCtxt.getByClass( OpDefNode.class );

    // For each definition in the instancee module, create a 
    // corresponding definition in the instancer module
    for (int i = 0; i < elts.size(); i++) {
      // Find the OpDefNode to be instantiated
      OpDefNode odn = (OpDefNode)elts.elementAt(i);

      /**********************************************************************
      * Ignore it if it is local or a builtin def.                          *
      **********************************************************************/
      if (    !odn.isLocal() 
           && (   (odn.getKind() == UserDefinedOpKind)
               || (odn.getKind() == ModuleInstanceKind) )) { 
        // Create the new name prepended with "name!"
        String compoundID = name + "!" + odn.getName();
        UniqueString qualifiedName = UniqueString.uniqueStringOf(compoundID);

        // Copy parameters for the op being defined
        FormalParamNode [] fpn    = odn.getParams();
        FormalParamNode [] params = new FormalParamNode[fpn.length + args.length];
        System.arraycopy(args, 0, params, 0, args.length);
        System.arraycopy(fpn, 0, params, args.length, fpn.length);

        OpDefNode newOdn ;
        if (odn.getKind() == UserDefinedOpKind) {
          if (substIn.getSubsts().length > 0) {
            // If there are substitutions, then the body of the new
            // definition instance must be wrapped in a SUBST-IN node.
            // Create the "wrapping" SubstInNode as a clone of "subst"
            // above, but with a body from the OpDefNode in the module
            // being instantiated
            SubstInNode substInNode = 
              new SubstInNode(treeNode, substIn.getSubsts(), odn.getBody(),
                              cm, instanceeModule);
  
            // Create the OpDefNode for the new instance of this
            // definition; because of the new operator name, cm is the
            // module of origin for purposes of deciding of two defs are
            // "the same" or "different"
            newOdn = new OpDefNode(qualifiedName, UserDefinedOpKind, params, 
                                   localness, substInNode, cm, symbolTable, 
                                   treeNode, true, odn.getSource());   
            setOpDefNodeRecursionFields(newOdn, cm) ;
            newOdn.setLabels(odn.getLabelsHT()) ;
           } // if (substIn.getSubsts().length > 0) 
          else {
            // no SUBST-IN node required; but because of the new
            // operator name, cm is the module of origin for purposes of
            // deciding of two defs are "the same" or "different"
            newOdn = new OpDefNode(qualifiedName, UserDefinedOpKind, params, 
                                   localness, odn.getBody(), cm, symbolTable, 
                                   treeNode, true, odn.getSource());   
            setOpDefNodeRecursionFields(newOdn, cm) ;
            newOdn.setLabels(odn.getLabelsHT()) ;
           } // else
         } // if (odn.kind == UserDefinedOpKind) 
        else {
          /*****************************************************************
          * This is a ModuleInstanceKind node.                             *
          *****************************************************************/
          newOdn = new OpDefNode(
                    qualifiedName, params, localness, 
                    odn.getOriginallyDefinedInModuleNode(), symbolTable, 
                    treeNode, odn.getSource());
        } ; // else
        // defs is non-null iff this module definition is in the Let
        // part of a Let-In expression.  Add this newly created OpDef
        // to either the LET list or the module cm's definition list.
        if (defs == null) {
          cm.appendDef(newOdn);
         }
        else {
          defs.addElement(newOdn);
         } 
      } // if (!odn.isLocal()&& ... )
    } // for

     /**********************************************************************
     * Import the ThmOrAssumpDefNode objects to the current module.  The   *
     * following code for doing this was copied and modified without       *
     * much thinking from the code above for OpDefNode objects             *
     **********************************************************************/
    // Create a vector of all of the ThmOrAssumpDefNodes in the 
    // instancee module
    Vector taelts = instanceeCtxt.getByClass( ThmOrAssumpDefNode.class );

    // For each definition in the instancee module, create a 
    // corresponding definition in the instancer module
    for (int i = 0; i < taelts.size(); i++) {
      // Find the ThmOrAssumpDefNode to be instantiated
      ThmOrAssumpDefNode taOdn = (ThmOrAssumpDefNode)taelts.elementAt(i);

      /*********************************************************************
      * There are no builtin ThmOrAssumpDefNode objects.                   *
      *********************************************************************/
      // Ignore it if it is local 
      if (!taOdn.isLocal()) { 
        // Create the new name prepended with "name!"
        String compoundID = name + "!" + taOdn.getName();
        UniqueString qualifiedName = UniqueString.uniqueStringOf(compoundID);

        // Copy parameters for the op being defined
        /*******************************************************************
        * Theorem or assumption definitions have no parameters.            *
        *******************************************************************/
        FormalParamNode [] fpn    = taOdn.getParams();
        FormalParamNode [] params = 
                            new FormalParamNode[fpn.length + args.length];
        System.arraycopy(args, 0, params, 0, args.length);
        System.arraycopy(fpn, 0, params, args.length, fpn.length);

        ThmOrAssumpDefNode newtaOdn;
        if (substIn.getSubsts().length > 0) {
          // If there are substitutions, then the body of the new
          // definition instance must be wrapped in a SUBST-IN node.
          // Create the "wrapping" SubstInNode as a clone of "subst"
          // above, but with a body from the ThmOrAssumpDefNode in the module
          // being instantiated
          APSubstInNode substInNode = 
            new APSubstInNode(treeNode, substIn.getSubsts(), taOdn.getBody(),
                              cm, instanceeModule);

          // Create the ThmOrAssumpDefNode for the new instance of this
          // definition; because of the new operator name, cm is the
          // module of origin for purposes of deciding of two defs are
          // "the same" or "different"
          newtaOdn = new ThmOrAssumpDefNode(qualifiedName, taOdn.isTheorem(),
                                substInNode, cm, symbolTable, 
                                 treeNode, params, instanceeModule,
                                 taOdn.getSource());   
          // Following statement added by LL on 30 Oct 2012 to handle locally 
          // instantiated theorems and assumptions. Added setLabels call
          // on 31 Oct 2012.
          newtaOdn.setLocal(localness);
          newtaOdn.setLabels(taOdn.getLabelsHT()) ;
          
          /*****************************************************************
          * No recursion fields needed for a theorem or assumption         *
          * because it can't appear in a recursive section.                *
          *****************************************************************/
          // setThmOrAssumpDefNodeRecursionFields(newtaOdn, cm) ;
        }
        else {
          // no SUBST-IN node required; but because of the new
          // operator name, cm is the module of origin for purposes of
          // deciding if two defs are "the same" or "different"
          newtaOdn = new ThmOrAssumpDefNode(qualifiedName, taOdn.isTheorem(),
                                 taOdn.getBody(), cm, symbolTable, 
                                 treeNode, params, instanceeModule,
                                 taOdn.getSource());
          // Following statement added by LL on 30 Oct 2012 to handle locally 
          // instantiated theorems and assumptions.   Added setLabels call
          // on 31 Oct 2012.       
          newtaOdn.setLocal(localness);
          newtaOdn.setLabels(taOdn.getLabelsHT()) ;
          /*****************************************************************
          * No recursion fields needed for theorems or assumptions         *
          * because they can't appear in a recursive section.              *
          *****************************************************************/
          // setThmOrAssumpDefNodeRecursionFields(newtaOdn, cm) ;
        }
  
        // defs is non-null iff this module definition is in the Let
        // part of a Let-In expression.  Add this newly created ThmOrAssumpDef
        // to either the LET list or the module cm's definition list.
        if (defs == null) {
          cm.appendDef(newtaOdn);
        }
        else {
          defs.addElement(newtaOdn);
        }
      } // if (!taOdn.isLocal()&& ... )
    } // for

    // Create a new InstanceNode to represent this INSTANCE stmt 
    // in the current module
    InstanceNode inst = new InstanceNode(name, localness, args, 
                                         instanceeModule,
                                         substIn.getSubsts(), treeNode);

    // Append this new InstanceNode to the vector of InstanceNodes
    // being accumulated for this module
    if (insts == null) {
      cm.appendInstance(inst);
    }
    else {
      insts.addElement(inst);
    }

    // Create new OpDefNode with ModuleInstanceKind.  The reason for
    // doing this is to get the name in the symbol table so the name
    // cannot be re-used later in this module for a user-defined
    // operator.
    return new OpDefNode(name, args, localness, cm, symbolTable, treeNode, 
                         null);
      /*********************************************************************
      * Note: the module's OpDefNode does not have recursive parameters    *
      * set.  If the module definition statement occurs in a recursive     *
      * section, then it is the instantiated definitions that are          *
      * recursive, not the module definition itself.  (The name under      *
      * which the module is instantiated cannot appear in a RECURSIVE      *
      * statement.)                                                        *
      *********************************************************************/
      
  } // end processModuleDefinition()
  
  /**
   * From a particular explicit substitution (substTarget <- substValue)
   * check the legality of the substTarget, and if OK, generate the
   * appropriate type of node for substValue
   */
  private ExprOrOpArgNode generateSubst(
              Context instanceeCtxt, 
              TreeNode substTarget,
              TreeNode substValue, 
              ModuleNode mn) 
  throws AbortException {
    SymbolNode targetSymbol = instanceeCtxt.getSymbol(substTarget.getUS());

    // if the targetSymbol cannot be found in the instancee context, 
    // or if it does not correspond to a declaration, then it is an 
    // illegal substitution target

    if (targetSymbol == null || ! (targetSymbol instanceof OpDeclNode) ) {
      errors.addError(
        substTarget.getLocation(),
        "Identifier '" + substTarget.getUS() + "' is not a legal" +
        " target of a substitution. \nA legal target must be a declared" +
        " CONSTANT or VARIABLE in the module being instantiated." +
        " \n(Also, check for warnings about multiple declarations of" +
        " this same identifier.)");
      return nullOAN;
    }
    
    // but if the symbol is found, then if it has arity 0, the RHS 
    // should be an expression, if arity > 0, the the RHS should be an OpArg
    ExprOrOpArgNode returnObject;

    if ( targetSymbol.getArity() == 0 ) {
      // if the target of the substitution has arity 0,
      // then we expect an expression to be substituted for it
      returnObject = generateExpression(substValue, mn);
    }
    else { 
      // if the target of the substitution has arity > 0,
      // then and operator must be substituted for it
      returnObject = generateOpArg(targetSymbol, substValue, mn);

      // and it better have the same arity as the target
      if ( ((OpArgNode)returnObject).getArity() != targetSymbol.getArity() ) {
        errors.addError(substValue.getLocation(),
                        "An operator must be substituted for symbol '" +
                        targetSymbol.getName() + "', and it must have arity " +
                        targetSymbol.getArity() + ".");
      }
    }
    return returnObject;
  } // end generateSubst()

  /**
   * Return an OpArgNode constructed from a GeneralId tree to be used
   * in the RHS of a substitution
   */
  private OpArgNode generateOpArg(SymbolNode targetSymbol, 
                                  TreeNode opArgSyntaxNode,
                                  ModuleNode mn) 
  throws AbortException {
    /***********************************************************************
    * If this is a lambda expressiion, then just get it and go.            *
    ***********************************************************************/
    if (opArgSyntaxNode.isKind(N_Lambda)) {
      return new OpArgNode(generateLambda(opArgSyntaxNode, mn), 
                           opArgSyntaxNode, mn) ;
      } ;
    // First, make sure that an operator ID is present, and not an expression
    if ( ! ( opArgSyntaxNode.isKind(N_GeneralId)           ||
             opArgSyntaxNode.isKind(N_GenInfixOp)          ||
             opArgSyntaxNode.isKind(N_GenPrefixOp)         ||
             opArgSyntaxNode.isKind(N_GenNonExpPrefixOp)   ||
               /************************************************************
               * This last disjunct was added by LL on 9 May 2007.         *
               *                                                           *
               * The original parser phase produced an N_GenPrefixOp       *
               * here, but an N_GenNonExpPrefixOp for the syntactically    *
               * identical situation in an operator argument.  The new     *
               * TLA+2 parser produces N_GenNonExpPrefixOp nodes here,     *
               * but I left the N_GenPrefixOp case in here just in case    *
               * this is called somewhere else that I haven't found.       *
               ************************************************************/
               
             opArgSyntaxNode.isKind(N_GenPostfixOp) 
           )
       ) {
      errors.addError(opArgSyntaxNode.getLocation(), 
                      "Arity " + targetSymbol.getArity() + 
                      " operator (not an expression) is expected" + 
                      " \nto substitute for CONSTANT '" + 
                      targetSymbol.getName() + "'." );
      return nullOpArg;
    }

    /***********************************************************************
    * If the argument is a GeneralId node, then we use                     *
    * genIdToSelector and selectorToNode to generate the OpArg node.       *
    ***********************************************************************/
    if (opArgSyntaxNode.getKind() == N_GeneralId) {
      /*********************************************************************
      * First, a sanity check to make sure we're never looking for an      *
      * expression argument.                                               *
      *********************************************************************/
      if (targetSymbol.getArity() <= 0) {
        errors.addAbort(opArgSyntaxNode.getLocation(),
                       "Internal error: expected to find arity > 0.", true);
        } ;

         LevelNode ln = selectorToNode(genIdToSelector(
                            (SyntaxTreeNode) opArgSyntaxNode), 
                            targetSymbol.getArity(), false, false, mn);

        /*******************************************************************
        * Added 23 February 2009: It appears that, in case of an error,    *
        * selectorToNode can return something other than an OpArgNode      *
        * here.  (In particular, an OpApplNode.)  Rather than tix          *
        * selectorToNode, I am adding a kludge to simply ignore the        *
        * problem and hope that it can be caused only by some other        *
        * error.  If no error has been found, then we abort and debug if   *
        * this is encountered.                                             *
        *******************************************************************/
         if (!(ln instanceof OpArgNode)) { 
           if (errors.getNumErrors() > 0) { return nullOpArg; }
           errors.addAbort(opArgSyntaxNode.getLocation(),
                           "Internal error: " +
                           "Expected an operator argument but " +
                           "found something else.");
           };
         return (OpArgNode) ln ;
    } ;
       
    /*******************************************************************
    * If the argument is not a GeneralId node, we use the code from    *
    * SANY1 to generate the OpArg node.                                *
    *******************************************************************/
  
    // Assemble the (possibly compound) generalized identifier, and resolve it.
    GenID genID = generateGenID(opArgSyntaxNode, mn);

    // If the fully-qualified op is undefined, then a message has already been
    // put in errors, but we must insert a nullOpArgNode in the tree.
    if (genID.getFullyQualifiedOp() != null && genID.getArgs().length == 0 ) {
      // Create an OpArgNode from it.
      return new OpArgNode(genID.getFullyQualifiedOp(), opArgSyntaxNode, mn);
    }
    else if ( genID.getArgs().length > 0 ) { 
      // Expression being used where Operator is required
      errors.addError(opArgSyntaxNode.getLocation(), 
                      "Arity " + targetSymbol.getArity() + 
                      " operator (not an expression) is expected" + 
                      " to substitute for CONSTANT '" + 
                      targetSymbol.getName() + "'." );
      return nullOpArg;      
    }
    else {
      return nullOpArg;
    }
  } // end generateOpArg()

  /**
   * Process the substitutions clause of a module definition or instantiation;
   * returns a SubstInNode that can be used as a template for the wrapper that
   * must be present around each OpDefNode body created from the module
   * instantiation or module definition.
   */
  private SubstInNode processSubst(
            TreeNode    treeNode,
            TreeNode[]  substNodes, 
               // array of subst nodes [c1 <- e1, ... ,cn <- en]
            SymbolTable instancerST,    
               // SymbolTable in which the ei must be resolved
            Context     instanceeCtxt,  
               // Context in which the ci must be resolved
            ModuleNode  instanceeModule,
               // the ModuleNode of the module in which ci must be resolved
            ModuleNode  mn) throws AbortException {
    TreeNode[] children;    // find the substitution part of the syntax tree

    // Create a vector of all declarations of CONSTANTS and VARIABLES 
    // in the context of the module being instantiated (instancee).
    // These are all the symbols that must have substitutions defined
    // for them in the instantiation, either explictly or implicitly.
    Vector decls = instanceeCtxt.getByClass( OpDeclNode.class );

    // Create a SubstInNode to be used as a template for the SubstInNodes 
    // in the body of every newly instantiated OpDef in the module.  
    // The substitutions in the returned SubstInNode object will be the 
    // implicit substitutions of the form c<-c for all CONSTANTS and 
    // VARIABLES c that are BOTH declared in instancee and for which the 
    // same name is declared or defined in instancer.  Note the instancerST 
    // must be passed to this constructor because with a default substitution 
    // LHS<-RHS the LHS is resolved in the instanceeCtxt, (done
    // in the previous line) and the RHS is resolved in the instancerST.
    SubstInNode substIn = 
         new SubstInNode(treeNode, instancerST, decls, mn, instanceeModule);

    // For each explicit substitution in the syntax tree, overwrite or add
    // the corresponding default entry in SubstInNode just created
    for (int i = 3; i < substNodes.length; i += 2) {
      // pick up array of syntax elements for one substitution, 
      // e.g. ["c","<-",expr]
      TreeNode sc[] = substNodes[i].heirs(); 

      // substRHS is the expression "exp" in "c <- exp"; this stmt first 
      // checks that c is properly declared in the instancee context, 
      // and then generates an ExprOrOpArgNode.  If c is a constant 
      // with parameters, then an OpArgNode is returned; otherwise it is 
      // an ExprNode. 
      ExprOrOpArgNode substRHS = 
                        generateSubst(instanceeCtxt, sc[0], sc[2], mn);

      // Overwrite an implicit substitution if there is one, or add a new one, 
      // checking for duplicate substitutions for the same symbol
      substIn.addExplicitSubstitute(instanceeCtxt, sc[0].getUS(), 
                                    sc[2], substRHS );
    }

    // Check if substitution is complete, i.e. that all constants and vars 
    // have been substituted for.  
    substIn.matchAll( decls );  
    return substIn;
  } // end processSubst

  /**
   * This method treats *unnamed* INSTANCE stmts
   * NOTE: this code does nothing with ASSUMES or THEOREMS
   */
  /*************************************************************************
  * However, SANY2 imports ThmOrAssumpDef nodes.                           *
  *************************************************************************/
  /**
 * @param treeNode
 * @param cm
 * @param topLevel
 * @return
 * @throws AbortException
 */
/**
 * @param treeNode
 * @param cm
 * @param topLevel
 * @return
 * @throws AbortException
 */
/**
 * @param treeNode
 * @param cm
 * @param topLevel
 * @return
 * @throws AbortException
 */
/**
 * @param treeNode
 * @param cm
 * @param topLevel
 * @return
 * @throws AbortException
 */
private final InstanceNode 
   generateInstance(TreeNode treeNode, ModuleNode cm, boolean topLevel)
   throws AbortException {
     /**********************************************************************
     * topLevel argument is true for a top-level INSTANCE statement, and   *
     * false elsewise--that is, for an INSTANCE inside a proof.            *
     **********************************************************************/
     TreeNode[] children ;
     if (topLevel) {
       children = treeNode.one()[0].heirs(); }
                        // skip one generation below NonLocalInstance
                        // because we know zero defines local in a 
                        // top-level INSTANCE
     else {children = treeNode.heirs();} ;
     // id of module being instanced
     UniqueString moduleId = children[1].getUS();  
                        
     // If this module instance is declared "LOCAL" then all of the 
     // definitions in it must be instanced as if they were "LOCAL"
     boolean localness = treeNode.local();

     // Create a list of all declarations for module moduleId.
     // Match them against either something in the substitutions or 
     // something in the current context (symbol table) for the 
     // substitution.  Check that the symbol does occur in the module 
     // and as a declaration.
     Context instanceeCtxt = this.getContext(moduleId);
     if (instanceeCtxt == null) {
       errors.addAbort(children[1].getLocation(),
                       "Internal error: No context available for module `" +
                       moduleId.toString() + "'.", true);
      } ;
     // Try to find the ModuleNode for the module being instanced in
     // the symbolTable
     ModuleNode instanceeModuleNode = symbolTable.resolveModule(moduleId);

     // It must be an external module if it isn't in the symbolTable;
     // try to find it in moduleTable (it cannot be in both places, or
     // a name conflict would have resulted)
     if (instanceeModuleNode == null) { 
       instanceeModuleNode = moduleTable.getModuleNode(moduleId);
     }

     if (instanceeModuleNode == null) {
        errors.addAbort(children[1].getLocation(), 
                        "Could not find module " + moduleId.toString(),
                        false);
     }
    
     /*
      * Set isInstantiated field of instancee.  Added by LL 23 July 2013
      */
     instanceeModuleNode.setInstantiated(true) ;
     
     // Create the SubstInNode that will act as a template "wrapper"
     // for each definition in the module being instantiated; this
     // SubstInNode itself gets discarded after being used as template
     // however many times is necessary
     SubstInNode subst = processSubst(treeNode, children, symbolTable,
                                      instanceeCtxt, instanceeModuleNode, cm);

     // Create a vector of all of the OpDefNodes in the module being 
     // instantiated
     Vector defs = instanceeCtxt.getByClass(OpDefNode.class);

     OpDefNode odn;       // OpDefNode in module being instantiated (instancee)
     OpDefNode newOdn;    // Its counterpart current module (instancer)
     SubstInNode substInTemplate;  // Template to be used for any 
                                   // SubstInNode wrappers required
     
     // Duplicate the OpDef records from the module being INSTANCE'd 
     for (int i = 0; i < defs.size(); i++) {
       odn = (OpDefNode)defs.elementAt(i); 
          // OpDefNode in module being instantiated (instancee)

       // Do not instantiate built-in or local operators, or those 
       // OpDefNodes created solely to prevent a ModuleName from being 
       // used as an operator node.
       if (odn.getKind() == BuiltInKind ||
           odn.getKind() == ModuleInstanceKind ||
           odn.isLocal()) {
         continue;
       }

       // If there are parameters to the module being instantiated, then 
       // a SubstInNode is required, and possibly a different module of 
       // origin should be indicated
       if (!instanceeModuleNode.isParameterFree()) {
         // Create the OpDefNode for the new instance of this definition
         // Note that the new OpDefNode shares the array of FormalParamNodes 
         //   with the old OpDefNode, as well as large parts of its body 
         // (all but the SubstInNode). Hence, changes by a tool to an Original 
         // OpDefNode will likely be reflected in all instances of it.
         if ( odn.getOriginallyDefinedInModuleNode().isParameterFree() ) {  

           /****************************************************************
           * Originally, newOdn was set the way it now is if localness =   *
           * true.  Here's the problem with it.  Suppose the instantiated  *
           * module EXTENDS the Naturals module.  Then this will add new   *
           * OpDefNodes for all the symbols defined in Naturals.  If the   *
           * current module EXTENDS Naturals, this will lead to multiple   *
           * definitions.  So, for nonlocal definitions, we just           *
           * set newOdn to odn.                                            *
           *                                                               *
           * However, now the problem is: suppose the current module       *
           * does not EXTEND the Naturals module.  Then the operators      *
           * defined in Naturals, which should be defined in the current   *
           * module, are not.  So, we add them to symbolTable.  This does  *
           * not lead to a multiple definition error because apparently    *
           * it's the addSymbol method that is smart enough to detect if   *
           * we are adding a definition that comes from the same source as *
           * the original one.                                             *
           *                                                               *
           * This fix was made by LL on 16 Feb 2009.                       *
           *                                                               *
           * On 6 June 2010, LL add "&& topLevel" to the following `if'    *
           * test.  This was needed because an INSTANCE inside a proof     *
           * was producing a "Multiple declarations or definition"         *
           * warning if the INSTANCEd module and the current module both   *
           * EXTENDed Naturals.  This fix seems to do the right thing,     *
           * but I have not extensively tested it and I have no idea what  *
           * problems may remain.                                          *
           ****************************************************************/
           if (localness  && topLevel ) {
             newOdn = new OpDefNode( odn.getName(), UserDefinedOpKind, odn.getParams(),
                            localness, odn.getBody(), 
                            odn.getOriginallyDefinedInModuleNode(), 
                            symbolTable, treeNode, true, odn.getSource() );   
             /***************************************************************
             * The following statement was added by LL on 16 Feb 2009, by  *
             * analogy with the corresponding code about 45 lines below.  I *
             * have no idea if it was originally omitted for a good reason. *
             ***************************************************************/
             newOdn.setLabels(odn.getLabelsHT()) ;   
            }
           else {
             newOdn = odn;
             symbolTable.addSymbol(odn.getName(), odn);
           }
         }
         else {        
           // Create the "wrapping" SubstInNode as a clone of "subst" above, 
           // but with a body from the OpDefNode in the module being 
           // instantiated
           substInTemplate = new SubstInNode(treeNode, subst.getSubsts(),
                                             odn.getBody(), cm, 
                                             instanceeModuleNode);
           newOdn = new OpDefNode(odn.getName(), UserDefinedOpKind, 
                                  odn.getParams(),  localness, 
                                  substInTemplate, cm, symbolTable, treeNode, 
                                  true, odn.getSource());   
                newOdn.setLabels(odn.getLabelsHT()) ;    


         }
       }
       else { 
         // There are no parameters to the instancee module; this
         // means that a SubstInNode is not necessary, and also that
         // the new operator should be considered to be "originally
         // defined in" the same module as the old one for purposes of
         // telling whether they are "the same" or different definitions

         // Create an OpDefNode whose body is the same as the instancer's.

         if (localness) {
           /****************************************************************
           * See the comments about the similar change made to the         *
           * setting of newOdn in the `then' clause, just above.           *
           * This entire change was made by LL on 16 Feb 2009.             *
           ****************************************************************/
           newOdn = new OpDefNode(odn.getName(), UserDefinedOpKind, odn.getParams(),  
                         localness, odn.getBody(), 
                         odn.getOriginallyDefinedInModuleNode(), 
                         symbolTable, treeNode, true, odn.getSource()); 
                   newOdn.setLabels(odn.getLabelsHT()) ;   
          }
         else {
           newOdn = odn;
           symbolTable.addSymbol(odn.getName(), odn);
          }
       }
       cm.appendDef(newOdn);
       setOpDefNodeRecursionFields(newOdn, cm) ;
     } // end for

     /**********************************************************************
     * Import the ThmOrAssumpDefNode objects to the current module.  The   *
     * following code for doing this was copied and modified without       *
     * thinking from the code above for OpDefNode objects                  *
     **********************************************************************/
     Vector tadefs = instanceeCtxt.getByClass(ThmOrAssumpDefNode.class);

     ThmOrAssumpDefNode tadn;       
        // ThmOrAssumpDefNode in module being instantiated (instancee)
     ThmOrAssumpDefNode newTadn;    
       // Its counterpart current module (instancer)
     APSubstInNode tasubstInTemplate;  // Template to be used for any 
                                   // SubstInNode wrappers required
     
     // Duplicate the OpDef records from the module being INSTANCE'd 
     for (int i = 0; i < tadefs.size(); i++) {
       tadn = (ThmOrAssumpDefNode)tadefs.elementAt(i); 
          // ThmOrAssumpDefNode in module being instantiated (instancee)

       // Following statement added by LL on 30 Oct 2012 to handle locally 
       // instantiated theorems and assumptions.          
       if (tadn.isLocal()) {
           continue ;
       }

       // If there are parameters to the module being instantiated, then 
       // a SubstInNode is required, and possibly a different module of 
       // origin should be indicated
       if (!instanceeModuleNode.isParameterFree()) {
         // Create the ThmOrAssumpDefNode for the new instance of this 
         // definition. Note that the new ThmOrAssumpDefNode shares the 
         // array of FormalParamNodes with the old ThmOrAssumpDefNode, 
         // as well as large parts of its body (all but the SubstInNode). 
         // Hence, changes by a tool to an Original ThmOrAssumpDefNode will 
         // likely be reflected in all instances of it.
         if ( tadn.getOriginallyDefinedInModuleNode().isParameterFree() ) { 
           // Following if/else added by LL on 30 Oct 2012 to handle locally
           // instantiated theorems and assumptions.
           if (localness  && topLevel ) {
               newTadn = new ThmOrAssumpDefNode(tadn.getName(), tadn.isTheorem(), 
                                           tadn.getBody(), cm, symbolTable, treeNode,
                                           tadn.getParams(), instanceeModuleNode, 
                                           tadn.getSource()) ;
               newTadn.setLocal(true);
           }
           else {
              newTadn = tadn;
              // On 30 Oct 2012, LL noticed that code was added on 16 Feb 2009
              // to the corresponding place in the code for an OpDefNode, but that
              // nothing was added here.  I suspect that something should have been
              // that the 2009 code should also have been added here, but wasn't--
              // perhaps because there's no getLabelsHT method for a ThmOrAssumpDefNode.
              // This may mean that there's a bug in handling labels in the
              // instantiated theorem or assumption.
           }
           /*
             new ThmOrAssumpDefNode( tadn.getName(), UserDefinedOpKind, 
                            tadn.getParams(),
                            localness, tasubstInTemplate, 
                            tadn.getOriginallyDefinedInModuleNode(), 
                            symbolTable, treeNode, true );   
           */
         }
         else {        
           // Create the "wrapping" SubstInNode as a clone of "subst" above, 
           // but with a body from the ThmOrAssumpDefNode in the module being 
           // instantiated
           tasubstInTemplate = new APSubstInNode(treeNode, subst.getSubsts(),
                                                 tadn.getBody() , cm, 
                                                 instanceeModuleNode);
           newTadn = new ThmOrAssumpDefNode(tadn.getName(), tadn.isTheorem(),
                                  tasubstInTemplate, cm, symbolTable, 
                                  treeNode, tadn.getParams(), 
                                  instanceeModuleNode, tadn.getSource());
           // Following if/else added by LL on 30 Oct 2012 to handle locally
           // instantiated theorems and assumptions.
           newTadn.setLocal(localness) ;
           // cm.appendDef(newTadn);
           newTadn.setLabels(tadn.getLabelsHT()) ;
           
         }
       }
       else { 
         // There are no parameters to the instancee module; this
         // means that a SubstInNode is not necessary, and also that
         // the new operator should be considered to be "originally
         // defined in" the same module as the old one for purposes of
         // telling whether they are "the same" or different definitions

         // Create a ThmOrAssumpDefNode whose body is the same as 
         // the instancer's.
         if (localness && topLevel) {
           newTadn = 
              new ThmOrAssumpDefNode(tadn.getName(), tadn.isTheorem(),
                            tadn.getBody(), 
                            tadn.getOriginallyDefinedInModuleNode(), 
                            symbolTable, treeNode, tadn.getParams(),
                            instanceeModuleNode, tadn.getSource()); 
            // Following if/else added by LL on 30 Oct 2012 to handle locally
            // instantiated theorems and assumptions.
            newTadn.setLocal(localness) ;
            newTadn.setLabels(tadn.getLabelsHT()) ;
         }
         else {
         newTadn = tadn;
         symbolTable.addSymbol(tadn.getName(), tadn);
         }
        }
       if (topLevel) {cm.appendDef(newTadn);} ;
       /********************************************************************
       * No recursion fields needed for theorems or assumptions because    *
       * they can't appear in a recursive section.                         *
       ********************************************************************/
       // setOpDefNodeRecursionFields(newTadn, cm) ;
     } // end for

     // Create a new InstanceNode to represent this INSTANCE stmt in 
     // the current module
     InstanceNode inst = 
         new InstanceNode(null /*no name*/, localness, null /*no parms*/, 
                          instanceeModuleNode, subst.getSubsts(), treeNode);

     // Append this new InstanceNode to the vector of InstanceNodes
     // being accumulated for this module
     if (topLevel){ cm.appendInstance(inst); } ;
     return inst;

  } // void generateInstance


  private final void processTheorem(TreeNode stn, ModuleNode cm) 
   throws AbortException {
    ThmOrAssumpDefNode tadn = null ;
    LevelNode body ;  
    ProofNode proof = null ;
    int bodyIndex = stn.heirs().length - 1 ;
    boolean isAssumeProve = false ;
      /*********************************************************************
      * Set true if the body is an ASSUME/PROVE.                           *
      *********************************************************************/
    boolean hasProof =    
                  (stn.heirs()[bodyIndex].getKind() == N_Proof)
               || (stn.heirs()[bodyIndex].getKind() == N_TerminalProof) ;
    if (hasProof) {bodyIndex--;} ;

    if (bodyIndex > 1) {
      /*********************************************************************
      * If this is a named theorem, start fresh processing of labels,      *
      * create the object.                                                 *
      *********************************************************************/
      pushLS();
      UniqueString name = stn.heirs()[1].getUS() ;
      tadn = new ThmOrAssumpDefNode(name, stn) ;
     } ;
    if (stn.zero()[bodyIndex].isKind(N_AssumeProve))
      { /*******************************************************************
        * Theorem statement is an ASSUME/PROVE.  Must set currentGoal.     *
        *******************************************************************/
        currentGoal = tadn ;
        isAssumeProve = true ;

        /*******************************************************************
        * We want the symbols declared in top-level NEW statements of the  *
        * ASSUME clause to be visible in the proof.  Therefore, we do the  *
        * context push for the top-level AssumeProveNode here instead of   *
        * in generateAssumeProve.                                          *
        *******************************************************************/
        symbolTable.pushContext(new Context(moduleTable, errors)) ;
        body = generateAssumeProve(stn.heirs()[bodyIndex], cm);
        currentGoal = null ;
      } 
    else { /****************************************************************
           * Theorem statement must be an ExprNode.                        *
           ****************************************************************/
           body = generateExpression(stn.heirs()[bodyIndex], cm);
      } ;
   if (bodyIndex > 1) {
     /**********************************************************************
     * The theorem node has the form                                       *
     *      THEOREM Ident == statement                                     *
     **********************************************************************/
     Context assumeContext = null;
     if (isAssumeProve) {
       /********************************************************************
       * If the body is an ASSUME/PROVE, we must save in assumeContext     *
       * the context containing the symbols declared in the ASSUME         *
       * clause and pop it, so Ident is made visible outside the proof.    *
       ********************************************************************/
       assumeContext = symbolTable.getContext() ;
       symbolTable.popContext() ;
      } ;
     UniqueString name = stn.heirs()[1].getUS() ;
     tadn.construct(true, body, cm, symbolTable, null) ;
     tadn.setLabels(popLabelNodeSet()) ;
     cm.appendDef(tadn) ;
     if (isAssumeProve) {
       /********************************************************************
       * After putting Ident into the symbol table, we push the ASSUME     *
       * context back onto symboltable.                                    *
       ********************************************************************/
        symbolTable.pushContext(assumeContext) ;
      };
     } ; // if (bodyIndex > 1)

   /************************************************************************
   * Note: If this is a named theorem, then the name has been added to     *
   * symbolTable so it can be referred to within the theorem's proof (if   *
   * it has one).                                                          *
   ************************************************************************/
   if (hasProof) {proof = generateProof(stn.heirs()[bodyIndex+1], cm);} ;

   if (isAssumeProve) { 
     symbolTable.popContext(); 
       /********************************************************************
       * Pop the context containing ASSUME declarations.                   *
       ********************************************************************/
     ((AssumeProveNode) body).inProof = false ;
       /********************************************************************
       * Reset the AssumeProve node's inProof field.                       *
       ********************************************************************/
    } ;
   cm.addTheorem(stn, body, proof, tadn) ;   
  } // ProcessTheorem

  private final void processAssumption(TreeNode stn, ModuleNode cm) 
  throws AbortException {
    ThmOrAssumpDefNode tadn = null ;
    int lastIndex = stn.heirs().length - 1 ;
    if (lastIndex > 1) {pushLS();} ;
      /*********************************************************************
      * If this is a named assumption, start fresh processing of labels.   *
      *********************************************************************/
    ExprNode expr = generateExpression(stn.heirs()[lastIndex], cm);

    if (lastIndex > 1) {
      /**********************************************************************
      * The assumption node has the form                                    *
      *      ASSUME Ident == expression                                     *
      **********************************************************************/
      UniqueString name = stn.heirs()[1].getUS() ;
      tadn = new ThmOrAssumpDefNode(name, false, expr, cm, symbolTable, stn,
                                    null, null, null) ;
      tadn.setLabels(popLabelNodeSet()) ;
      cm.appendDef(tadn) ;
     } ;
    cm.addAssumption(stn, expr, symbolTable, tadn);
    return;
  } // processAssumption


  private final ProofNode generateProof(TreeNode stn, ModuleNode cm) 
    /***********************************************************************
    * Node stn is of kind N_TerminalProof or an N_Proof.  The heirs of an  *
    * N_Proof node consist of an optional PROOF token followed by a        *
    * seequence of N_ProofStep nodes.  The heirs of an N_ProofStep node    *
    * are a StartStep() token, a statement body, and an optional proof.    *
    * A statement body is one of the following node kinds:                 *
    *                                                                      *
    *   Have no proof:                                                     *
    *     N_DefStep   N_UseOrHide   N_NonLocalInstance   N_HaveStep,       *
    *     N_TakeStep  N_WitnessStep                                        *
    *                                                                      *
    *   Have a proof                                                       *
    *     N_QEDStep  N_PickStep   N_CaseStep   N_AssertStep                *
    *                                                                      *
    * Each step produces the following kind of semantic node:              *
    *                                                                      *
    *     N_DefStep   : DefStepNode                                        *
    *                                                                      *
    *     N_UseOrHide : UseOrNideNode                                      *
    *                                                                      *
    *     N_NonLocalInstance : InstanceNode                                *
    *                                                                      *
    *     Others: TheoremNode                                              *
    *       The type of statement is indicated by the body of the          *
    *       node.  For any step other than an N_AssertStep, the body       *
    *       is an OpApplNode with the following dummy operator:            *
    *                                                                      *
    *          N_HaveStep     : $Have                                      *
    *          N_CaseStep     : $Pfcase                                    *
    *          N_TakeStep     : $Take                                      *
    *          N_PickStep     : $Pick                                      *
    *          N_WitnessStep  : $Witness                                   *
    *          N_QEDStep      : $Qed                                       *
    ***********************************************************************/
  throws AbortException {
    int numberOfPops = 0;
      /*********************************************************************
      * For each SUFFICES ASSUME/PROVE step, we push a new context onto    *
      * the symbol table containing declarations of any NEW symbols.       *
      * These need to be popped off when through processing the proof.     *
      *********************************************************************/
    if (stn.getKind() == N_TerminalProof) {
       return generateLeafProof(stn, cm) ;} ;

    Context pfCtxt = new Context(moduleTable, errors) ;
    symbolTable.pushContext(pfCtxt);
      /*********************************************************************
      * Create a new sub-Context for the proof.                            *
      *********************************************************************/

    TreeNode heirs[] = stn.heirs() ;
    int offset = 0 ;
    if (heirs[0].getKind() == TLAplusParserConstants.PROOF) { offset = 1 ; } ;
    LevelNode[] steps = new LevelNode[heirs.length - offset] ;
    Vector iVec = new Vector() ;
      /*********************************************************************
      * A vector to hold the InstanceNodes generated by steps of the form  *
      * Id == INSTANCE ...  so they can be level checked.                  *
      *********************************************************************/

    /***********************************************************************
    * At the beginning of each loop iteration, the variable prevIsInFix    *
    * equals true iff the previous step consists of a formula whose main   *
    * operator is an infix operator, including an "@-step" of the form "@  *
    * infix-op expression".  If it is true, then rhSide is the ExprNode    *
    * of the infix-op's right-hand-side expression.                        *
    ***********************************************************************/
    boolean prevIsInfix = false ;
    ExprNode prevRHS = null ;

    for (int i = offset ; i < heirs.length; i++) {
      /*********************************************************************
      * Process proof step i.                                              *
      *********************************************************************/
      boolean isAssumeProve = false ;
        /*******************************************************************
        * Will be set true for an ASSUME/PROVE, so we can reset the        *
        * node's inProof field.                                            *
        *******************************************************************/
      boolean isSuffices = false ;
        /*******************************************************************
        * Will be set to true for a SUFFICES statement.  This is used to   *
        * do the right thing with ASSUME declarations in an ASSUME/PROVE   *
        * step, and to set the suffices field of the ThmOrAssumpDefNode    *
        * if this is a named step.                                         *
        *******************************************************************/
        
      /*********************************************************************
      * For an ASSUME/PROVE, we set assumeContext to a context containing  *
      * the declarations from the outer-most NEWs of the ASSUME. For an    *
      * ordinary ASSUME/PROVE, this context is pushed onto the symbol      *
      * table for statement's processing the proof.  For a SUFFICE         *
      * ASSUME/PROVE, it is pushed onto the symbol table after processing  *
      * the statement's proof so the outermost NEW declarations are        *
      * visible for the rest of the current proof.                         *
      * The handling of the assumeContext was changed on 1 Jul 2009        *
      * because SUFFICE ASSUME/PROVE was not being handled properly.       *
      *********************************************************************/
      Context assumeContext = null;

      /*********************************************************************
      * For "PICK x : exp", the symbol x is declared in exp, undeclared    *
      * in the proof of the step, and declared afterwards.  (There'd be a  *
      * similar problem with TAKE if it took a proof.)  The following      *
      * variables are used to manipulate this, with pickContext holding    *
      * the declarations of the symbols introduced by the PICK step.       *
      *********************************************************************/
      boolean isPick = false;
      Context pickContext = null;

      /*********************************************************************
      * Set stepNumSTN, stepBodySTN, and stepPfSTN to the syntax tree      *
      * nodes of the step number, the body, and the proof (the latter      *
      * equal to null if there's no proof.                                 *
      *********************************************************************/
      TreeNode pfStepSTN   = heirs[i] ;
      TreeNode stepNumSTN  = pfStepSTN.heirs()[0] ;
      TreeNode stepBodySTN = pfStepSTN.heirs()[1] ;
      TreeNode stepPfSTN   = null ;
      if (pfStepSTN.heirs().length > 2) {stepPfSTN = pfStepSTN.heirs()[2];};

      LevelNode pfNumNode = null ;
      boolean makePfNumNode = true ;
        /*******************************************************************
        * For a numbered step that doesn't produce a TheoremNode,          *
        * pfNumNode is set to a node that will be the stepNode of a        *
        * NumberedProofStepKind OpDefNode.                                 *
        *******************************************************************/
      /*
       * On 23 Feb 2014 LL added the following code to make step numbers
       * like <*>13 illegal, so <+> and <*> can be used only for unnamed
       * steps.  It would be most natural to make the change age the
       * parsing level by changing the JavaCC code.  However, that code
       * is a Kludge that it is best not to touch unless absolutely necessary.
       * Also, detecting the error here allows multiple instances of the
       * error to be reported in a single execution of the parser.
       * 
       * The modification is based on the following empirical observation:
       * 
       *   - For a step number like "<3>13."
       *       stepNumSTN.image = stepNumSTN.originalImage = "<3>13."
       *   - For a step number like "<*>13.",
       *       stepNumSTN.image = "<3>13." and stepNumSTN.originalImage = "<*>13."
       *   - For unnumbered steps,
       *       stepNumSTN.originalImage = null  and    stepNumSTN.image = the actual token.
       */
      SyntaxTreeNode STN = (SyntaxTreeNode) stepNumSTN ;
      if (    (STN.originalImage != null)
           && (STN.originalImage != STN.image) 
           ) {
          String oimage = STN.originalImage.toString() ;
          if   (    (! oimage.equals(STN.image.toString()))
                 && ( (oimage.charAt(1) == '*') || (oimage.charAt(1) == '+') )
               ) {
              errors.addError(stepNumSTN.getLocation(),
                      "<*> and <+> cannot be used for a named step.");
          }          
      }

      /*********************************************************************
      * Set stepNum to the step number, or null if its an unnumbered step. *
      *********************************************************************/
      UniqueString stepNum = null ;
      switch (stepNumSTN.getKind()) {
      // LL: On 25 Feb 2010 I discovered the following comment here:
      //      XXXXXX  xyz: need to add the following case
      // The ProofImplicitStepLexeme case (something like <*>3) seems to be 
      // handled properly in tests.  I presume that this is an obsolete
      // comment that I didn't remove when I added the case to the code. 
        case TLAplusParserConstants.ProofImplicitStepLexeme :
        case TLAplusParserConstants.ProofStepLexeme :
          stepNum = stepNumSTN.getUS() ; 
          break ;
        case TLAplusParserConstants.ProofStepDotLexeme :
          String stNum = stepNumSTN.getUS().toString() ;
          stepNum = UniqueString.uniqueStringOf(
                      stNum.substring(0, stNum.indexOf("."))) ;
          break ;
        default : 
          makePfNumNode = false ;
          break ;
      } ; // switch

      /*********************************************************************
      * If this is a numbered step, process labels.                        *
      *********************************************************************/
      if (stepNum != null) {
        pushLS();
        } ;

       /********************************************************************
       * Construct the ThmOrOpDefNode if needed.  (We need to do it now    *
       * because we have to set currentGoal before we generate the body.)  *
       ********************************************************************/
       ThmOrAssumpDefNode tadn = null ;
       if (stepNum != null) { 
         tadn = new ThmOrAssumpDefNode(stepNum, stepNumSTN) ;
        } ;
      
      /*********************************************************************
      * Set prevIsInfix false unless this is an AssertStep node.           *
      *********************************************************************/
      int stepKind = stepBodySTN.getKind();
      if (stepKind != N_AssertStep) {prevIsInfix = false ;} ;

      switch (stepKind) {
        case N_DefStep :
          /*****************************************************************
          * Set defSTNs to the array of heirs, and defOffSet so that       *
          * defSTNs[defOffSet] ...  defSTNs[defSTNs.length-1] is the       *
          * sequence of definitions.                                       *
          *****************************************************************/
          TreeNode[] defSTNs = stepBodySTN.heirs();
          int defOffSet = 0 ;
          if (defSTNs[0].getKind() == DEFINE) {defOffSet = 1;};

          OpDefNode[] defs = new OpDefNode[defSTNs.length - defOffSet] ;
            /***************************************************************
            * Will be set to the sequence of OpDefNodes for the            *
            * definitions.                                                 *
            ***************************************************************/
          for (int j = defOffSet; j < defSTNs.length ; j++) {
            TreeNode defSTN = defSTNs[j]; ;
            Vector vec = new Vector() ;
            switch (defSTN.getKind()) {
              /***************************************************************
              * Need to check if it's an operator, function, or module       *
              * definition.                                                  *
              ***************************************************************/
              case N_FunctionDefinition :
                processFunction(defSTN, vec, cm) ;
                break ;
              case N_ModuleDefinition :
                /*************************************************************
                * The call to processModuleDefinition sets defsVec to a      *
                * vector of all the definitions it makes, and adds the new   *
                * InstanceNode to iVec.  For now, we're just throwing        *
                * away defsVec.  (If defsVec were null, then                 *
                * processModuleDefinition would add these definitions to to  *
                * the module's list of top-level definitions.)               *
                *************************************************************/
                Vector defsVec = new Vector() ;
                vec.addElement(
                   processModuleDefinition(defSTN, defsVec, iVec, cm)) ;
                break ;
              case N_OperatorDefinition :
                processOperator(defSTN, vec, cm) ;
                /*************************************************************
                * processOperator creates an OpDefNode, puts an entry for    *
                * it in symbolTable, and adds the OpDefNode to vec.          *
                *************************************************************/
                break ;
             }; // switch (def.getKind())
            defs[j - defOffSet] = (OpDefNode) vec.elementAt(0);
           }; // for j 
          pfNumNode = new DefStepNode(stepBodySTN, stepNum, defs) ;
          steps[i - offset] = pfNumNode ;
          break ;

        case N_UseOrHide :
          UseOrHideNode uohn = generateUseOrHide(stepBodySTN, cm) ;

          // Added by LL on 16 Jun 2010 so location returnedby getLocation() will
          // include the step number.
          uohn.stn = pfStepSTN; 

          uohn.setStepName(stepNum);  // Added 6 June 2010 by LL.
          
          if (uohn.facts.length + uohn.defs.length == 0) {
            errors.addError(stepBodySTN.getLocation(),
                            "Empty USE or HIDE statement.");
           };
           uohn.factCheck();
             // Added 4 Mar 2009.
           pfNumNode = uohn ;
          steps[i - offset] = pfNumNode ;
          break ;

        case N_NonLocalInstance :
          // Code to set step name added by LL on 6 June 2010
          InstanceNode inst = generateInstance(stepBodySTN, cm, false);
          inst.setStepName(stepNum);
          pfNumNode = inst;
          steps[i - offset] = pfNumNode ;
          break ;

        default :
          makePfNumNode = false ;
          TreeNode[] bodyHeirs = stepBodySTN.heirs() ;
          LevelNode body = null ;
            /***************************************************************
            * This will be set to the body of the TheoremNode or           *
            * ThmOrAssumpDefNode.                                          *
            ***************************************************************/
          UniqueString op = null ;
          ExprNode[] args ;
            /***************************************************************
            * For anything but an N_Assert node, body is set to an         *
            * OpApplNode having these as its operator and arguments.       *
            ***************************************************************/

          switch (stepBodySTN.getKind()) {
           case N_AssertStep :
             int bodyNext = 0 ;
             if (bodyHeirs[0].getKind() == 
                    TLAplusParserConstants.SUFFICES) {
               bodyNext = 1 ;
               isSuffices = true ;
               /************************************************************
               * We can't have an "@" in a SUFFICES step.                  *
               ************************************************************/
              } ;
             if (bodyHeirs[bodyNext].getKind() == N_AssumeProve) {
               /************************************************************
               * This is an AssumeProve node.                              *
               ************************************************************/
               isAssumeProve = true ;

               /************************************************************
               * For an ASSUME/PROVE, we need save the symbol              *
               * declarations from top-level NEW statements in the ASSUME  *
               * to make them visible only in the statement's proof for    *
               * an ordinary ASSUME/PROVE, and only after the statement's  *
               * proof for a SUFFICES ASSUME/PROVE.                        *
               ************************************************************/
               symbolTable.pushContext(new Context(moduleTable, errors)) ;

               currentGoal = tadn ;
                 /**********************************************************
                 * Need to set currentGoal before generating the           *
                 * AssumeProve node.                                       *
                 **********************************************************/
               body = generateAssumeProve(bodyHeirs[bodyNext], cm);

               if (isSuffices) { ((AssumeProveNode) body).setSuffices(); };
                 /**********************************************************
                 * Added 16 Feb 2009 by LL.                                *
                 **********************************************************/
               currentGoal = null ;
               assumeContext = symbolTable.getContext() ;
               symbolTable.popContext() ;
               prevIsInfix = false ;
               }
             else {  
               /************************************************************
               * This is an ordinary expression.                           *
               ************************************************************/
               TreeNode curExpr = bodyHeirs[bodyNext] ;

               /************************************************************
               * Special handling of SUFFICES added by LL 16 Feb 2009.     *
               ************************************************************/
               if (isSuffices) {  
                 args = new ExprNode[1] ;
                 args[0] = generateExpression(curExpr, cm) ;
                 body = new OpApplNode(OP_suffices, args, stepBodySTN, cm) ;
                } // if (isSuffices) 
               else {  
                 /************************************************************
                 * If the current expression is an infix expression, set     *
                 * curLHS to its current LHS, otherwise set it to null.      *
                 ************************************************************/
                 SyntaxTreeNode curLHS  = null ;
                 if (curExpr.getKind() == N_InfixExpr) {
                   curLHS = (SyntaxTreeNode) curExpr.heirs()[0] ;
                  } ;
                 /************************************************************
                 * If prevIsInfix is true and curLHS is an "@", then         *
                 * process it, using as the right-hand side a new $Nop node  *
                 * with prevRHS as its argument.                             *
                 ************************************************************/
                 if (   prevIsInfix
                     && (curLHS != null)
                     && (curLHS.heirs().length > 0)
                        /***************************************************
                        * This test added 25 Feb 2010 because if curLHS    *
                        * is a string, then curLHS.heirs() is a            *
                        * zero-length array, so the following test threw   *
                        * an out-of-bounds array index exception.  Note    *
                        * that curLHS.heirs() should never be null,        *
                        * because the heirs() method can never return      *
                        * null.                                            *
                        ***************************************************/
                     && (((SyntaxTreeNode) 
                             curLHS.heirs()[0]).heirs().length == 0) 
                     && (curLHS.heirs()).length > 1
                        /***************************************************
                        * This test added 2 Mar 2009 to fix following      *
                        * bug.  When we are here and the left-hand side    *
                        * is something like a number, then curLHS.heirs()  *
                        * seems to have length 1 and the following test    *
                        * causes an ArrayIndexOverflowException.           *
                        ***************************************************/
                     && (curLHS.heirs()[1].getKind() == IDENTIFIER)
                     && (curLHS.heirs()[1].getUS() == AtUS)) {
  
                   /**********************************************************
                   * The following code obtained by a simple modification    *
                   * of the N_InfixExpr case of generateExpression.          *
                   **********************************************************/
                   TreeNode[] children = curExpr.heirs() ;
                   GenID genID = generateGenID(children[1], cm);
                   ExprNode[]sns = new ExprNode[2];
                   SymbolNode opn = 
                      symbolTable.resolveSymbol(
                        Operators.resolveSynonym(genID.getCompoundIDUS()));
                   if ( opn == null ) {
                      errors.addError(curExpr.getLocation(),
                          "Couldn't resolve infix operator symbol `" + 
                          genID.getCompoundIDUS() + "'." );
                      return null;
                    } ;
                   sns[1] = generateExpression( children[2], cm );
                   /**********************************************************
                   * Set sns[1] to a new $Nop OpApplNode whose argument is   *
                   * prevRHS.                                                *
                   **********************************************************/
                   ExprNode[] nopArgs = new ExprNode[1] ;
                   nopArgs[0] = prevRHS ;
                   sns[0] = new OpApplNode(OP_nop, nopArgs,  curLHS, cm) ;
                   body = new OpApplNode(opn, sns, curExpr, cm);
                  }  // if ( prevIsInfix ...)
                 else { // this is not an @-step
                   body = generateExpression(curExpr, cm) ;
                  } ;
                 
                 /************************************************************
                 * If this is an infix ioperator, set prevIsInfix true and   *
                 * prevRHS equal to its right-hand argument, else set        *
                 * prevIsInfix false.                                        *
                 ************************************************************/
                 prevIsInfix = false ;
                 if  (   (curLHS != null)
                      /*******************************************************
                      * The following conjuncts should be true unless there  *
                      * was an error in the expression.                      *
                      *******************************************************/
                      && (body != null)    
                      && (body.getKind() == OpApplKind)
                      && ( ((OpApplNode) body).getArgs().length > 1)) {
                   prevIsInfix = true ;
                   prevRHS = (ExprNode) ((OpApplNode) body).getArgs()[1] ;
                  }
                }
              }; // else This is an ordinary expression.
             break ;
 
           case N_HaveStep :
           case N_CaseStep :
             if (stepBodySTN.getKind() == N_HaveStep) {op = OP_have ;}
             else {op = OP_pfcase ;} ;
             args = new ExprNode[1] ;
             args[0] = generateExpression(bodyHeirs[1], cm) ;
             body = new OpApplNode(op, args, stepBodySTN, cm) ;
             break ;

           case N_TakeStep :
           case N_PickStep :
             if (stepBodySTN.getKind() == N_TakeStep) {op = OP_take ;}
             else {
               op = OP_pick ;
               isPick = true;
               /************************************************************
               * Push a new context onto the symbolTable stack to get the  *
               * declarations of the PICK symbols.                         *
               ************************************************************/
               symbolTable.pushContext(new Context(moduleTable, errors)) ;
              } ;

             if (bodyHeirs[1].getKind() == N_QuantBound) {
               /************************************************************
               * The introduced identifiers are bounded--e.g., "TAKE id    *
               * \in Set".                                                 *
               ************************************************************/
               
               /************************************************************
               * Set quants to the number of N_QuantBound nodes.           *
               ************************************************************/
               int quants = 1 ;
               int nextTok = 2;
               while (   (nextTok < bodyHeirs.length) 
                      && (bodyHeirs[nextTok].getKind() 
                             == TLAplusParserConstants.COMMA)) {
                 quants++ ;
                 nextTok = nextTok + 2 ;
                };
               FormalParamNode[][] params = new FormalParamNode[quants][0];
               boolean[]           bt = new boolean[quants] ;
               ExprNode[]          paramBounds = new ExprNode[quants];
               processQuantBoundArgs(
                   bodyHeirs, 1, params, bt, paramBounds, cm) ;

               if (isPick) {
                 /**********************************************************
                 * Save the declarations in pickContext.                   *
                 **********************************************************/
                 pickContext = symbolTable.getContext() ;
                 /**********************************************************
                 * This is a PICK step; get the ": expr".                  *
                 **********************************************************/
                 nextTok++ ; // Skip over the ":"
                 args = new ExprNode[1] ;
                 pushFormalParams(flattenParams(params)) ;
                   /********************************************************
                   * Push the bound variables on Last(LS).paramSeq and     *
                   * process the body of the PICK.                         *
                   ********************************************************/
                 args[0] = generateExpression(bodyHeirs[nextTok], cm) ;
                 popFormalParams() ;
                 symbolTable.popContext() ;
                   /********************************************************
                   * Remove the bound symbols from the symbol table so     *
                   * they're undefined for the proof of the PICK.          *
                   ********************************************************/
                }  
               else {
                 /**********************************************************
                 * This is a TAKE step.                                    *
                 **********************************************************/
                 args = new ExprNode[0] ;
                };
               body = new OpApplNode(op, null, args, params, 
                                     bt, paramBounds, stepBodySTN, cm) ;
              }
             else {
               /************************************************************
               * The introduced identifiers are unbounded--e.g., "TAKE     *
               * id1, id2".                                                *
               ************************************************************/
               
               /************************************************************
               * Set ids to the number of introduced identifiers.          *
               ************************************************************/
               int ids = 1 ;
               while (   (2*ids < bodyHeirs.length) 
                      && (bodyHeirs[2*ids].getKind() == 
                            TLAplusParserConstants.COMMA)) {ids++;} ;
     
               /************************************************************
               * Set params to the array of new FormalParamNodes for the   *
               * identifiers.  The identifiers are added to the current    *
               * symbol table.                                             *
               ************************************************************/
               FormalParamNode[]   params = new FormalParamNode[ids];
               for (int j = 0 ; j < ids ; j++) {
                  params[j] = new FormalParamNode(
                                    bodyHeirs[2*j + 1].getUS(), 0, 
                                    bodyHeirs[2*j + 1], symbolTable, cm);
                 } ;
     
               if (isPick) {
                 /**********************************************************
                 * Save the declarations in pickContext.                   *
                 **********************************************************/
                  pickContext = symbolTable.getContext() ;
 
                 /**********************************************************
                 * This is a PICK step; get the ": expr".                  *
                 **********************************************************/
                 pushFormalParams(params) ;
                   /********************************************************
                   * Push formal parameters on Last(LS).paramSeq for       *
                   * processing the body.                                  *
                   ********************************************************/
                 args = new ExprNode[1] ;
                 args[0] = generateExpression(bodyHeirs[2*ids + 1], cm) ;
                 popFormalParams() ;
                 symbolTable.popContext() ;
                   /********************************************************
                   * Remove the bound symbols from the symbol table so     *
                   * they're undefined for the proof of the PICK.          *
                   ********************************************************/
               }
               else {
                 /**********************************************************
                 * This is a TAKE step.                                    *
                 **********************************************************/
                 args = new ExprNode[0] ;
                };
               body = new OpApplNode(op, args, params, stepBodySTN, cm) ;
              } ;

             break ;

           case N_WitnessStep :
             /**************************************************************
             * Set ids to the number of expressions.                       *
             **************************************************************/
             int ids = 1 ;
             while (   (2 * ids < bodyHeirs.length) 
                    && (bodyHeirs[2 * ids].getKind() == 
                          TLAplusParserConstants.COMMA)) {ids++;} ;

             args = new ExprNode[ids] ;
             for (int j = 0 ; j < ids ; j++) {
               args[j] = generateExpression(bodyHeirs[2*j + 1], cm);
                 } ;
             body = new OpApplNode(OP_witness, args, stepBodySTN, cm) ;
             break ;

           case N_QEDStep :
             args = new ExprNode[0] ;
             body = new OpApplNode(OP_qed, args, stepBodySTN, cm) ;
             break ;

           default :
             errors.addAbort(
                stn.getLocation(),
                "Internal error: Unexpected SyntaxTreeNode kind: " 
                  + heirs[i].getKind()) ;
             break ;
        }; // switch


       /********************************************************************
       * Set the fields of the ThmOrOpDefNode if there is one, including   *
       * the suffices field.                                               *
       ********************************************************************/
       if (stepNum != null) { 
         tadn.construct(true, body, cm, symbolTable, null) ;
         tadn.setLabels(popLabelNodeSet()) ;
         if (isSuffices) { tadn.setSuffices() ;} ;
        } ;
       /***********************************************************************
       * Set proof to the proof, or to null if there is none.  There is no    *
       * check made to see if this is a kind of step that should have a       *
       * proof.  Thus, adding a proof to something like a WITNESS statement   *
       * requires changing only the parsing phase (specified by tla+.jj).     *
       ***********************************************************************/
       ProofNode proof = null ;
       if (stepPfSTN != null) { 
         /******************************************************************
         * For an ordinary ASSUME/PROVE, must make the ASSUME's            *
         * declarations visible in the statement's proof.                  *
         ******************************************************************/
         if (isAssumeProve && !isSuffices) {
           symbolTable.pushContext(assumeContext) ;
          } ;
         proof = generateProof(stepPfSTN, cm); 
         if (isAssumeProve && !isSuffices) {symbolTable.popContext(); } ;
        } ;

       /********************************************************************
       * For a SUFFICES ASSUME/PROVE, must make the ASSUME's declarations  *
       * visible after the proof.  This is done by pushing assumeContext   *
       * onto the symbol table and incrementing numberOfPops so it will    *
       * be popped at the end of the proof.                                *
       ********************************************************************/
       if (isAssumeProve && isSuffices) {
           numberOfPops++ ;
           symbolTable.pushContext(assumeContext) ; } ;
       if (isAssumeProve) { ((AssumeProveNode) body).inProof = false ; } ;
         /******************************************************************
         * For an ASSUME/PROVE, set the inProof field to false.            *
         ******************************************************************/
       TheoremNode thm = new TheoremNode(stepBodySTN, body, cm, proof, tadn);
       
       // Added by LL on 16 Jun 2010 so location returnedby getLocation() will
       // include the step number.
       thm.stn = pfStepSTN; 

       thm.suffices = isSuffices ;
       steps[i - offset] = thm; 
       }; // switch
      if (makePfNumNode) {
        /*******************************************************************
        * Make an OpDefNode for the numbered step and add any label        *
        * declarations to it.                                              *
        *******************************************************************/
        OpDefNode nodeMadeOnlyToBePutInSymbolTable =
           new OpDefNode(stepNum, pfNumNode, cm, symbolTable, pfStepSTN) ;
        nodeMadeOnlyToBePutInSymbolTable.setLabels(popLabelNodeSet()) ;
       }
      if (isPick) {
        /*******************************************************************
        * We have to take the symbol declarations from pickContext and     *
        * put them into the current symbol table.                          *
        *******************************************************************/
        Enumeration e = pickContext.content() ;
        while (e.hasMoreElements()) {
          SymbolNode sym = ((Context.Pair)(e.nextElement())).getSymbol();
          symbolTable.addSymbol(sym.getName(), sym) ;
         }
       }
     } ; // for i
    InstanceNode[] insts = new InstanceNode[iVec.size()] ;
    for (int i = 0 ; i < insts.length; i++) {
      insts[i] = (InstanceNode) iVec.elementAt(i) ; 
     }; 

    /***********************************************************************
    * Pop the contexts that were pushed onto the symbol table for SUFFICE  *
    * ASSUME/PROVE steps.                                                  *
    ***********************************************************************/
    for (int i = 0; i < numberOfPops; i++) {
      // Added by LL on 24 June 2010
      // Need to add the symbols in the context being popped to pfCtxt
      // so they will be put into the context of the NonLeafProofNode.
      Context topContext = symbolTable.getContext();
      Enumeration e = topContext.content() ;
      while (e.hasMoreElements()) {
        SymbolNode sym = ((Context.Pair)(e.nextElement())).getSymbol();
        pfCtxt.addSymbolToContext(sym.getName(), sym) ;
       }
      symbolTable.popContext(); 
     };
    symbolTable.popContext();
    return new NonLeafProofNode(stn, steps, insts, pfCtxt);
      /*********************************************************************
      * Pop the sub-Context.                                               *
      *********************************************************************/
   } // generateProof

/***************************************************************************
* The following method is not used and I have no idea why it's still       *
* here.                                                                    *
***************************************************************************/
  private final LevelNode generateNumerableStep(
          TreeNode stn,
//          TreeNode stmt, 
//          UniqueString stepNum,
//          TreeNode proof, 
          ModuleNode cm) 
    throws AbortException {
    /***********************************************************************
    * Used to generate the step for a NumerableStep or QEDStep token.      *
    * Returns a TheoremNode or ThmOrAssumpDefNode.                         *
    *                                                                      *
    * The parsing into the syntactic tree makes it hard to rationalize     *
    * processing of an N_NumerableStep node because there are two          *
    * different ways such a step can be parsed                             *
    *                                                                      *
    *  1. [step number] (sequence of tokens of the statement) [proof]      *
    *  2. [step number] (NonExprBody) [proof]                              *
    *                                                                      *
    * where, in case 2, the NonExprBody node contains all the tokens of    *
    * the statement except the optional step number.  Here are the         *
    * classes into which the different kinds of NumerableStep nodes fall.  *
    *                                                                      *
    * 1. CASE, (step number) expression.                                   *
    *                                                                      *
    * 2. WITNESS, TAKE, PICK, HAVE, ASSUME/PROVE,  SUFFICES,               *
    *    and PROVE expression                                              *
    ***********************************************************************/
errors.addAbort(stn.getLocation(), "Uses generateNumerable_Step") ;
    UniqueString stepNum = null ;
    TreeNode[] heirs = stn.heirs() ;
    int nextTok = 0 ;
    ThmOrAssumpDefNode tadn = null ;
    boolean isSuffices = false ;
    boolean isAssumeProve = false ;
      /*********************************************************************
      * Set true if this is an ASSUME/PROVE step, in which case some       *
      * messing with the symbol table is necessary so that symbols         *
      * declared in the ASSUME are visible in the proof of this step.      *
      * They should be visible in the rest of the proof iff this is a      *
      * SUFFICES ASSUME...  step.                                          *
      *********************************************************************/
    Context assumeContext = null;
      /*********************************************************************
      * For use with an ASSUME/PROVE.                                      *
      *********************************************************************/
    LevelNode body = null ;
      /*********************************************************************
      * This will be set to the body of the TheoremNode or                 *
      * ThmOrAssumpDefNode.                                                *
      *********************************************************************/
      
    /***********************************************************************
    * We now save the values of heirs and nextTok.  If the tokens of the   *
    * statement are inside a NonExprBody node, we set heirs to the         *
    * children of that node, nextTok to 0, and hasNonExprBody true.        *
    * After processing the statement, we will reset heirs and set nextTok  *
    * to the its saved value plus 1.                                       *
    ***********************************************************************/
    TreeNode[] savedHeirs = heirs ;
    int        savedNextTok = nextTok ;
    boolean    hasNonExprBody = false ;
    if (heirs[nextTok].getKind() == N_NonExprBody) {
      heirs = heirs[nextTok].heirs() ;
      nextTok = 0 ;
      hasNonExprBody = true ;
     } ;

    /***********************************************************************
    * If next token is "SUFFICES", then skip over it and set isSuffices    *
    * true.  With the current grammar, this is the case only for an        *
    * ordinary assertion (a statement or ASSUME/PROVE).                    *
    ***********************************************************************/
    if (heirs[nextTok].getKind() == TLAplusParserConstants.SUFFICES) {
      nextTok++ ;
      isSuffices = true ;
     } ;
    
    /***********************************************************************
    * Skip over the next token if it's "PROVE".  With current grammar,     *
    * this only happens when nextTok = 0.                                  *
    ***********************************************************************/
    if (heirs[nextTok].getKind() == TLAplusParserConstants.PROVE) {
      nextTok++ ;
     } ;

    /***********************************************************************
    * If body will be an OpApplNode with a dummy operator (like $Pick),    *
    * then set op to the operator's name and move past the determining     *
    * token (like "PICK").  Otherwise, the body will be an ordinary        *
    * assertion and op is left null.                                       *
    ***********************************************************************/
    UniqueString op = null ;
    switch (heirs[nextTok].getKind()) {
      case TLAplusParserConstants.QED :
        body = new OpApplNode(OP_qed, new ExprNode[0], heirs[nextTok], cm) ;
        nextTok++ ;
        break ;

      case TLAplusParserConstants.CASE :
      case TLAplusParserConstants.HAVE :
        op = OP_have ;
        if (heirs[nextTok].getKind() == TLAplusParserConstants.CASE) {
          op = OP_pfcase ;
         };
        nextTok++ ;
        ExprNode[] args = new ExprNode[1] ;
        args[0] = generateExpression(heirs[nextTok], cm) ;
        body = new OpApplNode(op, args, heirs[nextTok], cm) ;
        nextTok++ ;
        break ;

      case TLAplusParserConstants.TAKE :
      case TLAplusParserConstants.PICK :
        op = OP_take ;
        if (heirs[nextTok].getKind() == TLAplusParserConstants.PICK) {
          op = OP_pick ;
         };
        nextTok++ ;
          
        if (heirs[nextTok].getKind() == N_QuantBound) {
          int offset = nextTok;
          /*****************************************************************
          * The introduced identifiers are bounded--e.g.,                  *
          * "TAKE id \in Set".                                             *
          *****************************************************************/
          /*****************************************************************
          * Set quants to the number of N_QuantBound nodes.                *
          *****************************************************************/
          int quants = 1 ;
          nextTok++ ;
          while (   (nextTok < heirs.length) 
                 && (heirs[nextTok].getKind() 
                        == TLAplusParserConstants.COMMA)) {
            quants++ ;
            nextTok = nextTok + 2 ;
           };
          FormalParamNode[][] params = new FormalParamNode[quants][0];
          boolean[]           bt = new boolean[quants] ;
          ExprNode[]          paramBounds = new ExprNode[quants];
          processQuantBoundArgs(heirs, offset, params, bt, paramBounds, cm) ;

//          ExprNode[]          args ;
          if (op == OP_pick) {
           /****************************************************************
           * This is a PICK step; get the ": expr".                        *
           ****************************************************************/
           nextTok++ ; // Skip over the ":"
           args = new ExprNode[1] ;
           args[0] = generateExpression(heirs[nextTok], cm) ;
           nextTok++ ;
           }
          else {
           /****************************************************************
           * This is a TAKE step.                                          *
           ****************************************************************/
           args = new ExprNode[0] ;
           };
          body = 
           new OpApplNode(op, null, args, params, bt, paramBounds, stn, cm) ;
         }
        else {
          /*****************************************************************
          * The introduced identifiers are unbounded--e.g.,                *
          * "TAKE id1, id2".                                               *
          *****************************************************************/
          /*****************************************************************
          * Set ids to the number of introduced identifiers.               *
          *****************************************************************/
          int ids = 1 ;
          while (   (nextTok + 2*ids - 1 < heirs.length) 
                 && (heirs[nextTok + 2*ids - 1].getKind() == 
                       TLAplusParserConstants.COMMA)) {ids++;} ;

          /*****************************************************************
          * Set params to the array of new FormalParamNodes for the        *
          * identifiers.  The identifiers are added to the current symbol  *
          * table.                                                         *
          *****************************************************************/
          FormalParamNode[]   params = new FormalParamNode[ids];
          for (int i = 0 ; i < ids ; i++) {
             params[i] = new FormalParamNode(
                               heirs[2*i + nextTok].getUS(), 0, 
                               heirs[2*i + nextTok], symbolTable, cm);
            } ;
          /*****************************************************************
          * Skip over the identifier-list tokens.                          *
          *****************************************************************/
          nextTok = nextTok + 2*ids - 1;

//          ExprNode[] args ;
          if (op == OP_pick) {
           /****************************************************************
           * This is a PICK step; get the ": expr".                        *
           ****************************************************************/
           nextTok++ ; // Skip over the ":"
           args = new ExprNode[1] ;
           args[0] = generateExpression(heirs[nextTok], cm) ;
           nextTok++ ;
           }
          else {
           /****************************************************************
           * This is a TAKE step.                                          *
           ****************************************************************/
           args = new ExprNode[0] ;
           };
          body = 
           new OpApplNode(op, args, params, stn, cm) ;
         } ;
        break ;

      case TLAplusParserConstants.WITNESS :
        nextTok++ ;

        /*******************************************************************
        * Set ids to the number of expressions.                            *
        *******************************************************************/
        int ids = 1 ;
        while (   (nextTok + 2*ids - 1 < heirs.length) 
               && (heirs[nextTok + 2*ids - 1].getKind() == 
                     TLAplusParserConstants.COMMA)) {ids++;} ;
        ExprNode[] exprs = new ExprNode[ids] ;
        for (int i = 0 ; i < ids ; i++) {
          exprs[i] = generateExpression(heirs[2*i + nextTok], cm);
            } ;

        body = new OpApplNode(OP_tup, exprs, stn, cm) ;
        nextTok = nextTok + 2*ids - 1;
        break ;

      default:
        /*******************************************************************
        * This is an ordinary assertion--either an ExprNode or an          *
        * AssumeProve node.                                                *
        *******************************************************************/
        if (heirs[nextTok].getKind() == N_AssumeProve) {
          /*****************************************************************
          * This is an AssumeProve node.                                   *
          *                                                                *
          * For an ordinary ASSUME/PROVE, we need to save symbol           *
          * declarations from top-level NEW statements in the ASSUME to    *
          * make them visible only in the proof.  If this is a SUFFICES    *
          * ASSUME/PROVE, we don't need to do that because we want those   *
          * symbol declarations to be visible outside the PROVE clause as  *
          * well.                                                          *
          *****************************************************************/
          isAssumeProve = true ;
          if (!isSuffices) {
            symbolTable.pushContext(new Context(moduleTable, errors)) ;
// System.out.println("here") ;
           } ;
// System.out.println("here and there") ;
          body = generateAssumeProve(heirs[nextTok], cm);
          if (!isSuffices) {
            assumeContext = symbolTable.getContext() ;
            symbolTable.popContext() ;
           } ;
         }
        else {
          /*****************************************************************
          * This is an ordinary expression.                                *
          *****************************************************************/
          body = generateExpression(heirs[nextTok], cm) ;
         };
        nextTok++ ;
        break ;
     } ; // switch

    /***********************************************************************
    * Complete the ThmOrOpDefNode, if there is one.                        *
    ***********************************************************************/
    if (stepNum != null) { 
      // SZA: the next line commented, to prevent a NullPointerException
      // The method is not executed anyways.
      // tadn.construct(true, body, cm, symbolTable, null) ;
     } ;


    /***********************************************************************
    * Restore heirs and nextTok if the statement's tokens were inside a    *
    * NonExprBody node.                                                    *
    ***********************************************************************/
    if (hasNonExprBody) {
      heirs = savedHeirs ;
      nextTok = savedNextTok + 1;
     } ;
    
    /***********************************************************************
    * Set proof to the proof, or to null if there is none.  There is no    *
    * check made to see if this is a kind of step that should have a       *
    * proof.  Thus, adding a proof to something like a WITNESS statement   *
    * requires changing only the parsing phase (specified by tla+.jj).     *
    ***********************************************************************/
    ProofNode proof = null ;
    if (heirs.length > nextTok) { 
      if (isAssumeProve && !isSuffices) {
        symbolTable.pushContext(assumeContext) ;
       } ;
      proof = generateProof(heirs[nextTok], cm); 
      if (isAssumeProve && !isSuffices) {
        symbolTable.popContext();
       } ;
     } ;

    TheoremNode thm = new TheoremNode(stn, body, cm, proof, tadn);
    thm.suffices = isSuffices ;
    return thm; 

   } // generateNumerableStep

  private final LeafProofNode generateLeafProof(TreeNode stn, ModuleNode cm) 
  throws AbortException {
    TreeNode heirs[] = stn.heirs() ;
    LevelNode[] facts ;
    SymbolNode[] defs ;
    int nextTok = 0 ;
    boolean omitted = false ;

    /***********************************************************************
    * Skip over an optional "PROOF" (which can occur in a BY statement).   *
    ***********************************************************************/
    if (heirs[0].getKind() == TLAplusParserConstants.PROOF) {
      nextTok++ ;
     } ;
    
    boolean isOnly = false ;
    
    if (heirs[nextTok].getKind() == TLAplusParserConstants.BY) {
      /*********************************************************************
      * For a BY proof, call generate a UseOrHideNode and use its facts    *
      * and defs field.                                                    *
      *********************************************************************/
      UseOrHideNode uh = generateUseOrHide(stn, cm) ;
      isOnly = uh.isOnly ;
      facts = uh.facts;
      defs  = uh.defs;
      /*********************************************************************
      * The following check added by LL on 16 Feb 2009.                    *
      *********************************************************************/
      if (facts.length + defs.length == 0) { 
          errors.addError(stn.getLocation(), "Empty BY");
         };
     } 
    else{
      facts = new LevelNode[0];
      defs  = new SymbolNode[0];
      if (heirs[nextTok].getKind() == TLAplusParserConstants.OMITTED) {
       omitted = true ; };
     } ;
    return new LeafProofNode(stn, facts, defs, omitted, isOnly) ;    
   }

  UseOrHideNode 
  generateUseOrHide(TreeNode stn, ModuleNode cm) throws AbortException {
    /***********************************************************************
    * Since a BY statement currently has essentially the same syntax as    *
    * USE and HIDE, this is also used to parse a BY statement.  If given   *
    * a BY statement, it returns a UseOrHideNode that will be used to      *
    * form the LeafProofNode (and then thrown away).                       *
    ***********************************************************************/
    int kind = UseKind ;
    TreeNode heirs[] = stn.heirs() ;
   
    boolean isOnly = false;
      /*********************************************************************
      * True iff this is an "ONLY" step--either a BY ONLY or a USE ONLY.   *
      * However, we may decide not to include USE ONLY in the language,    *
      * which wil require a simple modification of the javacc code.        *
      *********************************************************************/
      
    if (heirs[0].getKind() == TLAplusParserConstants.HIDE)
      {kind = HideKind; } ;

    int nextTok = 1 ;

    /***********************************************************************
    * Skip over an optional "PROOF" (which can occur in a BY statement).   *
    ***********************************************************************/
    if (heirs[0].getKind() == TLAplusParserConstants.PROOF) {
      nextTok++ ;
     } ;

    if (nextTok >= heirs.length) {
        errors.addError(stn.getLocation(), "Empty BY, USE, or HIDE");
        return new UseOrHideNode(kind, stn, new LevelNode[0],  new SymbolNode[0], isOnly);
    }
    Vector vec = new Vector() ;
      /*********************************************************************
      * To hold the facts and then the defs.                               *
      *********************************************************************/

    if (heirs[nextTok].getKind() == TLAplusParserConstants.ONLY) {
      isOnly = true;
      nextTok++ ;
     } ;

    /***********************************************************************
    * Get the facts.                                                       *
    ***********************************************************************/
    while (  (nextTok < heirs.length) 
           && (heirs[nextTok].getKind() != TLAplusParserConstants.DF)) {
      if (heirs[nextTok].getKind() == TLAplusParserConstants.MODULE) {
        nextTok++ ;
        UniqueString moduleId = heirs[nextTok].getUS();
        ModuleNode moduleNode = symbolTable.resolveModule(moduleId);

        /*******************************************************************
        * The following added 16 Oct 2007 to allow a fact to be the        *
        * current module.  This will probably mean to use or hide facts    *
        * introduced so far in the current module.                         *
        *******************************************************************/
        if ((moduleNode == null) && (moduleId == cm.getName())) {
          moduleNode = cm ;} ;
        if (moduleNode != null) { vec.addElement(moduleNode) ; } 
        else {
          errors.addError(
            heirs[nextTok].getLocation(),
            "Module `" + moduleId + 
              "' used without being extended or instantiated.");
         }
       } // if
      else {
        /*******************************************************************
        * If the this token is an N_GeneralId, then we generate it here    *
        * using selectorToNode so we can call that method with the isFact  *
        * argument true.  Otherwise, we just call generateExpression.      *
        *******************************************************************/
        if (heirs[nextTok].getKind() == N_GeneralId) {
          /*****************************************************************
          * Here, we are using the fact that a theorem name must be a      *
          * GeneralId and not something like an N_GenInfixOp.              *
          *****************************************************************/
          vec.addElement(
             selectorToNode(genIdToSelector((SyntaxTreeNode) heirs[nextTok]), 
                                            0, true, false, cm)) ;
         }
        else if (heirs[nextTok].getKind() == N_AssumeProve) {
          vec.addElement(generateAssumeProve(heirs[nextTok], cm)) ;
          }
        else {
          vec.addElement(generateExpression(heirs[nextTok], cm)) ;
         } // else
       } // else
      nextTok++ ;
      if (   (nextTok < heirs.length)
          && (heirs[nextTok].getKind() == TLAplusParserConstants.COMMA)) {
        nextTok++ ;
       };
     } ; // while  
    LevelNode[] facts = new LevelNode[vec.size()] ;
    for (int i = 0 ; i < vec.size() ; i++) {
      facts[i] = (LevelNode) vec.elementAt(i) ;
     } ;

    /***********************************************************************
    * Get the defs.                                                        *
    ***********************************************************************/
    SymbolNode[] defs ;
    if (nextTok >= heirs.length) {
      defs = new SymbolNode[0] ;
     }
    else {
      vec = new Vector() ;
      nextTok++ ;
      while (nextTok < heirs.length) {
        if (heirs[nextTok].getKind() == TLAplusParserConstants.MODULE) {
          nextTok++ ;
          UniqueString moduleId = heirs[nextTok].getUS();
          ModuleNode moduleNode = symbolTable.resolveModule(moduleId);

          /*****************************************************************
          * The following added 16 Oct 2007 to allow a fact to be the      *
          * current module.  This will probably mean to use or hide        *
          * definitions introduced so far in the current module.           *
          *****************************************************************/
          if ((moduleNode == null) && (moduleId == cm.getName())) {
            moduleNode = cm ;} ;
          if (moduleNode != null) { vec.addElement(moduleNode) ; } 
          else {
            errors.addError(
              heirs[nextTok].getLocation(),
              "Module `" + moduleId + 
                "' used without being extended or instantiated.");
           }
         } // if
        else {
          Selector sel = genIdToSelector((SyntaxTreeNode) heirs[nextTok]) ;
          SemanticNode selToNd = selectorToNode(sel, -1, false, true, cm);
          if (   (selToNd instanceof OpDefNode)
              || (selToNd instanceof ThmOrAssumpDefNode)) { 
            SymbolNode def = (SymbolNode) selToNd;
            vec.addElement(def) ;
           } 
          else {
            /***************************************************************
            * This error is redundant, because it should have been caught  *
            * in selectorToNode.  But a little redundancy can't hurt.      *
            * But a little redundancy can't hurt.                          *
            ***************************************************************/
            errors.addError(
              heirs[nextTok].getLocation(),
              "DEF clause entry should describe a defined operator.") ;
           } // else
         } // else
        nextTok++ ;
        if (   (nextTok < heirs.length)
            && (heirs[nextTok].getKind() == TLAplusParserConstants.COMMA)) {
          nextTok++ ;
          };
       } ; // while  
      defs = new SymbolNode[vec.size()] ;
      for (int i = 0 ; i < vec.size() ; i++) {
        defs[i] = (SymbolNode) vec.elementAt(i) ;
       } ;
     } // else of if (nextTok >= heirs.length)
    return new UseOrHideNode(kind, stn, facts, defs, isOnly) ;
   } // generateUseOrHide

  void processRecursive(TreeNode tn, ModuleNode cm) {
    /***********************************************************************
    * Process a RECURSIVE statement.  Creates an OpDefNode for each of     *
    * the declared operators.                                              *
    ***********************************************************************/
    TreeNode[] children = tn.heirs() ;

    /***********************************************************************
    * Increment unresolvedCnt unresolvedSum, and, if necessary,            *
    * recursiveSectionCount.  This needs to be done before the calls to    *
    * startOpDefNode so that we are in a recursive section when it is      *
    * called.  Note that for                                               *
    *                                                                      *
    *   RECURSIVE op_1, ... , op_n                                         *
    *                                                                      *
    * children is the sequence of tokens                                   *
    *                                                                      *
    *   "RECURSIVE",  op_1,  ",",  ... ,  "," , op_n                       *
    *                                                                      *
    * so   children.length = 2*n  and  n = children.length / 2.            *
    ***********************************************************************/
    if (unresolvedSum == 0) {recursiveSectionCount ++; };
    int numOfDecls = children.length / 2 ;
    unresolvedCnt[curLevel] = unresolvedCnt[curLevel] + numOfDecls ;
    unresolvedSum = unresolvedSum + numOfDecls;

    for (int i = 1 ; i < children.length; i = i+2) {
      /*********************************************************************
      * Process the i-th declaration in the RECURSIVE statement.           *
      *********************************************************************/
      TreeNode declNode = children[i] ;

      /*********************************************************************
      * Set odn to an OpDeclNode made from the i-th declaration.           *
      *********************************************************************/
      OpDeclNode odn = 
         buildParameter(declNode, 
                        ConstantDeclKind, // Value of argument doesn't matter.
                        ConstantLevel,    // Value of argument doesn't matter.
                        cm,
                        false) ; // Not adding OpDeclNode to symbolTable

      /*********************************************************************
      * Set params to the array of parameters for the declared operator's  *
      * OpDefNode.                                                         *
      *********************************************************************/
      FormalParamNode[] params = new FormalParamNode[odn.getArity()] ;
      for (int ip = 0 ; ip < params.length ; ip++) {
        params[ip] = new FormalParamNode(null, 0, null, null, cm) ;
       } ;
      OpDefNode node =  startOpDefNode(odn.getName(), 
                                       declNode,
                                       UserDefinedOpKind,
                                       params,
                                       false, //localness
                                       cm,
                                       symbolTable);
         /******************************************************************
         * This node isn't saved anywhere.  It will be found either by     *
         * looking up the operator when the N_OperatorDefinition node is   *
         * encountered, or else by looking through the module's            *
         * recursiveDecls vector when it is discovered that some operator  *
         * has been declared but not defined (by finding unresolvedCnt >   *
         * 0 when coming to the end of a LET or of the module).            *
         ******************************************************************/
     cm.recursiveOpDefNodes.addElement(node) ;
         
     } // for (int i = 1 ...)   
    }



/***************************************************************************
* LABEL HANDLING                                                           *
*                                                                          *
* The following methods are used to create the labels fields of OpDefNode  *
* and LabelNode objects.  They are specified in terms of an abstract data  *
* object LS which is an element of                                         *
*                                                                          *
*   Seq( [labels   : SUBSET LabelNode,                                     *
*         paramSeq : Seq (SUBSET OpDeclNode)] )                            *
*                                                                          *
* Thus, for all i \in 1..Len(LS) :                                         *
*   LS[i].labels is a set of LabelNode objects                             *
*   LS[i].paramSeq is a sequence of sets of OpDeclNode objects.            *
*                                                                          *
* Initially, LS equals the empty sequence << >>.                           *
*                                                                          *
* We define                                                                *
*   Front(LS) == [i \in 1..Len(LS-1) |-> LS[i]]                            *
*   Last(LS)  == LS[Len(LS)]                                               *
*                                                                          *
* LS is a stack containing one element for each OpDefNode and LabelNode    *
* within which we are currently processing nodes, where Last(LS) is the    *
* inner-most such node.  Last(LS).paramSeq is a stack containing one       *
* element for each node that comes between the the preceding OpDefNode or  *
* LabelNode and the current node that introduces bound variables.          *
* Last(LS).paramSeq[j] is the set of bound variables introduced by the     *
* j-th such node, where Last(Last(LS).paramSeq) is the most recent such    *
* set of bound variables.                                                  *
***************************************************************************/

/***************************************************************************
* Code for handling labels was added in the following methods:             *
*    generateAssumeProve                                                   *
*    generateLambda                                                        *
*    processTheorem                                                        *
*    processAssumption                                                     *
*    processOperator                                                       *
*    processFunction                                                       *
*    processChoose                                                         *
*    processBoundQuant                                                     *
*    processUnboundQuant                                                   *
*    processSubsetOf                                                       *
*    processSetOfAll                                                       *
*    processFcnConst                                                       *
*    generateExpression                                                    *
*    generateProof                                                         *
***************************************************************************/

  LabelNode generateLabel(TreeNode stn, ModuleNode cm) 
   throws AbortException {

    boolean isAssumeProve = false ;
      /*********************************************************************
      * Set true iff this is a labeled ASSUME/PROVE.                       *
      *********************************************************************/
      
    if (!inOpDefNode()) {
      errors.addError(stn.getLocation(),
                      "Label not in definition or proof step.");
      return nullLabelNode ;
     };

    if (noLabelsAllowed()) {
      errors.addError(
        stn.getLocation(),
        "Label not allowed within scope of declaration in " +
        "nested ASSUME/PROVE.");
      return nullLabelNode ;
      } ;

    /***********************************************************************
    * For now at least, and probably forever, we are not allowing an       *
    * expression to be labeled if it lies inside an EXCEPT clause--which   *
    * means if it is used where an "@" could appear.  The test for this    *
    * is taken from generateExpression.                                    *
    ***********************************************************************/
    if (!((excStack.empty() || excSpecStack.empty()))) {
          errors.addError(stn.getLocation(),
             "Labels inside EXCEPT clauses are not yet implemented.");
          return nullLabelNode ;
      } ;

    TreeNode[] labelExpChildren  = stn.heirs() ;

    /***********************************************************************
    * We first process the body, since we need it to create the LabelNode. *
    ***********************************************************************/
    pushLS() ;
    LevelNode body ;
      if (labelExpChildren[2].getKind() == N_AssumeProve) {
        body = generateAssumeProve(labelExpChildren[2], cm) ;
        isAssumeProve = true ;
       }
      else { body = generateExpression(labelExpChildren[2], cm) ; } ;
    Hashtable ht = popLabelNodeSet() ;

    /***********************************************************************
    * We now create the LabelNode.                                         *
    ***********************************************************************/
    UniqueString name ;
    FormalParamNode[] params;
      /*********************************************************************
      * The label's name and parameter list.                               *
      *********************************************************************/
    if (labelExpChildren[0].getKind() == N_GeneralId) {
      /*********************************************************************
      * There are no arguments to the label.                               *
      *********************************************************************/
      name = labelExpChildren[0].heirs()[1].getUS() ;
      params = new FormalParamNode[0] ;
     }
    else {
     /**********************************************************************
     * The label should be represented as an N_OpApplication node.         *
     **********************************************************************/
      if (labelExpChildren[0].getKind() != N_OpApplication)
        { throw new WrongInvocationException("Label has unexpected syntax tree kind.") ; };

      TreeNode[] opApplChildren = labelExpChildren[0].heirs() ;
      name = opApplChildren[0].heirs()[1].getUS() ;
      TreeNode[] opArgsChildren =  opApplChildren[1].heirs() ;
      int numOfParams = (opArgsChildren.length - 1) / 2 ;
      params = new FormalParamNode[numOfParams] ;
      for (int i = 0; i < numOfParams; i++) {
        /*******************************************************************
        * We have to get the FormalParamNode objects for the parameter     *
        * array params by looking them up in the current context, since    *
        * they could be either ConstantLevel (normal case) or StateLevel   *
        * (if they're introduced in a \AA or \EE expression).              *
        *******************************************************************/
        TreeNode argSyntaxNode = opArgsChildren[2*i + 1];
        UniqueString argName = argSyntaxNode.heirs()[1].getUS() ;
        SymbolNode argNode = symbolTable.resolveSymbol(argName) ;
        FormalParamNode arg = null ;
        if (argNode instanceof FormalParamNode) 
          {arg = (FormalParamNode) argNode ;}
         else {errors.addError(argSyntaxNode.getLocation(),
                               "Illegal parameter " + argName.toString() +
                               " of label `" + name.toString() + "'.");  
               arg = new FormalParamNode(argName, 0, argSyntaxNode, null, cm);
                 /**********************************************************
                 * Create a dummy FormalParamNode to prevent a null        *
                 * pointer exception in later processing.                  *
                 **********************************************************/
         };      
        params[i] = arg ;
       } // for
     } ; // else
    SemanticNode cg = null ;
    if (assumeProveDepth > 0) {cg = currentGoal;} ;
    LabelNode retVal = new LabelNode(stn, name, params, currentGoal, 
                                     currentGoalClause, body, isAssumeProve) ;
    retVal.setLabels(ht) ;
    boolean ignore = formalParamsEqual(retVal) ;
      /*********************************************************************
      * We throw away the return value because if there's an error, it is  *
      * reported by the method.                                            *
      *********************************************************************/
    if (!addLabelNodeToSet(retVal)) {
      errors.addError(stn.getLocation(),
                      "Duplicate label `" + name.toString() + "'."); 
     } ;
    return retVal ;
   } // generateLabel

  Vector LSlabels   = new Vector() ;
    /***********************************************************************
    * LSlabels.elementAt(i) is a HashTable that represents                 *
    * LS.labels[i+1].  The values in the Hashtable are LabelNode objects,  *
    * where ln.getName() is the key of object ln.  The empty set is        *
    * represented by null.                                                 *
    ***********************************************************************/

  Vector LSparamSeq = new Vector() ;
    /***********************************************************************
    * LsparamSeq.elementAt(i) is a Vector whose elements are of type       *
    * FormalParamNode[] that represents LS.paramSeq[i+1].  In particular   *
    * LS.paramSeq[i+1][j+1] equals                                         *
    *   LET foo == (FormalParamNode[])                                     *
    *                  ((Vector) LsparamSeq.elementAt(i))).elementAt(j)    *
    *   IN  { (FormalParamNode) foo[j] : j \in 0 .. foo.length}            *
    ***********************************************************************/

  void pushLS() {
    /***********************************************************************
    * Implements   LS' = Append(LS, [labels |-> {}, paramSeq |-> << >>])   *
    * That is, it pushes an "empty" record onto the end of LS.             *
    ***********************************************************************/
    LSlabels.addElement(null) ;
    LSparamSeq.addElement(new Vector()) ;
   }

  Hashtable popLabelNodeSet() {
    /***********************************************************************
    * Implements  LS' = Front(LS)                                          *
    *             return Last(LS).labels                                   *
    ***********************************************************************/
    int size = LSlabels.size() ;
    if (size == 0) 
      {throw new WrongInvocationException("popLabelNodeSet called on empty stack.");} ;
    Hashtable retVal = (Hashtable) LSlabels.elementAt(size-1) ;
    LSlabels.removeElementAt(size-1) ;
    LSparamSeq.removeElementAt(size-1) ;
    return retVal ;
   }    

  boolean addLabelNodeToSet(LabelNode ln) {
    /***********************************************************************
    * Implements                                                           *
    *   LET succ == \A eln \in Last(LS).labels : eln.name # ln.name        *
    *   IN  LS' = IF succ THEN [LS EXCEPT                                  *
    *                             ![Len(LS)].labels = @ \cup {ln}]         *
    *                     ELSE Labeling Stack                              *
    *       return succ                                                    *
    * That is, it adds LabelNode ln to Last(LS).labels iff there is not    *
    * already a LabelNode with the same name in it, otherwise do nothing.  *
    * It returns true iff ln was added.                                    *
    ***********************************************************************/
    int size = LSlabels.size() ;
    if (size == 0) 
      {throw new WrongInvocationException("addLabelNodeToSet called on empty stack.");} ;
    Hashtable ht = (Hashtable) LSlabels.elementAt(size-1) ;
    if (ht == null) {
      ht = new Hashtable() ;
      LSlabels.setElementAt(ht, size-1) ;
     } 
    boolean retVal = ! ht.containsKey(ln.getName()) ;
    if (retVal) { ht.put(ln.getName(), ln); } ;
    return retVal ;
   }    

  void pushFormalParams(FormalParamNode[] odns) {
    /***********************************************************************
    * Implements                                                           *
    *                                                                      *
    *   LS' = IF LS # << >>                                                *
    *           THEN [LS EXCEPT ![Len(LS)].paramSeq =                      *
    *                         Append(@, {odns[i] : i \in DOMAIN odns)]     *
    *           ELSE LS                                                    *
    *                                                                      *
    * That is, if LS is not empty, then it pushes the set of               *
    * FormalParamNode objects in the array odns onto the end of            *
    * Last(LS).paramSeq.                                                   *
    ***********************************************************************/
    if (!inOpDefNode()){return;} ;
    Vector lastFormalParams = 
            (Vector) LSparamSeq.elementAt(LSparamSeq.size() - 1) ;
    lastFormalParams.addElement(odns) ;
   }

  void popFormalParams() {
    /***********************************************************************
    * Implements                                                           *
    *                                                                      *
    *   LS' = IF LS # << >>                                                *
    *           THEN [LS EXCEPT ![Len(LS)].paramSeq = Front(@)]            *
    *           ELSE LS                                                    *
    * That is, if LS is not empty, then it removes the last item from      *
    * Last(LS).paramSeq.                                                   *
    ***********************************************************************/
    if (!inOpDefNode()){return;} ;
    Vector lastFormalParams = 
            (Vector) LSparamSeq.elementAt(LSparamSeq.size() - 1) ;
    int size = lastFormalParams.size() ;
    if (size == 0) 
      {throw new WrongInvocationException("popFormalParams called on empty stack.");} ;
    lastFormalParams.removeElementAt(size - 1);
   }    

  boolean formalParamsEqual(LabelNode ln) {
    /***********************************************************************
    * Returns  LET odns == ln.params                                       *
    *          IN  /\ \A i, j \in DOMAIN odns :                            *
    *                     (i # j) => odns[i] # odns[j]                     *
    *              /\ {odns[i] : i \in DOMAINE odns} =                     *
    *                    UNION {Last(LS).parmSeq[i] :                      *
    *                              i \in DOMAIN Last(LS).parmSeq}          *
    * That is, it returns true iff all the FormalParamNode objects in      *
    * odns are distinct and the set of all thos objects equals the union   *
    * of all the sets in the sequence Last(LS).paramSeq.                   *
    *                                                                      *
    * If this returns false, then an error message explains why.           *
    ***********************************************************************/
    boolean retVal = true ;
    HashSet opParams = new HashSet() ;
    FormalParamNode[] odns = ln.params ;
    for (int i = 0; i < odns.length; i++) {
      if (!opParams.add(odns[i])) {
        retVal = false;
        errors.addError(ln.stn.getLocation(),
                        "Repeated formal parameter " + 
                        odns[i].getName().toString() + " \nin label `" +
                        ln.getName().toString() + "'.") ;
       };
      } // for ;
    Vector lastFormalParams = 
            (Vector) LSparamSeq.elementAt(LSparamSeq.size() - 1) ;
    int size = lastFormalParams.size() ;
    for (int i = 0 ; i < size; i++) {
      FormalParamNode[] ops = (FormalParamNode[]) lastFormalParams.elementAt(i);
      for (int j = 0 ; j < ops.length ; j++) {
        if (! opParams.remove(ops[j])) {
         retVal = false;
         errors.addError(ln.stn.getLocation(),
                         "Label " + ln.getName().toString() + 
                         " must contain formal parameter `" + 
                         ops[j].getName().toString() + "'.") ;         
         };
       } // for j;
      } // for i;
    if (!opParams.isEmpty()) {
     retVal = false ;
     Iterator iter = opParams.iterator();
     String res = "Label " + ln.getName().toString() +
                  " declares extra parameter(s)  ";
      while (iter.hasNext()){
        FormalParamNode nd = (FormalParamNode) iter.next() ;
        res = res + nd.getName().toString() + "  ";
       } // while
      errors.addError(ln.stn.getLocation(), res) ;
      } // if
    return retVal ;
   }

  boolean inOpDefNode() { return LSlabels.size() > 0; }
    /***********************************************************************
    * Returns true iff LS is not equal to the empty sequence << >>.        *
    ***********************************************************************/

  FormalParamNode[] flattenParams(FormalParamNode[][] array) {
    /***********************************************************************
    * Flatten a 2-dimensional array of FormalParamNodes into a             *
    * 1-dimensional array.  Used because the oan.boundedBoundSymbols       *
    * field for an OpApplNode is such a 2-dimensional array, since         *
    * "bounded bound symbols" may be tuples.                               *
    ***********************************************************************/
    int size = 0 ;
    for (int i = 0 ; i < array.length; i++) { size = size + array[i].length; } ;
    FormalParamNode[] res = new FormalParamNode[size] ;
    int k = 0 ;
    for (int i = 0 ; i < array.length; i++) { 
      for (int j = 0 ; j < array[i].length; j++) {
        res[k] = array[i][j] ;
        k++ ;
        } ; // for j
     } ; // for i
    return res ;
   }    

/***************************************************************************
*                            Recursion Processing                          *
*                                                                          *
* This is the code for setting the fields of OpDefNode objects that are    *
* related to recursion--namely, letInLevel, inRecursive,                   *
* inRecursiveSection.  See the description of these fields in              *
* semantic/OpDefNode.java to see what they mean.                           *
*                                                                          *
* A tool might also want to compute the strongly connected components of   *
* the dependency graph--the graph of OpDefNode objects containing an edge  *
* from n to m iff m's operator appears in the body of n.                   *
*                                                                          *
* I originally thought that the dependency graph could be created while    *
* the semantic graph was being constructed, and that the strongly          *
* connected components could be computed incrementally by running a        *
* connected-component algorithm at the end of each recursive section.  I   *
* thought that could be done easily by creating an OpDefNode for a         *
* definition before processing the definition's body, and adding to a      *
* field in that OpDefNode a list of the OpDefNodes that appeared in        *
* OpApplNodes in the body.  However, that didn't work because of           *
* definitions like                                                         *
*                                                                          *
*   f == LET f == ...                                                      *
*        IN  ...                                                           *
*                                                                          *
* So, I abandoned that idea.  It's probably easiest to compute the         *
* connected components after the module is processed.                      *
*                                                                          *
* If we ever do want to construct those connected components, we can run   *
* a version of Tarjan's algorithm for computing strongly connected         *
* components of a directed graph.  A +cal coding of this algorithm is in   *
* the file Tarjan.tla, a copy of which appears as a comment at the end of  *
* this file.                                                               *
***************************************************************************/

/***************************************************************************
* The fields.                                                              *
***************************************************************************/
  final int MaxLetInLevel = 100 ;
    /***********************************************************************
    * It seems safe to assume that LETs won't be nested more than 100      *
    * deep, so we can use arrays instead of having to deal with vectors    *
    * to allow arbitrary depths.                                           *
    ***********************************************************************/

  int   curLevel = 0 ;
    /***********************************************************************
    * The current LET/IN nesting level--that is, the number of LET/IN      *
    * statements within which the nodes we are currently processing lie.   *
    ***********************************************************************/

  int[] unresolvedCnt = new int[MaxLetInLevel] ;
    /***********************************************************************
    * For i \in 0..curLevel, the value of unresolvedCnt[i] is the number   *
    * of operators declared in RECURSIVE statements at let/in level i that *
    * have not yet been defined.                                           *
    ***********************************************************************/

  int unresolvedSum = 0;
    /***********************************************************************
    * Equals the sum from i = 0 to curLevel of unresolvedCnt[i].           *
    ***********************************************************************/

  int recursiveSectionCount = 0 ;
    /***********************************************************************
    * This field is incremented whenever a new recursive section is        *
    * begun--that is, when unresolvedSum changes from 0 to a positive      *
    * value (which must be 1).                                             *
    ***********************************************************************/

//  Code to construct dependence graph removed by LL on 7 Apr 2007
//  OpDefNode[] defStack = new OpDefNode[MaxLetInLevel] ;
//  int defStackLen ;
//    /***********************************************************************
//    * The elements defStack[0] ... defStack[defStackLen-1] form the stack  *
//    * of OpDefNode objects representing definitions being processed.  For  *
//    * example, in                                                          *
//    *                                                                      *
//    *    Foo == LET Bar == LET FB == exp ..                                *
//    *                                                                      *
//    * while processing exp the stack will contain the OpDefNode objects    *
//    * for Foo, Bar, and FB. This stack is used to construct the nbrs       *
//    * field of the OpDefNode objects on the stack.                         *
//    *                                                                      *
//    * Note that defStackLen \leq curLevel.  It may be strictly less        *
//    * because we could be in the IN clause of some of the nested LET/IN    *
//    * statements.                                                          *
//    ***********************************************************************/

// Was put into the ModuleNode object, since otherwise it would contain
// nodes from all inner modules.
//  Vector recursiveDecls = new Vector(100) ;
//    /***********************************************************************
//    * The set of OpDefNode objects that originally appeared in a           *
//    * RECURSIVE declaration.  For now, it is used only to find operators   *
//    * that were declared in a RECURSIVE declaration but never defined.     *
//    * Perhaps some other use will be found for it, in which case it        *
//    * should be put into the module's ModuleNode object.                   *
//    ***********************************************************************/
    
  int max_dfs = 0;
    /***********************************************************************
    * A variable used in the Tarjan algorithm.                             *
    ***********************************************************************/
    
  Vector nstack = new Vector(10) ;
    /***********************************************************************
    * A vector of OpDefNode objects, representing the stack of the Tarjan  *
    * algorithm.                                                           *
    ***********************************************************************/

  int moduleNestingLevel = -1 ;
    /***********************************************************************
    * When processing a module, this is its nesting level--that is, its    *
    * depth in the tree of inner modules of the outermost module.          *
    ***********************************************************************/

/***************************************************************************
* Methods.                                                                 *
***************************************************************************/
  OpDefNode startOpDefNode(UniqueString us,
                           TreeNode tn, 
                           int kind,
                           FormalParamNode[] params,
                           boolean localness,
                           ModuleNode oModNode,
                           SymbolTable st
                           )       {
    /***********************************************************************
    * Called to create an OpDefNode for a RECURSIVE declaration.  The      *
    * params argument should be an array of dummy FormalParamNode          *
    * objects, with null names.  The OpDefNode's setParams method should   *
    * be used to add the actual formal parameter's to the object.          *
    *                                                                      *
    * Note: for an operator declared in a RECURSIVE statement, this        *
    * method is called when processing that statement with the Treenode    *
    * tn equal to the syntax tree node for the declaration.                *
    ***********************************************************************/
    OpDefNode odn = new OpDefNode(us, UserDefinedOpKind, params, localness,
                                  null, // the expression 
                                  oModNode, st, tn, false, null) ;
//  was incrementing it twice
//    unresolvedCnt[curLevel] ++ ;
//    unresolvedSum = unresolvedSum ++ ;

    oModNode.recursiveDecls.addElement(odn) ;

    odn.letInLevel         = curLevel ;
    odn.inRecursive        = true ;
    odn.inRecursiveSection = true ;
    odn.recursiveSection   = recursiveSectionCount;
    oModNode.opDefsInRecursiveSection.addElement(odn) ;

// the participating and nbrs field have been removed from OpDefNode objects
//    odn.participating      = true ;
//    odn.nbrs               = new Vector(10);

//  Code to construct dependence graph removed by LL on 7 Apr 2007
//      if (! recursive) {
//        defStack[defStackLen] = odn ;
//        defStackLen ++ ;
//       } ;
    return odn;
   }

  void endOpDefNode(OpDefNode nd,
                    ExprNode  exp,
                    TreeNode  stn)  {
    /***********************************************************************
    * Called to complete the creation of an OpDefNode nd that was created  *
    * by an invocation of startOpDefNode.  If we are processing recursive  *
    * definitions, then it modifies unresolvedCnt and unresolvedSum if     *
    * necessary.                                                           *
    *                                                                      *
    * When called for an operator not declared in a RECURSIVE statement,   *
    * the TreeNode stn is the same one that startOpDefNode was called      *
    * with to create the OpDefNode.                                        *
    ***********************************************************************/
    nd.isDefined = true ;

    /***********************************************************************
    * Set the node's body and syntax-tree node.                            *
    ***********************************************************************/
    nd.setBody(exp) ;
    nd.stn = stn ;

//  Code to construct dependence graph removed by LL on 7 Apr 2007
//    if (unresolvedSum > 0) {
//      /*********************************************************************
//      * Pop OpDefNode off defStack.                                        *
//      *********************************************************************/
//      defStackLen -- ;
//     } ;

    if (nd.inRecursive) { 
      unresolvedCnt[curLevel] -- ;
      unresolvedSum -- ;
//  Code to construct dependence graph removed by LL on 7 Apr 2007
//      if (unresolvedSum == 0) {
//        tarjan() ; 
//        for (int i = 0 ; i < participants.size(); i++) {        
//          ((OpDefNode) participants.elementAt(i)).participating = false ;
//         } ; // for
//        participants = new Vector(100) ;
//       } // if (unresolvedSum == 0)
      if (unresolvedSum < 0) { 
          throw new WrongInvocationException("Defined more recursive operators than were declared " +
                    "in RECURSIVE statements.") ;
       };
     } // if (nd.inRecursive)
   }

//  Code to construct dependence graph removed by LL on 7 Apr 2007
//  void registerSymbolNode(SymbolNode nd) {
//    /***********************************************************************
//    * Called upon creating an OpApplNode whose operator has SymbolNode     *
//    * nd.  If we are processing recursive definitions, and if nd is an     *
//    * OpDefNode that is a participant, then nd is added to dfnd.nbrs, for  *
//    * every node dfnd in defStack (if it's not already there).             *
//    ***********************************************************************/
//    if (   (unresolvedSum > 0)
//        && (nd instanceof OpDefNode)) {
//        OpDefNode odn = (OpDefNode) nd ;
//        if (odn.participating) {
//          for (int i = 0 ; i < defStackLen ; i++) {
//            defStack[i].nbrs.addElement(odn) ;
//           } ;
//         } ; // if
//     } ; // if
//   }

//  Code to construct dependence graph removed by LL on 7 Apr 2007
//  SymbolNode findSymbol(UniqueString name) {
//    /***********************************************************************
//    * To gather the data needed to compute the dependence graph, when      *
//    * processing a definition, the operator being defined is put into the  *
//    * symbol table before the body of the definition is processed.         *
//    * However, if the operator is not declared in a RECURSIVE statement,   *
//    * a use of it in the body must be reported as an error.  To do this,   *
//    * calls that of symbolTable.resolveSymbol have been replaced by calls  *
//    * to findSymbol, which checks if the found symbol is not defined or    *
//    * declared at this point, and returns null if that is the case.        *
//    ***********************************************************************/
//    SymbolNode nd = symbolTable.resolveSymbol(name) ;
//    if ((nd != null) && (nd instanceof OpDefNode)) {
//      OpDefNode ond = (OpDefNode) nd ;
//      if ((!ond.isDefined) && (!ond.inRecursive)) { nd = null; } ;
//     };
//    return nd ;
//   } // findSymbol


  void setOpDefNodeRecursionFields(OpDefNode odn, ModuleNode cm) {
    /***********************************************************************
    * Called to set the field odn.letInLevel and the fields                *
    * odn.recursiveSection and odn.inRecursiveSection if they need         *
    * non-default values, and to add odn to cm.opDefsInRecursiveSection    *
    * if necessary.                                                        *
    ***********************************************************************/
    odn.letInLevel = curLevel ;
    if (unresolvedSum > 0) {
        odn.recursiveSection   = recursiveSectionCount;
        odn.inRecursiveSection = (unresolvedCnt[curLevel] > 0) ;
        cm.opDefsInRecursiveSection.addElement(odn) ;
       }
    
    } 

  void checkIfInRecursiveSection(TreeNode tn, String type) {
    /***********************************************************************
    * Report an error if we are in a recursive section--between an         *
    * operator's declaration in a RECURSIVE statement and its definition.  *
    ***********************************************************************/
    if (unresolvedSum > 0) {
            errors.addError(tn.getLocation(),
                            type + " may not appear within " +
                            "a recursive definition section."   
                           ) ;
     }
    }

  void checkForUndefinedRecursiveOps(ModuleNode cm) {
    /***********************************************************************
    * Called at the end of a LET clause and at the end of processing a     *
    * module to check for operators that were declared in a RECURSIVE      *
    * statement but not defined.  It calls errors.addError to report any   *
    * that it finds.                                                       *
    ***********************************************************************/
    /***********************************************************************
    * The number of operators declared in RECURSIVE statements within the  *
    * LET but not defined equals unresolvedCnt[curLevel].                  *
    ***********************************************************************/
    if (unresolvedCnt[curLevel] > 0) {
      /*********************************************************************
      * Go through the module's recursiveDecls vector to find all symbols  *
      * declared at the current LET/IN level but not defined.              *
      *********************************************************************/
      for (int i = 0 ; i < cm.recursiveDecls.size() ; i++) {
        OpDefNode odn = (OpDefNode) cm.recursiveDecls.elementAt(i) ;
        if (   (odn.letInLevel == curLevel)
            && odn.inRecursive
            && (! odn.isDefined)) {
            errors.addError(odn.getTreeNode().getLocation(),
                            "Symbol " + odn.getName().toString() +
                            " declared in RECURSIVE statement but not defined."   
                           ) ;
          } ;
       }; // for

      unresolvedSum = unresolvedSum - unresolvedCnt[curLevel] ;
        /*******************************************************************
        * Need to update unresolvedSum correct because we are effectively  *
        * setting unresolvedCnt[curLevel] to 0.                            *
        *******************************************************************/
     }; // if (unresolvedCnt[curLevel] > 0) 
    }


//  void tarjan() {
//    /***********************************************************************
//    * This is the Java version of the algorithm in the file Tarjan.tla, a  *
//    * copy of which appears below.                                         *
//    ***********************************************************************/
///***************************************************************************
//* XXXXXX: Not yet implemented.                                             *
//***************************************************************************/
//   }

}   

/************************ file Tarjan.tla ***********************************
------------------------------ MODULE Tarjan --------------------------------
(***************************************************************************)
(* This version of Tarjan's algorithm for computing the strongly           *)
(* connected components of a directed graph was adapted from the version   *)
(* of 27 Mar 2007 on the Wikipedia page                                    *)
(*                                                                         *)
(* http://en.wikipedia.org/wiki/Tarjan's_strongly_connected_components_algorithm *)
(*                                                                         *)
(* One modification is that the set of connected components it returns     *)
(* does not contain a singleton {n} unless n has an edge pointing to       *)
(* itself.                                                                 *)
(*                                                                         *)
(* This is an implementation of the algorithm in Tarjan.tla with data      *)
(* structures that correspond to the ones used in the algorithm for        *)
(* constructing dependency components in semantic/Generator.               *)
(*                                                                         *)
(*                                                                         *)
(* I have not rigorously verified this algorithm, but I think I understand *)
(* why it works.  I have tested it only on the 10 graphs at the end of     *)
(* this file.                                                              *)
(***************************************************************************)

EXTENDS Integers, Sequences, TLC

CONSTANT N,         \* The number of nodes
         Neighbors  \* A sequence of edges.

Node == 1..N

ASSUME Neighbors \in Seq(Node \X Node) 

Min(a, b) == IF a < b THEN a ELSE b

Front(s) == [i \in 1 .. (Len(s)-1) |-> s[i]]
  (*************************************************************************)
  (* The sequence obtained from a sequence s by deleting the last item.    *)
  (*************************************************************************)

Last(s) == s[Len(s)]
  (*************************************************************************)
  (* The last item in the sequence s.                                      *)
  (*************************************************************************)

(***************************************************************************)
(* I believe the algorithm works because it maintains the following        *)
(* invariants (at reasonable points in the code).  We say that node        *)
(* nstack[i] precedes nstack[j] iff i < j.                                 *)
(*                                                                         *)
(*   - A node n is in nstack iff n.dfs \geq 0                              *)
(*                                                                         *)
(*   - For all nodes n # m in nstack, if n precedes m then:                *)
(*       /\ n.dfs < m.dfs.                                                 *)
(*       /\ there is a path from n to m in the graph.                      *)
(*                                                                         *)
(*   - For every node n in nstack,                                         *)
(*      /\ n.lowlink \leq n.dfs and                                        *)
(*      /\ there is a node m in nstack such that                           *)
(*          1. n.lowlink = m.dfs.                                          *)
(*          2. if m # n then there is a path from n to m in the graph.     *)
(*      /\ For every node m in the same connected component as n:          *)
(*         m.examined = TRUE  implies  m is in nstack                      *)
(***************************************************************************)

(*************************
--algorithm Tarjan2
variables nstack = << >> ;        
            (***************************************************************)
            (* The stack of nodes, where nstack[1] is the bottom of the    *)
            (* stack.                                                      *)
            (***************************************************************)
          max_dfs = 0 ;      
            (***************************************************************)
            (* Incremented by 1 every time a new element is added to the   *)
            (* stack.                                                      *)
            (***************************************************************)

          data = [nd \in Node |-> [lowlink  |-> -1, 
                                   dfs      |-> -1, 
                                   examined |-> FALSE,
                                   nbrs     |-> << >>, 
                                     (*****************************************)
                                     (* A sequence of nodes to which there    *)
                                     (* are edges from this node.  The        *)
                                     (* same node may appear multiple         *)
                                     (* times.                                *)
                                     (*****************************************)
                                   nxtDep   |-> -1 ]] ;
            (***************************************************************)
            (* The information maintained for the nodes.  Note that        *)
            (*                                                             *)
            (*  - Node nd is on nstack iff data[nd].dfs \geq 0, in         *)
            (*    which case  nstack[data[nd].dfs + 1] = nd.               *)
            (*                                                             *)
            (*  - nbrs is set from Neighbors by the initialization code.   *)
            (*                                                             *)
            (*  - nxtDep represents the nextDependency field of the        *)
            (*    OpDefNode object, where a value of -1 represents         *)
            (*    null.  Following nxtDep pointers leads in a cycle of     *)
            (*    the node's connected component.  See the comments on     *)
            (*    the nextDependency field in semantic/OpDefNode.          *)
            (***************************************************************)

          idx ;  \* A counter variable.

procedure tarjan(n)
 variable nxt ;     \* A counter variable
          nxtnbr ;  \* An abbreviation
          
 begin
   data[n].lowlink  := max_dfs || 
   data[n].dfs      := max_dfs || 
   data[n].examined := TRUE ;
   max_dfs := max_dfs + 1;
   nstack  := Append(nstack, n) ;
   nxt := 1 ;
   while nxt \leq Len(data[n].nbrs) do
     nxtnbr := data[n].nbrs[nxt] ;
     if ~ data[nxtnbr].examined
       then (***************************************************************)
            (* nxtnbr is unexamined                                        *)
            (***************************************************************)
            call tarjan(nxtnbr) ;
            data[n].lowlink := Min(data[n].lowlink, data[nxtnbr].lowlink) ;

       elsif data[nxtnbr].dfs \geq 0  
            then (**********************************************************)
                 (* nxtnbr is in nstack                                    *)
                 (**********************************************************)
                 data[n].lowlink := Min(data[n].lowlink, data[nxtnbr].dfs) ;
      end if ;
      nxt := nxt + 1;
   end while ;
   if data[n].lowlink = data[n].dfs
     then (*****************************************************************)
          (* The set of all nodes on nstack from n to the end form a       *)
          (* connected component.                                          *)
          (*****************************************************************)
          nxtnbr := Last(nstack) ;  \* save last node on stack.
          while n # Last(nstack) do
            data[Last(nstack)].nxtDep := nstack[Len(nstack)-1] ||
            data[Last(nstack)].dfs    := -1 ;
              (*************************************************************)
              (* Make nxtDep field of last node on stack point to next to  *)
              (* last node.                                                *)
              (*************************************************************)
            nstack := Front(nstack) ;
          end while ;
          if \/ n # nxtnbr
             \/ \E i \in 1..Len(data[n].nbrs) : n = data[n].nbrs[i]
            then (**********************************************************)
                 (* Form a connected component consisting of just n only   *)
                 (* if n is a neighbor of itself.                          *)
                 (**********************************************************)
            data[n].nxtDep := nxtnbr; 
          end if;
          data[n].dfs    := -1 ;
          nstack := Front(nstack) ;
   end if ;
   data[n].nbrs := << >> ;
     (**********************************************************************)
     (* Can garbage collect the sequence of neighbors.                     *)
     (**********************************************************************)
   return ;
end procedure 

begin
   (************************************************************************)
   (* Initialize the nbrs field of data elements from Neighbors.           *)
   (************************************************************************)
   idx := 1 ;
   while idx \leq Len(Neighbors) do
     with edge = Neighbors[idx] do
      data[edge[1]].nbrs := Append(data[edge[1]].nbrs, edge[2]) ;
     end with ;
   idx := idx + 1;
   end while ;
   
   (************************************************************************)
   (* while there is an unexamined node, call tarjan(nd)                   *)
   (* for any unexamined node nd.                                          *)
   (************************************************************************)
   idx := 1 ;
   while idx \leq N do
     if data[idx].lowlink < 0    
       then (***************************************************************)
            (* idx is unexamined                                           *)
            (***************************************************************)
            call tarjan(idx) ;
       end if;
     idx := idx + 1 ;
   end while ;

   (************************************************************************)
   (* print result.                                                        *)
   (************************************************************************)
   idx := 1 ;
   while idx \leq N do
     if data[idx].nxtDep \geq 0 
       then print <<idx, "->", data[idx].nxtDep>>
     end if ;
     idx := idx+1;
   end while
end algorithm
***********************) 

\* BEGIN TRANSLATION
\* END TRANSLATION

\**** Test data

Node1 == {1, 2, 3, 4}

Nbrs1 == << <<1, 2>>,   \* components 1 and 3,4
            <<1, 2>>,   \* components 1 and 3,4
            <<1, 1>>,
            <<1, 1>>,
            <<3, 4>> ,
            <<3, 4>> ,
            <<4, 3>> ,
            <<4, 3>>,
            <<4, 3>>
         >>

Nbrs2 == << <<1, 2>>, \* components 1 and 3,4
            <<1, 1>>,
            <<1, 3>>,
            <<3, 4>>,
            <<4, 3>>
         >>
Nbrs3 == << <<1, 2>>, \* components 1 and 3,4
            <<1, 1>>,
            <<3, 1>>,
            <<3, 4>>,
            <<4, 3>>
         >>
Nbrs4 == << <<1, 3>>,  \* 
           <<1, 8>>,   \* componetns:  2,3,4,5 and 7,8,9
           <<1, 9>>,
           <<1, 9>>,
           <<1, 9>>,
           <<3, 2>>,
           <<3, 2>>,
           <<2, 4>>,
           <<4, 5>>,
           <<4, 10>>,
           <<5, 3>>,
           <<8, 7>>,
           <<8, 7>>,
           <<9, 8>>,
           <<7, 9>>,
           <<7, 9>>,
           <<9, 10>>,
           <<9, 10>>,
           <<9, 10>>
         >>

Nbrs5 == << <<1, 8>>,  \* components 7,8,9
           <<1, 9>>,
           <<4, 10>>,
           <<8, 7>>,
           <<9, 8>>,
           <<7, 9>>,
           <<9, 10>>
         >>

Nbrs6 == << <<6, 4>>,  \* components 2,3,4,5
           <<3, 4>>,
           <<4, 5>>,
           <<5, 2>>,
           <<2, 3>>,
           <<5, 1>>,
           <<2, 1>>
         >>

Nbrs7 == << <<1, 7>>, \* 1 component with 1..9 \ {3}
           <<1, 9>>,
           <<2, 1>>,  
           <<3, 2>>,
           <<3, 6>>,
           <<4, 6>>,
           <<5, 2>>,
           <<6, 5>>,
           <<6, 8>>,
           <<7, 5>>,
           <<7, 8>>,
           <<8, 4>>,
           <<8, 10>>,
           <<9, 7>>,
           <<9, 10>>
         >>
Nbrs8 == << <<1, 7>>, \* 1 component with 1..8 \ {3}
           <<2, 1>>,  
           <<3, 2>>,
           <<3, 2>>,
           <<3, 2>>,
           <<3, 6>>,
           <<4, 6>>,
           <<5, 2>>,
           <<6, 5>>,
           <<6, 8>>,
           <<6, 8>>,
           <<6, 8>>,
           <<7, 5>>,
           <<7, 8>>,
           <<8, 4>>,
           <<8, 10>>,
           <<9, 7>>,
           <<9, 10>>
         >>
Nbrs9 == <<           \* 4,6, 7,8,9,10 
           <<2, 1>>,  
           <<3, 2>>,
           <<3, 6>>,
           <<4, 6>>,
           <<4, 6>>,
           <<4, 6>>,
           <<5, 2>>,
           <<6, 5>>,
           <<6, 8>>,
           <<7, 5>>,
           <<7, 5>>,
           <<7, 5>>,
           <<7, 5>>,
           <<7, 8>>,
           <<8, 4>>,
           <<8, 10>>,
           <<9, 7>>,
           <<10, 9>>
         >>
Nbrs == <<           \* 1, 3, 4, 5 and 6
           <<1, 4>>,  
           <<2, 1>>,
           <<2, 3>>,
           <<2, 3>>,
           <<2, 3>>,
           <<2, 5>>,
           <<3, 4>>,
           <<4, 1>>,
           <<4, 5>>,
           <<4, 5>>,
           <<4, 5>>,
           <<5, 3>>,
           <<6, 5>>,
           <<6, 6>>
         >>

=============================================================================

************************** end file Tarjan.tla ******************************/

/************************* file Subexpression.tla  **********************
last modified on Fri 13 November 2009 at 14:11:05 PST by lamport
------------------------  MODULE Subexpression --------------------------- 


(***************************************************************************)
(*                        NAMING                                           *)
(*                                                                         *)
(* There are four kinds of Nameable Objects:                               *)
(*   - Expressions                                                         *)
(*   - Operators that take an argument                                     *)
(*      (and that can appear as operator arguments)                        *)
(*   - Operator definitions (named in BY/USE/HIDE statements)              *)
(*   - ASSUME/PROVEs.                                                      *)
(*                                                                         *)
(* There are three relevant kinds of primitive names that appear in a      *)
(* TLA+ module.                                                            *)
(*                                                                         *)
(*   Defined Module Name (ModuleName):                                     *)
(*      It appears to the left of "== INSTANCE...".  It may or may not     *)
(*      contain arguments.                                                 *)
(*   Primitive Operator Name (PrimOpName):                                 *)
(*      It appear to the left of the "==" in a definition, theorem         *)
(*      or assumption.  It may or may not contain arguments.               *)
(*   Label:                                                                *)
(*      It appears before a "::" in an expression.                         *)
(*                                                                         *)
(* Examples of possible primitive names are "Foo" and "Bar(x+1, 42)".      *)
(*                                                                         *)
(* The Built-In Operator names (like "SUBSET") will not be considered to   *)
(* be primitive names in the following.                                    *)
(*                                                                         *)
(* To these explicit names we add the following Operand Selector (OpSel)   *)
(* names:                                                                  *)
(*   - numbers,                                                            *)
(*   - "<<", ">>",                                                         *)
(*   - Things of the form (exp_1, ... , exp_n) where the exp_i are         *)
(*     expressions or operator arguments and n > 0.                        *)
(*   - "@",                                                                *)
(*                                                                         *)
(* A Compound Name is a sequence of primitive names, operand selectors,    *)
(* and ":"s separated by "!"s.                                             *)
(*                                                                         *)
(* In TLA+1, the general way of naming a non-built-in operator is with     *)
(* what I will call an Elementary Operator Name (ElemOpName) which has     *)
(* the following syntax.  For simplicity, I will ignore the "!"s in the    *)
(* `formal' syntax.                                                        *)
(*                                                                         *)
(*    ElemOpName ::= (ModuleName)* PrimOpName                              *)
(*                                                                         *)
(* We consider this to name both the operator and its definition (the      *)
(* expression to the right of the "==").  How the two meanings are         *)
(* disambiguated will be explained below.                                  *)
(*                                                                         *)
(* If EON is an ElemOpName and Lab_1, ...  , Lab_n are a sequence of       *)
(* label names, then EON ! Lab_1 ! ...  ! Lab_N names the expression       *)
(* labeled by Lab_N, where each Lab_(i+1) must be the name of a labeled    *)
(* expression within the expression labeled by Lab_i with no labels        *)
(* between Lab_i and Lab_(i+1).  Thus a name described by                  *)
(*                                                                         *)
(*    ElemOpName (Label)*                                                  *)
(*                                                                         *)
(* describes an operator definition or a labeled expression.  To such a    *)
(* name, we can append a sequence of OperandSelectors.  By rules           *)
(* described later, the resulting name selects a subexpression (or         *)
(* ASSUME/PROVE node) or Operator (appearing as an operator argument)      *)
(* from the body of the operator definition or labeled expression.  If     *)
(* the labeled expression is a LET/IN, then to this name can be appended   *)
(* an ElemOpName defined in the LET part, and the naming process can then  *)
(* be iterated.  The full syntax of a General Name  is:                    *)
(*                                                                         *)
(*    OperatorName ::=   ElemOpName                                        *)
(*                     | ElemOpName (Label)* ((OpSel)+ | ":") ElemOpName   *)
(*                                                                         *)
(*    GeneralName ::= OperatorName (":" | (Label)* (OpSeq)* )              *)
(*                                                                         *)
(* Note that ":" is used in two ways:                                      *)
(*                                                                         *)
(*   - An OperatorName not followed by ":" names the operator; one         *)
(*     followed by ":" names the operator's definition.                    *)
(*   - Suppose a general name GN ending in a label names a LET/IN          *)
(*     expression and EON is an ElemOpName.  Then GN !: !EON names         *)
(*     an operator defined in the LET.  The general name GN ! Foo would    *)
(*     name an expression labeled by Foo inside the IN clause.             *)
(***************************************************************************)


(***************************************************************************)
(* This +cal program describes an algorithm used in generating the         *)
(* semantic tree for a parse tree consisting of a GeneralId node or an     *)
(* OpApplication node whose first child is a GeneralId node.  Two examples *)
(* are                                                                     *)
(*                                                                         *)
(*   Foo(x)!Bar!<<!(a,b)!G                                                 *)
(*   Foo(x)!Bar!<<!(a,b)!G(c)                                              *)
(*                                                                         *)
(* We assume that these are processed to yield two sequences of nodes:     *)
(* op and args.  The sequences for the first are                           *)
(*                                                                         *)
(*   op   = << "Foo", "Bar", "<<",  "null",   "G"  >>                      *)
(*   args = << <<x>>, << >>, << >>, <<a, b>>, <<>> >>                      *)
(*                                                                         *)
(* and for the second are                                                  *)
(*                                                                         *)
(*   op   = << "Foo", "Bar", "<<",  "null",   "G"   >>                     *)
(*   args = << <<x>>, << >>, << >>, <<a, b>>, <<c>> >>                     *)
(*                                                                         *)
(* where each symbol in args represents the semantic node produced by that *)
(* symbol.                                                                 *)
(*                                                                         *)
(* The other input to the algortithm is an integer expectedArity.  There   *)
(* are three cases:                                                        *)
(*                                                                         *)
(*   expectedArity = 0 :                                                   *)
(*     The parser is expecting an expression.  This is the case            *)
(*     when the expression occurs in the first part of a USE               *)
(*     or HIDE statement.                                                  *)
(*                                                                         *)
(*   expectedArity > 0  : The parser is expecting an operator              *)
(*     argument of this arity.                                             *)
(*                                                                         *)
(*   expectedArity = -1 :                                                  *)
(*     The parser is expecting the name of a definition.  This is          *)
(*     the case when the expression occurs in the DEF clause of a USE      *)
(*     or HIDE or BY statement.                                            *)
(*                                                                         *)
(* If expectedArity # 0, then args equals a sequence each of whose         *)
(* element is the empty sequence.                                          *)
(***************************************************************************)

(***************************************************************************)
(* Note: This spec is assuming that proof-step numbers are treated like    *)
(* operator names.  That is, a step                                        *)
(*                                                                         *)
(*   <3>2. foo > bar                                                       *)
(*                                                                         *)
(* will be represented by a ThmOrAssumpDefKind node just as if it were     *)
(*                                                                         *)
(*   THEOREM <3>2 == foo > bar                                             *)
(*                                                                         *)
(* If this is not the case, then additional code needs to be added to deal *)
(* with numbered steps.  But however it is handled, the "<3>2" will be a   *)
(* name in the current symbol table.                                       *)
(***************************************************************************)

EXTENDS Integers, Sequences, TLC

(***************************************************************************)
(* SeqSeqToSeq(ss) is defined to be the concatenation of the sequences     *)
(* that are the elements of the sequence ss.                               *)
(***************************************************************************)
RECURSIVE SeqSeqToSeq(_)
SeqSeqToSeq(ss) == IF ss = << >> 
                     THEN << >>
                     ELSE Head(ss) \o SeqSeqToSeq(Tail(ss))

(***************************************************************************)
(* These are kinds of semantic nodes that can be encountered by the        *)
(* algorithm.  See tlasany/sematic/ASTConstants.java.                      *)
(***************************************************************************)
ConstantDeclKind   == "ConstantDecl"
VariableDeclKind   == "VariableDecl"
BoundSymbolKind    == "BoundSymbol"
UserDefinedOpKind  == "UserDefinedOp"
ModuleInstanceKind == "ModuleInstance"
BuiltInKind        == "BuiltIn"
OpArgKind          == "OpArg"
OpApplKind         == "OpAppl"
LetInKind          == "LetIn"
FormalParamKind    == "FormalParam"
TheoremKind        == "Theorem"
SubstInKind        == "SubstIn"
AssumeProveKind    == "AssumeProve"
ProofKind          == "Proof"
NumeralKind        == "Numeral"
DecimalKind        == "Decimal"
StringKind         == "String"
AtNodeKind         == "AtNode"
AssumeKind         == "Assume"
InstanceKind       == "Instance"
ThmOrAssumpDefKind == "ThmOrAssumpDef"
LabelKind          == "Label"
APSubstInKind      == "APSubstIn"

CONSTANT 
  NodeId,        \* The set of all node identifiers.
  Node,          \* A mapping from NodeId to nodes (which are records).
  GlobalContext, \* The initial context.
  null,          \* A special value not equal to anything else.
  debug          \* Setting to TRUE causes TLC to print a trace if the
                 \*  algorithm reports an error.

(***************************************************************************)
(*                              CONTEXTS                                   *)
(*                                                                         *)
(* A context is a mapping from names to NodeIds.  There are actually three *)
(* different kinds of mappings from names to nodes in the implementation   *)
(* that are all represented here as contexts:                              *)
(*  - The symbolTable of the Generator.                                    *)
(*  - The context field of a LetInNode                                     *)
(*  - The labels field of a LabelNode                                      *)
(***************************************************************************)
IsContext(C) == 
  (*************************************************************************)
  (* True iff C is a context.                                              *)
  (*************************************************************************)
  /\ DOMAIN C \subseteq STRING
  /\ \A str \in DOMAIN C : C[str] \in NodeId

LookUp(nm, ctxt) == 
  (*************************************************************************)
  (* The value assigned to name nm by context cxt, or null if there is no  *)
  (* value assigned.                                                       *)
  (*************************************************************************)
  IF nm \in DOMAIN ctxt THEN Node[ctxt[nm]] ELSE null

Param == [name : STRING, arity : Nat]
  (*************************************************************************)
  (* The set of parameters, which can appear in operator definitions.      *)
  (*************************************************************************)
  
(***************************************************************************)
(* For simplicity, we assume that argument numbers range from 1 to 9, and  *)
(* we define the following mappings from to and from argument numbers to   *)
(* their string representations.                                           *)
(***************************************************************************)
NumberOp == {"1", "2", "3", "4", "5", "6", "7", "8", "9"}
NumericVal(numOp) == CASE numOp = "1" -> 1 
                       [] numOp = "2" -> 2 
                       [] numOp = "3" -> 3 
                       [] numOp = "4" -> 4 
                       [] numOp = "5" -> 5 
                       [] numOp = "6" -> 6 
                       [] numOp = "7" -> 7 
                       [] numOp = "8" -> 8 
                       [] numOp = "9" -> 9

NumToString(num) ==  CASE num = 1 -> "1" 
                       [] num = 2 -> "2" 
                       [] num = 3 -> "3" 
                       [] num = 4 -> "4" 
                       [] num = 5 -> "5" 
                       [] num = 6 -> "6" 
                       [] num = 7 -> "7" 
                       [] num = 8 -> "8" 
                       [] num = 9 -> "9"

IsName(op) == 
  (*************************************************************************)
  (* A name is something other than an argument selector that can appear   *)
  (* in a compound name.                                                   *)
  (*************************************************************************)
  op \in STRING \ ({"<<", ">>", "@", ":", "null"} \cup NumberOp)

        
ArgNum(op, arity) ==
  (*************************************************************************)
  (* The argument number chosen by argument selector op for an operator    *)
  (* application with arity arguments.  It equals -1 if op is not a legal  *)
  (* argument selector for this arity.                                     *)
  (*************************************************************************)
  CASE op \in NumberOp ->
         IF NumericVal(op) <= arity THEN NumericVal(op) ELSE -1
    [] op = "<<" -> IF arity > 0 THEN 1 ELSE -1
    [] op = ">>" -> CASE arity = 1 -> 1
                      [] arity = 2 -> 2 
                      [] OTHER -> -1
    [] OTHER     -> -1

Arity(node) ==
  (*************************************************************************)
  (* The arity of a node--that is, the number of arguments it takes.       *)
  (*************************************************************************)
  IF node.kind \in {UserDefinedOpKind, BuiltInKind, ModuleInstanceKind,
                    ThmOrAssumpDefKind, OpArgKind, LabelKind, 
                    ConstantDeclKind, FormalParamKind}
    THEN node.arity
    ELSE 0

ParamArity(node, i) ==
  (*************************************************************************)
  (* The arity of the i-th parameter of the node of kind                   *)
  (* UserDefinedOpKind, ThmOrAssumpDefKind, ModuleInstanceKind,            *)
  (* ConstantDeclKind, or FormalParamKind                                  *)
  (*************************************************************************)
  IF node.kind \in {ConstantDeclKind, FormalParamKind}
    THEN 0
    ELSE node.params[i].arity
-----------------------------------------------------------------------------

(***************************************************************************)
(* The following assumptions define the data types--in particular, the     *)
(* record components that each node type must contain.                     *)
(***************************************************************************)
ASSUME IsContext(GlobalContext) 

ASSUME DOMAIN Node = NodeId

ASSUME
/\ \A id \in NodeId :
    LET node == Node[id] IN  
    /\ node.kind \in 
            {ConstantDeclKind, VariableDeclKind, BoundSymbolKind,
             UserDefinedOpKind, ModuleInstanceKind, BuiltInKind,
             OpArgKind, OpApplKind, LetInKind, FormalParamKind,
             TheoremKind, SubstInKind, AssumeProveKind, ProofKind,
             NumeralKind, DecimalKind, StringKind, AtNodeKind,
             AssumeKind, InstanceKind, ThmOrAssumpDefKind, LabelKind,
             APSubstInKind}

ASSUME
/\ \A id \in NodeId :
    LET node == Node[id] IN  
    /\ node.kind \in {UserDefinedOpKind, BuiltInKind, ModuleInstanceKind, 
                      ThmOrAssumpDefKind, LabelKind, ConstantDeclKind, 
                      FormalParamKind}
        => /\ node.name \in STRING
           /\ node.arity \in Nat \cup {-1}
           /\ (node.arity = -1) => (node.kind = BuiltInKind)

ASSUME
 \A id \in NodeId :
    LET node == Node[id] IN  
       node.kind \in {UserDefinedOpKind, ThmOrAssumpDefKind}  => 
         /\ node.body \in NodeId 
         /\ IsContext(node.labels)
         /\ node.params \in Seq(Param)
         /\ Len(node.params) = node.arity
         /\ node.defined \in BOOLEAN 
         /\ node.source \in {null} \cup NodeId
            \* The original definition (before instantiation)
            \* or null if this is it.

ASSUME
 \A id \in NodeId :
    LET node == Node[id] IN  
    /\ node.kind = OpApplKind =>
        /\ node.operands \in Seq(NodeId)
        /\ node.operator \in NodeId
        /\ node.unboundedBoundSymbols \in Seq(STRING)
        /\ node.boundedBoundSymbols \in Seq(Seq(STRING))
             (**************************************************************)
             (* These are actually arrays and arrays of arrays of          *)
             (* FormalParamNode objects (formerly OpDeclNode objects).     *)
             (**************************************************************)
        /\ node.ranges \in Seq(NodeId)
        /\ Len(node.ranges) = Len(node.boundedBoundSymbols)

ASSUME
 \A id \in NodeId :
    LET node == Node[id] IN  
    /\ node.kind = LetInKind =>
        /\ node.body \in NodeId
        /\ IsContext(node.context)

ASSUME
 \A id \in NodeId :
    LET node == Node[id] IN  
    /\ node.kind = OpArgKind =>
        /\ node.op \in NodeId
        /\ IsName(node.name)
        /\ (node.arity \in Nat) /\ (node.arity > 0)
        
ASSUME
 \A id \in NodeId :
    LET node == Node[id] IN  
    /\ node.kind = LabelKind =>
         /\ node.body \in NodeId 
         /\ IsContext(node.labels)
         /\ node.params \in Seq(Param)

ASSUME
 \A id \in NodeId :
    LET node == Node[id] IN  
    /\ node.kind = SubstInKind =>
         /\ node.body \in NodeId 
         /\ node.subst \in STRING \* Just to identify it.

ASSUME
 \A id \in NodeId :
    LET node == Node[id] IN  
    /\ node.kind = AssumeProveKind =>
         /\ node.assumes\in Seq(NodeId)
         /\ node.prove \in NodeId

    
RECURSIVE ExpandNode(_)
ExpandNode(node) ==
  CASE node.kind \in {UserDefinedOpKind, LetInKind} ->
        [node EXCEPT !.body = ExpandNode(Node[@])]
  []   node.kind = OpApplKind ->
        [node EXCEPT 
          !.operands = [i \in DOMAIN @ |-> ExpandNode(Node[@[i]])],
          !.operator = ExpandNode(Node[@]),
          !.ranges   = [i \in DOMAIN @ |-> ExpandNode(Node[@[i]])]]
  []   OTHER -> node


-----------------------------------------------------------------------------
(***************************************************************************)
(* Test Data                                                               *)
(*                                                                         *)
(* The algorithm has been tested on the following sets of data, where each *)
(* operator MCxxx is either substituted for constant parameter xxx or is   *)
(* used as initial value of the algorithm's input variable xxx.            *)
(***************************************************************************)


(*****************************


(***************************************************************************)
(* ------------------------ MODULE M ------------------------              *)
(* CONSTANT C                                                              *)
(* Op(Arg(_), p) == \A x \in {1,2}, <<y, z>> \in {3} :                     *)
(*                      lab(x,y,z) :: LET a + b == <<Arg(a), b>>           *)
(*                                    IN  1 + label2 :: p + C              *)
(* Foo(u) == "FooBody(u)"                                                  *)
(* =============================================================           *)
(*                                                                         *)
(* Inst(d) == INSTANCE M WITH C <- "expr(d)"                               *)
(***************************************************************************)

\* MCNode == 
\*  1 :> [kind     |-> UserDefinedOpKind,          \*  Op(Arg(_), p) == ...
\*        name     |-> "Op",
\*        body     |-> 3,
\*        labels   |->  "lab" :> 4,
\*        arity    |-> 2,
\*        params   |-> <<[name |-> "Arg",  arity |-> 1],
\*                       [name |-> "p",    arity |-> 0]>>,
\*        defined  |-> TRUE,
\*        source   |-> null   ]
\* @@
\*  2 :> [kind  |-> BuiltInKind,             
\*         name  |-> "$BoundedForall", 
\*         arity |-> -1
\*        ]
\* @@
\*  3 :> [kind     |-> OpApplKind,            \* \A x \in {1,2}, <<y, z>> \in {3} : ...
\*        operands |-> << 4 >>,   
\*        operator |-> 2,
\*        unboundedBoundSymbols |-> <<>>,
\*        boundedBoundSymbols |-> << <<"x">>, <<"y", "z">> >>,
\*        ranges |-> << 19, 21 >>]
\* @@
\*  4 :> [kind     |-> LabelKind,                    \* lab(x,y,z) :: LET a + b == <<Arg(a), b>>
\*        name     |-> "lab",                        \*               IN  1 + label2 :: p + C
\*        body     |-> 5,
\*        arity    |-> 3,
\*        params   |-> <<[name |-> "x", arity |->0], 
\*                       [name |-> "y", arity |->0], 
\*                       [name |-> "z", arity |->0] >>,
\*        labels   |-> "label2" :> 15      ]
\* @@
\*  5 :>  [kind    |-> LetInKind,     \*  LET a + b == <<Arg(a), b>>
\*         context |-> "+" :> 6,      \*  IN  1 + label2 :: p + C
\*         body    |->  13 ]
\* @@
\*  6 :> [kind     |-> UserDefinedOpKind,    \* a + b == <<Arg(a), b>>
\*        name     |-> "+",
\*        body     |-> 7,
\*        labels   |->  << >>,
\*        arity    |-> 2,
\*        params   |-> <<[name |-> "a",  arity |-> 0],
\*                       [name |-> "b",  arity |-> 0]>>,
\*        defined  |-> TRUE,
\*        source   |-> null   ]
\* @@
\*  7 :> [kind     |-> OpApplKind,            \* <<Arg(a), b>>
\*        operands |-> << 9, 12 >>,   
\*        operator |-> 8,
\*        unboundedBoundSymbols |-> <<>>,
\*        boundedBoundSymbols |-> << >>,
\*        ranges |-> << >>]
\* @@
\*  8 :> [kind  |-> BuiltInKind,
\*        name  |-> "$Tuple", 
\*        arity |-> -1
\*       ]
\* @@
\*  9 :> [kind     |-> OpApplKind,            \* Arg(a)
\*        operands |-> <<11 >>,   
\*        operator |-> 10,
\*        unboundedBoundSymbols |-> <<>>,
\*        boundedBoundSymbols |-> << >>,
\*        ranges |-> << >>]
\* @@
\* 10 :> [kind  |-> FormalParamKind,
\*        name  |-> "Arg",  
\*        arity |-> 1]
\* 
\* @@
\* 11 :> [kind  |-> FormalParamKind,
\*        name  |-> "a",  
\*        arity |-> 0]
\* @@
\* 12 :> [kind  |-> FormalParamKind,
\*        name  |-> "b",  
\*        arity |-> 0]
\* @@
\* 13 :> [kind     |-> OpApplKind,            \* 1 + label2 :: p + C
\*        operands |-> <<14, 15>>,   
\*        operator |-> 6,
\*        unboundedBoundSymbols |-> <<>>,
\*        boundedBoundSymbols |-> << >>,
\*        ranges |-> << >>]
\* @@
\* 14 :> [kind |-> NumeralKind,
\*        val  |-> 1]
\* @@
\* 15 :> [kind     |-> LabelKind,                    \* label2 :: p + C
\*        name     |-> "label2",                        
\*        body     |-> 16,
\*        arity    |-> 0,
\*        params   |-> <<>>,
\*        labels   |-> << >>]
\* @@
\* 16 :> [kind     |-> OpApplKind,            \* p + C
\*        operands |-> <<17, 18>>,   
\*        operator |-> 6,
\*        unboundedBoundSymbols |-> <<>>,
\*        boundedBoundSymbols |-> << >>,
\*        ranges |-> << >>]
\* @@
\* 17 :> [kind  |-> FormalParamKind,
\*        name  |-> "p",  
\*        arity |-> 0]
\* @@
\* 18 :> [kind  |-> ConstantDeclKind,
\*        name  |-> "C",
\*        arity |-> 0  ]
\* @@
\* 19 :> [kind     |-> OpApplKind,            \* {1,2}
\*        operands |-> << 14, 20 >>,   
\*        operator |-> 8,                     \* Actually, specifying <<1, 2>>
\*        unboundedBoundSymbols |-> << >>,
\*        boundedBoundSymbols |-> << >>,
\*        ranges |-> << >>]
\* @@
\* 20 :> [kind |-> NumeralKind,
\*        val  |-> 2]
\* @@
\* 21 :> [kind     |-> OpApplKind,            \* {1,2}
\*        operands |-> << 22>>,   
\*        operator |-> 8,                     \* Actually, specifying <<1, 2>>
\*        unboundedBoundSymbols |-> << >>,
\*        boundedBoundSymbols |-> << >>,
\*        ranges |-> << >>]
\* @@
\* 22 :> [kind |-> NumeralKind,
\*        val  |-> 3]
\* @@
\* 23 :> [kind     |-> UserDefinedOpKind,          \*  Foo(u) == "FooBody(u)"
\*        name     |-> "Foo",
\*        body     |-> 24,
\*        labels   |-> << >>,
\*        arity    |-> 1,
\*        params   |-> <<[name |-> "u",  arity |-> 0]>>,
\*        defined  |-> TRUE,
\*        source   |-> null   ]
\* @@
\* 24 :> [kind |-> StringKind,
\*        val  |-> "FooBody(u)"]
\* @@
\* 25 :> [kind |-> StringKind,
\*        val  |-> "string"]
\* @@
\* 26 :> [kind     |-> ModuleInstanceKind,    \* Inst(d) == INSTANCE M WITH C <- "expr(d)"
\*        name     |-> "Inst",
\*        arity    |-> 1,
\*        params   |-> <<[name |-> "d", arity |-> 0] >>,
\*        defined  |-> TRUE   ]
\* @@
\* 27 :> [kind  |-> SubstInKind,
\*        body  |-> 24,
\*        subst |-> "expr(d)"]
\* @@
\* 28 :> [kind     |-> UserDefinedOpKind,          \*  Foo(u) == "FooBody(u)"
\*        name     |-> "Inst!Foo",
\*        body     |-> 27,
\*        labels   |-> << >>,
\*        arity    |-> 2,
\*        params   |-> << [name |-> "d", arity |-> 0],
\*                        [name |-> "u",  arity |-> 0]>>,
\*        defined  |-> TRUE,
\*        source   |-> 23 ]
\* @@
\* 29 :> [kind     |-> UserDefinedOpKind,          \*  Op(Arg(_), p) == ...
\*        name     |-> "Inst!Op",
\*        body     |-> 30,
\*        labels   |-> "lab" :> 4,
\*        arity    |-> 3,
\*        params   |-> <<[name |-> "d", arity |-> 0],
\*                       [name |-> "Arg",  arity |-> 1],
\*                       [name |-> "p",    arity |-> 0]>>,
\*        defined  |-> TRUE,
\*        source   |-> 1   ]
\* @@
\* 30 :> [kind  |-> SubstInKind,
\*        body  |-> 3,
\*        subst |-> "expr(d)"]
\* @@
\* 31 :> [kind |-> StringKind,
\*        val  |-> "Argm"]
\* 
\* MCNodeId == 1..31
\* 
\* MCGlobalContext ==
\*   "Op" :> 1
\* @@
\*   "Foo" :> 23
\* @@
\*   "Inst" :> 26
\* @@
\*   "Inst!Foo" :> 28
\* @@
\*   "Inst!Op" :> 29
\* 
\* \* Foo("string")
\* \* MCops == <<"Foo">> 
\* \* MCargs ==   << <<25>>>>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")
\* \* MCops == <<"Op">> 
\* \* MCargs ==   << <<23, 25>> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")!lab(1,2,3)
\* \* MCops == <<"Op", "lab">> 
\* \* MCargs ==   << <<23, 25>> , <<14, 20, 22  >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")!lab(1,2,3)!<<
\* \* MCops == <<"Op", "lab", "<<">> 
\* \* MCargs ==   << <<23, 25>> , <<14, 20, 22>> , << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")!lab(1,2,3)!<<!>>
\* \* MCops == <<"Op", "lab", "<<", ">>">> 
\* \* MCargs ==   << <<23, 25>> , <<14, 20, 22>> , << >>, << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")!lab(1,2,3)!label2
\* \* MCops == <<"Op", "lab", "label2">> 
\* \* MCargs ==   << <<23, 25>> , <<14, 20, 22>> , << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")!lab(1,2,3)!label2!<<
\* \* MCops == <<"Op", "lab", "label2", "<<">> 
\* \* MCargs ==   << <<23, 25>> , <<14, 20, 22>> , << >>, << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")!lab(1,2,3)!:!+(3,2)
\* \* MCops == <<"Op", "lab", ":", "+" >>
\* \* MCargs ==   << <<23, 25>> , <<14, 20, 22>> , << >> , <<22, 20 >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")!lab(1,2,3)!:!+(3,2)!>>
\* \* MCops == <<"Op", "lab", ":", "+", ">>" >>
\* \* MCargs ==   << <<23, 25>> , <<14, 20, 22>> , << >> , <<22, 20 >>, << >>  >>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")!(1,2,3)
\* \* MCops == <<"Op", "null" >>
\* \* MCargs ==   << <<23, 25>> , <<14, 20, 22>> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")!(1,2,3)!>>!>>!<<
\* \* MCops == <<"Op", "null", ">>", ">>", "<<" >>
\* \* MCargs ==   << <<23, 25>> , <<14, 20, 22>>, << >>, << >>,  << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Op(Foo, "string")!<<!>>
\* \* MCops == <<"Op", "<<", ">>" >>
\* \* MCargs ==   << <<23, 25>>,  << >>, << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Foo("string")
\* \* MCops == <<"Inst", "Foo">> 
\* \* MCargs ==   << <<31>>, <<25>>>>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")
\* \* MCops == <<"Inst", "Op">> 
\* \* MCargs ==   << <<31>>, <<23, 25>> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")!lab(1,2,3)
\* \* MCops == <<"Inst", "Op", "lab">> 
\* \* MCargs ==   << <<31>>, <<23, 25>> , <<14, 20, 22  >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")!lab(1,2,3)!<<
\* \* MCops == <<"Inst", "Op", "lab", "<<">> 
\* \* MCargs ==   << <<31>>, <<23, 25>> , <<14, 20, 22>> , << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")!lab(1,2,3)!<<!>>
\* \* MCops == <<"Inst", "Op", "lab", "<<", ">>">> 
\* \* MCargs ==   << <<31>>, <<23, 25>> , <<14, 20, 22>> , << >>, << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")!lab(1,2,3)!label2
\* \* MCops == <<"Inst", "Op", "lab", "label2">> 
\* \* MCargs ==   << <<31>>, <<23, 25>> , <<14, 20, 22>> , << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")!lab(1,2,3)!label2!<<
\* \* MCops == <<"Inst", "Op", "lab", "label2", "<<">> 
\* \* MCargs ==   << <<31>>, <<23, 25>> , <<14, 20, 22>> , << >>, << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")!lab(1,2,3)!:!+(3,2)
\* \* MCops == <<"Inst", "Op", "lab", ":", "+" >>
\* \* MCargs ==   << <<31>>, <<23, 25>> , <<14, 20, 22>> , << >> , <<22, 20 >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")!lab(1,2,3)!:!+(3,2)!>>
\* \* MCops == <<"Inst", "Op", "lab", ":", "+", ">>" >>
\* \* MCargs ==   << <<31>>, <<23, 25>> , <<14, 20, 22>> , << >> , <<22, 20 >>, << >>  >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")!(1,2,3)
\* \* MCops == <<"Inst", "Op", "null" >>
\* \* MCargs ==   << <<31>>, <<23, 25>> , <<14, 20, 22>> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")!(1,2,3)!>>!>>!<<
\* \* MCops == <<"Inst", "Op", "null", ">>", ">>", "<<" >>
\* \* MCargs ==   << <<31>>, <<23, 25>> , <<14, 20, 22>>, << >>, << >>,  << >> >>
\* \* MCexpectedArity == 0 
\* 
\* \* Inst("Argm")!Op(Foo, "string")!<<!>>
\* \* MCops == <<"Inst", "Op", "<<", ">>" >>
\* \* MCargs ==   << <<31>>, <<23, 25>>,  << >>, << >> >>
\* \* MCexpectedArity == 0 

*****************************************)

(***************************************************************************)
(* ------------------------ MODULE M ------------------------              *)
(* CONSTANT C, Arg1(_)                                                     *)
(* Op(Arg, p) == \A x \in {1,2}, <<y, z>> \in {3} :                        *)
(*                      lab(x,y,z) :: LET a + b == <<Arg1(a), b>>          *)
(*                                    IN  1 + label2 :: p + C              *)
(* Bar(AOp(_)) == AOp(1)                                                   *)
(* Foo(u) == Bar(Arg1)                                                     *)
(* Foo2 == Bar(LAMBDA m, n : <<m, n>>)                                     *)
(* THEOREM Thm == ASSUME Arg1(1) , Bar(Arg1) PROVE << C, Bar(Arg1)>>       *)
(* UU == lab:: C                                                           *)
(* =============================================================           *)
(*                                                                         *)
(* Foo3 == \A x : LET Bar3 == 1 IN 2                                       *)
(* Inst(d) == INSTANCE M WITH C <- "expr(d)"                               *)
(***************************************************************************)


MCNode == 
 1 :> [kind     |-> UserDefinedOpKind,          \*  Op(Arg, p) == ...
       name     |-> "Op",
       body     |-> 3,
       labels   |->  "lab" :> 4,
       arity    |-> 2,
       params   |-> <<[name |-> "Arg",  arity |-> 0],
                      [name |-> "p",    arity |-> 0]>>,
       defined  |-> TRUE,
       source   |-> null   ]
@@
 2 :> [kind  |-> BuiltInKind,             
        name  |-> "$BoundedForall", 
        arity |-> -1
       ]
@@
 3 :> [kind     |-> OpApplKind,            \* \A x \in {1,2}, <<y, z>> \in {3} : ...
       operands |-> << 4 >>,   
       operator |-> 2,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << <<"x">>, <<"y", "z">> >>,
       ranges |-> << 19, 21 >>]
@@
 4 :> [kind     |-> LabelKind,                    \* lab(x,y,z) :: LET a + b == <<Arg(a), b>>
       name     |-> "lab",                        \*               IN  1 + label2 :: p + C
       body     |-> 5,
       arity    |-> 3,
       params   |-> <<[name |-> "x", arity |->0], 
                      [name |-> "y", arity |->0], 
                      [name |-> "z", arity |->0] >>,
       labels   |-> "label2" :> 15      ]
@@
 5 :>  [kind    |-> LetInKind,     \*  LET a + b == <<Arg(a), b>>
        context |-> "+" :> 6,      \*  IN  1 + label2 :: p + C
        body    |->  13 ]
@@
 6 :> [kind     |-> UserDefinedOpKind,    \* a + b == <<Arg(a), b>>
       name     |-> "+",
       body     |-> 7,
       labels   |->  << >>,
       arity    |-> 2,
       params   |-> <<[name |-> "a",  arity |-> 0],
                      [name |-> "b",  arity |-> 0]>>,
       defined  |-> TRUE,
       source   |-> null   ]
@@
 7 :> [kind     |-> OpApplKind,            \* <<Arg(a), b>>
       operands |-> << 9, 12 >>,   
       operator |-> 8,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
 8 :> [kind  |-> BuiltInKind,
       name  |-> "$Tuple", 
       arity |-> -1
      ]
@@
 9 :> [kind     |-> OpApplKind,            \* Arg1(a)
       operands |-> <<11 >>,   
       operator |-> 10,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
10 :> [kind  |-> ConstantDeclKind,
       name  |-> "Arg1",  
       arity |-> 1]

@@
11 :> [kind  |-> FormalParamKind,
       name  |-> "a",  
       arity |-> 0]
@@
12 :> [kind  |-> FormalParamKind,
       name  |-> "b",  
       arity |-> 0]
@@
13 :> [kind     |-> OpApplKind,            \* 1 + label2 :: p + C
       operands |-> <<14, 15>>,   
       operator |-> 6,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
14 :> [kind |-> NumeralKind,
       val  |-> 1]
@@
15 :> [kind     |-> LabelKind,                    \* label2 :: p + C
       name     |-> "label2",                        
       body     |-> 16,
       arity    |-> 0,
       params   |-> <<>>,
       labels   |-> << >>]
@@
16 :> [kind     |-> OpApplKind,            \* p + C
       operands |-> <<17, 18>>,   
       operator |-> 6,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
17 :> [kind  |-> FormalParamKind,
       name  |-> "p",  
       arity |-> 0]
@@
18 :> [kind  |-> ConstantDeclKind,
       name  |-> "C",
       arity |-> 0  ]
@@
19 :> [kind     |-> OpApplKind,            \* {1,2}
       operands |-> << 14, 20 >>,   
       operator |-> 8,                     \* Actually, specifying <<1, 2>>
       unboundedBoundSymbols |-> << >>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
20 :> [kind |-> NumeralKind,
       val  |-> 2]
@@
21 :> [kind     |-> OpApplKind,            \* {1,2}
       operands |-> << 22>>,   
       operator |-> 8,                     \* Actually, specifying <<1, 2>>
       unboundedBoundSymbols |-> << >>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
22 :> [kind |-> NumeralKind,
       val  |-> 3]
@@
23 :> [kind     |-> UserDefinedOpKind,          \*  Foo(u) == Bar(Arg1)
       name     |-> "Foo",
       body     |-> 24,
       labels   |-> << >>,
       arity    |-> 1,
       params   |-> <<[name |-> "u",  arity |-> 0]>>,
       defined  |-> TRUE,
       source   |-> null   ]
@@
24 :> [kind     |-> OpApplKind,            \* Bar(Arg1)
       operands |-> <<34>>,
       operator |-> 32,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
25 :> [kind |-> StringKind,
       val  |-> "string"]
@@
26 :> [kind     |-> ModuleInstanceKind,    \* Inst(d) == INSTANCE M WITH C <- "expr(d)"
       name     |-> "Inst",
       arity    |-> 1,
       params   |-> <<[name |-> "d", arity |-> 0] >>,
       defined  |-> TRUE   ]
@@
27 :> [kind  |-> SubstInKind,
       body  |-> 24,
       subst |-> "expr(d)"]
@@
28 :> [kind     |-> UserDefinedOpKind,          \*  Foo(u) == "FooBody(u)"
       name     |-> "Inst!Foo",
       body     |-> 27,
       labels   |-> << >>,
       arity    |-> 2,
       params   |-> << [name |-> "d", arity |-> 0],
                       [name |-> "u",  arity |-> 0]>>,
       defined  |-> TRUE,
       source   |-> 23 ]
@@
29 :> [kind     |-> UserDefinedOpKind,          \*  Op(Arg, p) == ...
       name     |-> "Inst!Op",
       body     |-> 30,
       labels   |-> "lab" :> 4,
       arity    |-> 3,
       params   |-> <<[name |-> "d", arity |-> 0],
                      [name |-> "Arg",  arity |-> 0],
                      [name |-> "p",    arity |-> 0]>>,
       defined  |-> TRUE,
       source   |-> 1   ]
@@
30 :> [kind  |-> SubstInKind,
       body  |-> 3,
       subst |-> "expr(d)"]
@@
31 :> [kind |-> StringKind,
       val  |-> "Argm"]
@@
32 :> [kind     |-> UserDefinedOpKind,          \*  Bar(AOp(_)) == AOp(1)
       name     |-> "Bar",
       body     |-> 33,
       labels   |-> << >>,
       arity    |-> 1,
       params   |-> <<[name |-> "AOp",  arity |-> 1]>>,
       defined  |-> TRUE,
       source   |-> null   ]
@@
33 :> [kind     |-> OpApplKind,            \* Arg1(1)
       operands |-> <<14>>,
       operator |-> 10,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
34 :> [kind  |-> OpArgKind,
       op    |-> 10,
       arity |-> 1,
       name  |-> "Arg1"]
@@ 
35 :> [kind     |-> UserDefinedOpKind,          \*  Foo2 == Bar(LAMBDA m, n : <<m, n>>)   
       name     |-> "Foo2",
       body     |-> 36,
       labels   |-> << >>,
       arity    |-> 0,
       params   |-> <<>>,
       defined  |-> TRUE,
       source   |-> null   ]
@@
36 :> [kind     |-> OpApplKind,            \* Bar(LAMBDA m, n : <<m, n>>)
       operands |-> <<41>>,
       operator |-> 32,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
37 :> [kind     |-> UserDefinedOpKind,          \* LAMBDA m, n : <<m, n>>
       name     |-> "LAMBDA",
       body     |-> 38,
       labels   |->  << >>,
       arity    |-> 2,
       params   |-> <<[name |-> "m",  arity |-> 0],
                      [name |-> "n",    arity |-> 0]>>,
       defined  |-> TRUE,
       source   |-> null   ]
@@
38 :> [kind     |-> OpApplKind,            \* <<m, n>>
       operands |-> << 39, 40 >>,   
       operator |-> 8,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
39 :> [kind  |-> FormalParamKind,
       name  |-> "m",  
       arity |-> 0]
@@
40 :> [kind  |-> FormalParamKind,
       name  |-> "n",  
       arity |-> 0]
@@
41 :> [kind  |-> OpArgKind,  \* LAMBDA m, n : <<m, n>>
       op    |-> 37,
       arity |-> 2,
       name  |-> "LAMBDA"]
@@ 
42 :> [kind     |-> UserDefinedOpKind,          \*  Inst!Foo2 == Bar(LAMBDA m, n : <<m, n>>)   
       name     |-> "Inst!Foo2",
       body     |-> 43,
       labels   |-> << >>,
       arity    |-> 1,
       params   |-> <<[name |-> "d", arity |-> 0]>>,
       defined  |-> TRUE,
       source   |-> 35    ]
@@
43 :> [kind  |-> SubstInKind,
       body  |-> 36,
       subst |-> "expr(d)"]
@@ 
44 :> [kind     |-> ThmOrAssumpDefKind, \*  Thm == ASSUME Arg1(1) ...
       name     |-> "Thm",
       body     |-> 45,
       labels   |-> << >>,
       arity    |-> 0,
       params   |-> << >> ,
       defined  |-> TRUE,
       source   |-> null   ]
@@
45 :> [kind    |-> AssumeProveKind,
       assumes |-> <<33, 24>>,
       prove   |-> 46 ]
@@
46 :> [kind     |-> OpApplKind,            \* <<c, Bar(Arg1)>>
       operands |-> << 59, 24 >>,   
       operator |-> 8,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@ 
47 :> [kind     |-> ThmOrAssumpDefKind,   \*  Thm == ASSUME Arg1(1) ...
       name     |-> "Inst!Thm",
       body     |-> 48,
       labels   |-> << >>,
       arity    |-> 1,
       params   |-> << [name |-> "d", arity |-> 0]>> ,
       defined  |-> TRUE,
       source   |-> 44   ]
@@
48 :> [kind  |-> SubstInKind,
       body  |-> 45,
       subst |-> "expr(d)"]
@@ 
49 :> [kind     |-> UserDefinedOpKind,     \* Foo3 == \A x : LET ...
       name     |-> "Foo3",
       body     |-> 51,
       labels   |-> << >>,
       arity    |-> 0,
       params   |-> <<>>,
       defined  |-> TRUE,
       source   |-> null   ]
@@
50 :>  [kind    |-> LetInKind,        \*  Foo3 == \A x : LET Bar3 == 1 IN 2
        context |-> "Bar3" :> 53,     
        body    |->  13 ]
@@
51 :> [kind     |-> OpApplKind,       \* \A x : LET Bar3 == 1 IN 2
       operands |-> << 50 >>,   
       operator |-> 52,
       unboundedBoundSymbols |-> <<"x">>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
52 :> [kind  |-> BuiltInKind,             \* \A x :
       name  |-> "$UnboundedForall", 
       arity |-> -1]
@@
53 :> [kind     |-> UserDefinedOpKind,          \* Bar3 == 1
       name     |-> "Bar3",
       body     |-> 14,
       labels   |->  << >>,
       arity    |-> 0,
       params   |-> <<>>,
       defined  |-> TRUE,
       source   |-> null   ]
@@
54 :> [kind     |-> FormalParamKind,          \* AOp
       name     |-> "AOp",  
       arity    |-> 1]
@@
55 :> [kind     |-> UserDefinedOpKind,          \*  Bar(AOp(_)) == AOp(1)
       name     |-> "Inst!Bar",
       body     |-> 56,
       labels   |-> << >>,
       arity    |-> 2,
       params   |-> <<[name |-> "d", arity |-> 0],
                      [name |-> "AOp",  arity |-> 1]>>,
       defined  |-> TRUE,
       source   |-> null   ]
@@
56 :> [kind  |-> SubstInKind,
       body  |-> 33,
       subst |-> "expr(d)"]
@@
57 :> [kind     |-> UserDefinedOpKind,    \* UU == lab:: C 
       name     |-> "UU",
       body     |-> 58,
       labels   |->  "lab":> 58,
       arity    |-> 0,
       params   |-> <<>>,
       defined  |-> TRUE,
       source   |-> null   ]
@@
58 :> [kind     |-> LabelKind,                    \* lab :: C
       name     |-> "lab",                        
       body     |-> 59,
       arity    |-> 0,
       params   |-> <<>>,
       labels   |-> << >>]

@@
59 :> [kind     |-> OpApplKind,       \* C
       operands |-> <<>>,   
       operator |-> 18,
       unboundedBoundSymbols |-> <<>>,
       boundedBoundSymbols |-> << >>,
       ranges |-> << >>]
@@
60 :> [kind     |-> UserDefinedOpKind,    \* UU == lab:: C 
       name     |-> "Inst!UU",
       body     |-> 58,
       labels   |->  "lab":> 58,
       arity    |-> 1,
       params   |-> <<[name |-> "d", arity |-> 0] >>,
       defined  |-> TRUE,
       source   |-> null   ]


  MCNodeId == 1..60

MCGlobalContext ==
  "Op" :> 1
@@
  "C" :> 18
@@
  "UU" :> 57
@@
  "Foo" :> 23
@@
  "Inst" :> 26
@@
  "Inst!Foo" :> 28
@@
  "Inst!Bar" :> 55
@@
  "Inst!Op" :> 29
@@
  "Inst!UU" :> 60
@@
  "Foo2" :> 35
@@
  "Inst!Foo2" :> 42
@@ 
  "Thm" :> 44
@@ 
  "Inst!Thm" :> 47
@@
  "Foo3" :> 49
@@
  "Bar" :> 32
@@
  "Arg1" :> 10
@@
  "AOp" :> 54
@@
  "p" :> 17

\* Foo
\* MCops == <<"Foo">> 
\* MCargs ==   << << >> >>
\* MCexpectedArity == 1

\* Op()
\* MCops == <<"Op">> 
\* MCargs ==   << <<>> >>
\* MCexpectedArity == 2

\* Op!lab
\* MCops == <<"Op", "lab">> 
\* MCargs ==   << <<>> , <<>> >>
\* MCexpectedArity == 5

\* Op!lab!<<
\* MCops == <<"Op", "lab", "<<">> 
\* MCargs ==   << <<>> , <<>> , << >> >>
\* MCexpectedArity == 5

\* Op!lab!<<!>>
\* MCops == <<"Op", "lab", "<<", ">>">> 
\* MCargs ==   << << >> , << >> , << >>, << >> >>
\* MCexpectedArity == 5 

\* Op!lab!label2
\* MCops == <<"Op", "lab", "label2">> 
\* MCargs ==   << << >> , << >> , << >> >>
\* MCexpectedArity == 5 

\* Op!lab!label2!<<
\* MCops == <<"Op", "lab", "label2", "<<">> 
\* MCargs ==   << << >> , << >> , << >>, << >> >>
\* MCexpectedArity == 5

\* Op!lab!:!+
\* MCops == <<"Op", "lab", ":", "+" >>
\* MCargs ==   << << >> , << >> , << >> , << >> >>
\* MCexpectedArity == 7 

\* Op!lab!:!+
\* MCops == <<"Op", "lab", ":", "+", ">>" >>
\* MCargs ==   << << >> , << >> , << >> , << >>, << >>  >>
\* MCexpectedArity == 7

\* Op!@
\* MCops == <<"Op", "@" >>
\* MCargs ==   << << >> , << >> >>
\* MCexpectedArity == 5 

\* Op!@!>>!>>!<<
\* MCops == <<"Op", "@", ">>", ">>", "<<" >>
\* MCargs ==   << << >> , << >>, << >>, << >>,  << >> >>
\* MCexpectedArity == 5 

\* Op!<<!>>
\* MCops == <<"Op", "<<", ">>" >>
\* MCargs ==   << << >>,  << >>, << >> >>
\* MCexpectedArity == 2 

\* Inst!Foo
\* MCops == <<"Inst", "Foo">> 
\* MCargs ==   << << >>, << >> >>
\* MCexpectedArity == 2 

\* Inst!Op
\* MCops == <<"Inst", "Op">> 
\* MCargs ==   << << >>, << >> >>
\* MCexpectedArity == 3 

\* Inst!Op!lab
\* MCops == <<"Inst", "Op", "lab">> 
\* MCargs ==   << << >>, << >> , << >> >>
\* MCexpectedArity == 6

\* Inst!Op!lab!<<
\* MCops == <<"Inst", "Op", "lab", "<<">> 
\* MCargs ==   << << >>, << >> , << >> , << >> >>
\* MCexpectedArity == 6

\* Inst!Op!lab!<<!>>
\* MCops == <<"Inst", "Op", "lab", "<<", ">>">> 
\* MCargs ==   << << >>, << >> , << >> , << >>, << >> >>
\* MCexpectedArity == 6 

\* Inst!Op!lab!label2
\* MCops == <<"Inst", "Op", "lab", "label2">> 
\* MCargs ==   << << >>, << >> , << >> , << >> >>
\* MCexpectedArity == 6

\* Inst!Op!lab!label2!<<
\* MCops == <<"Inst", "Op", "lab", "label2", "<<">> 
\* MCargs ==   << << >>, << >> , << >> , << >>, << >> >>
\* MCexpectedArity == 6

\* Inst!Op!lab!:!+
\* MCops == <<"Inst", "Op", "lab", ":", "+" >>
\* MCargs ==   << << >>, << >> , << >> , << >> , << >> >>
\* MCexpectedArity == 8 

\* Inst!Op!lab!:!+!>>
\* MCops == <<"Inst", "Op", "lab", ":", "+", ">>" >>
\* MCargs ==   << << >>, << >> , << >> , << >> , << >>, << >>  >>
\* MCexpectedArity == 8 

\* Inst!Op!@
\* MCops == <<"Inst", "Op", "@" >>
\* MCargs ==   << << >>, << >> , << >> >>
\* MCexpectedArity == 6 

\* Inst!Op!@!>>!>>!<<
\* MCops == <<"Inst", "Op", "@", ">>", ">>", "<<" >>
\* MCargs ==   << << >>, << >> , << >>, << >>, << >>,  << >> >>
\* MCexpectedArity == 6

\* Inst!Op!<<!>>
\* MCops == <<"Inst", "Op", "<<", ">>" >>
\* MCargs ==   << << >>, << >>,  << >>, << >> >>
\* MCexpectedArity == 3 

\* Foo!1
\* MCops == <<"Foo", "1">>
\* MCargs ==   << << >>, << >> >>
\* MCexpectedArity == 2

\* Inst!Foo!1
\* MCops == <<"Inst", "Foo", "1">>
\* MCargs ==   << << >>, << >>, << >> >>
\* MCexpectedArity == 3

\* Foo2!1
\* MCops == <<"Foo2", "1">>
\* MCargs ==   << << >>, << >> >>
\* MCexpectedArity == 2

\* Foo2!1!(1, 2)
\* MCops == <<"Foo2", "1", "null">>
\* MCargs ==   << << >>, << >>, <<14, 20>> >>
\* MCexpectedArity == 0

\* Foo2!1!(1, 2)!2
\* MCops == <<"Foo2", "1", "null", "2">>
\* MCargs ==   << << >>, << >>, <<14, 20>>, << >> >>
\* MCexpectedArity == 0

\* Inst!Foo2!1
\* MCops == <<"Inst", "Foo2", "1">>
\* MCargs ==   << << >>, << >>, << >> >>
\* MCexpectedArity == 3

\* Inst!Foo2!1
\* MCops == <<"Inst", "Foo2", "1", "@">>
\* MCargs ==   << << >>, << >>, << >>, << >> >>
\* MCexpectedArity == 3

\* Inst!Foo2!1!2
\* MCops == <<"Inst", "Foo2", "1", "@", "2">>
\* MCargs ==   << << >>, << >>, << >>, << >>, << >> >>
\* MCexpectedArity == 3

\* Inst("Argm")!Foo2!1!(1, 2)
\* MCops == <<"Inst", "Foo2", "1", "null">>
\* MCargs ==   << <<31>>,  << >>, << >>, <<14, 20>> >>
\* MCexpectedArity == 0

\* Inst("Argm")!Foo2!1!(1, 2)!2
\* MCops == <<"Inst", "Foo2", "1", "null", "2">>
\* MCargs ==   << <<31>>, << >>, << >>, <<14, 20>>, << >> >>
\* MCexpectedArity == 0

\* Thm!1
\* MCops == <<"Thm", "1" >>
\* MCargs ==   << << >>, << >> >> 
\* MCexpectedArity == 0

\* Thm!2
\* MCops == <<"Thm", "2" >>
\* MCargs ==   << << >>, << >> >> 
\* MCexpectedArity == 0

\* Thm!3!<<
\* MCops == <<"Thm", "3", "<<" >>
\* MCargs ==   << << >>, << >>, << >> >> 
\* MCexpectedArity == 0

\* Inst("Argm")!Thm!1
\* MCops == <<"Inst", "Thm", "1" >>
\* MCargs ==   << <<31>>, << >>, << >> >> 
\* MCexpectedArity == 0

\* Inst("Argm")!Thm!2
\* MCops == <<"Inst", "Thm", "2" >>
\* MCargs ==   << <<31>>, << >>, << >> >> 
\* MCexpectedArity == 0

\* Inst("Argm")!Thm!3!<<  
\* MCops == <<"Inst", "Thm", "3", "<<" >>
\* MCargs ==   << <<31>>, << >>, << >>, << >> >> 
\* MCexpectedArity == 0

\* Inst("Argm")!UU
\* MCops == <<"Inst", "UU">>
\* MCargs ==   << <<31>>, << >> >> 
\* MCexpectedArity == 0

\* Inst("Argm")!Bar(Arg1)!1<<  
\* MCops == <<"Inst", "Bar", "1" >>
\* MCargs ==   << <<31>>, <<10 >>, << >> >> 
\* MCexpectedArity == 0

\* Inst("Argm")!Bar(Arg1)!1<<  
\* MCops == <<"Inst", "Bar", "1" >>
\* MCargs ==   << <<31>>, <<10 >>, << >> >> 
\* MCexpectedArity == 0

\* Inst("Argm")!Thm             \* Note: doesn't report an error because 
\* MCops == <<"Inst", "Thm" >>  \* Inst!Thm isn't expanded
\* MCargs ==   << <<31>>, << >> >>
\* MCexpectedArity == 0

\* Inst("Argm")!Thm!:  ERROR!
\* MCops == <<"Inst", "Thm", ":" >>
\* MCargs ==   << <<31>>, << >>, << >> >>
\* MCexpectedArity == 0


\* Foo2
\* MCops == <<"Foo2">>
\* MCargs ==   <<<< >> >>
\* MCexpectedArity == 0

\* Foo3!(3)!:Bar3
\* MCops == <<"Foo3", "null", "Bar3">>
\* MCargs ==   << << >>, <<22>>, << >> >>
\* MCexpectedArity == 0

\* Bar(Arg1)
\* \* MCops == <<"Bar">>
\* \* MCargs ==   << <<10>> >>
\* \* MCexpectedArity == 0

\* Arg1(C)    
\* MCops == <<"Arg1">>
\* MCargs ==   << <<18>> >>
\* MCexpectedArity == 0

\* AOp  
\* MCops == <<"AOp">>  
\* MCargs ==   << <<18 >> >>
\* MCexpectedArity == 0

\* C  
\* MCops == <<"C">>  
\* MCargs ==   << << >> >>
\* MCexpectedArity == 0

\* p  
\* MCops == <<"p">>  
\* MCargs ==   << << >> >>
\* MCexpectedArity == 0

\* Foo3  
\* MCops == <<"Foo3">>  
\* MCargs ==   << << >> >>
\* MCexpectedArity == 0

\***** THIS IS A BUG--NOT HANDLED CORRECTLY ******
\* UU!lab
\* MCops == <<"UU", "lab">>  
\* MCargs ==   << << >>, << >> >>
\* MCexpectedArity == 0

\* Op(2, 2)!(2, 2, 2)
\* MCops == <<"Op", "null">>
\* MCargs ==   << <<20, 20>>, <<20, 20, 20 >> >>
\* MCexpectedArity == 0

\* Foo3!(2)
\* MCops == <<"Foo3", "null">>
\* MCargs ==   << << >>, <<20>> >>
\* MCexpectedArity == 0

\* Op(2, 2)!(2,2,2)!+(2, 2)
\* MCops == <<"Op", "null", "+">>
\* MCargs ==   << <<20,20 >>, <<20,20,20>> , <<20,20>>>>
\* MCexpectedArity == 0

\* MCops == <<"Op">> 
\* MCargs ==   << << >> >>
\* MCexpectedArity == -1

\* MCops == <<"Inst", "Op">> 
\* MCargs ==   << << >> , << >> >>
\* MCexpectedArity == -1

\* MCops == <<"Inst", "Thm">> 
\* MCargs ==   << << >> , << >> >>
\* MCexpectedArity == -1

\* MCops == <<"Inst", "Op", "@", "+">>
\* MCargs ==   << << >> , << >> , << >> , << >> >>
\* MCexpectedArity == -1

\* MCops == <<"Op", "lab", ":", "+">>
\* MCargs ==   << << >> , << >>, << >>,  << >> >>
\* MCexpectedArity == 7

\* MCops == <<"Op", "lab", ":", "+">>
\* MCargs ==   << << >> , << >>, << >>,  << >> >>
\* MCexpectedArity == -1

\* MCops == <<"Foo2">>
\* MCargs ==   << << >> >> 
\* MCexpectedArity == 0

\* MCops == <<"Foo3", ":">>
\* MCargs ==   << << >>, << >> >> 
\* MCexpectedArity == 0

\* MCops == <<"Op", "lab", ":", "+">>
\* MCargs ==   << << >>, << >>, << >>, << >> >> 
\* MCexpectedArity == -1

\* MCops == <<"Inst", "Thm">>
\* MCargs ==   << <<14 >>,  << >> >>
\* MCexpectedArity == 0

MCops == <<"Inst", "Thm", ":">>
MCargs ==   << <<14 >>,  << >>, << >> >>
MCexpectedArity == 0
MCdebug == FALSE \* TRUE

(*********************************
(***************************************************************************)
(* Module M                                                                *)
(* CONSTANT C                                                              *)
(* Op(Arg(_), p) == \A x \in {1,2}, <<y, z>> \in {3} :                     *)
(*                      lab(x,y,z) :: LET a + b == <<Arg(a), b>>           *)
(*                                    IN  1 + label2 :: p + C              *)
(*                                                                         *)
(* Foo(u) == "FooBody(u)"                                                  *)
(* Inst(w) == INSTANCE M WITH C <- <<w, CONST>>                            *)
(***************************************************************************)

\* MCNode == 
\*  1 :> [kind |-> NumeralKind,
\*        val  |-> 1]
\* @@
\*  2 :> [kind  |-> BuiltInKind,         \* \E 
\*        name  |-> "$UnboundedExists",
\*        arity |-> -1]
\*         
\* @@
\*  3 :> [kind     |-> OpApplKind,            \* \E x : Node 1
\*        operands |-> <<1>>,
\*        operator |-> 2,
\*        unboundedBoundSymbols |-> <<"x">>,
\*        boundedBoundSymbols |-> << >>,
\*        ranges |-> << >>]
\* @@
\*  4 :> [kind     |-> UserDefinedOpKind,    \* Inst!UserOp(p1, OpP) == Node 8
\*        name     |-> "Inst!UserOp",
\*        body     |-> 8,
\*        labels   |->  "Label1" :> 7,
\*        arity    |-> 2,
\*        params   |-> <<[name |-> "p1",  arity |-> 0],
\*                       [name |-> "OpP", arity |-> 0]>>,
\*        defined  |-> TRUE,
\*        source   |-> 40   ]
\* @@
\*  5 :> [kind     |-> ModuleInstanceKind,    \* Inst(p1) == INSTANCE
\*        name     |-> "Inst",
\*        arity    |-> 1,
\*        params   |-> <<[name |-> "p1", arity |-> 0] >>,
\*        defined  |-> TRUE   ]
\* @@
\*  6 :> [kind     |-> UserDefinedOpKind,    \* 1ArgOp(1OpP(_, _)) == Node 1
\*        name     |-> "1ArgOp",
\*        body     |-> 41,
\*        labels   |-> << >>,
\*        arity    |-> 1,
\*        params   |-> <<[name |-> "1OpP", arity |-> 0]>>,
\*        defined  |-> TRUE,
\*        source   |-> null   ]
\* @@
\*  7 :> [kind     |-> LabelKind,
\*        name     |-> "Label1",
\*        body     |-> 14,
\*        arity    |-> 1,
\*        params   |-> <<[name |-> "labParam1", arity |-> 0]>>,
\*        labels   |-> "Label2" :> 9
\*       ]
\* @@
\*  8 :> [kind  |-> SubstInKind,
\*        body  |-> 11,
\*        subst |-> "x <- something(p1)"]
\* 
\* @@
\*  9 :> [kind     |-> LabelKind,
\*        name     |-> "Label2",
\*        body     |-> 15,
\*        arity    |-> 1,
\*        params   |-> <<[name |-> "labParam2", arity |-> 0]>>,
\*        labels   |-> << >>
\*       ]
\* @@
\*  10 :> [kind |-> NumeralKind,
\*         val  |-> 10]
\* @@
\*  11 :> [kind  |-> SubstInKind,
\*         body  |-> 15,
\*         subst |-> "y <- something(p1)"]
\* @@
\*  12 :> [kind |-> StringKind,
\*         val  |-> "Body of UserOp (p1, OpP)"]
\* @@
\*  13 :> [kind |-> StringKind,
\*         val  |-> "Body of Label2(labParam2)"]
\* @@
\*  14 :> [kind |-> StringKind,
\*         val  |-> "Body of Label1(labParam1)"]
\* @@
\*  15 :> [kind    |-> LetInKind,
\*         context |-> "1ArgOp" :> 6,
\*         body    |-> 16]
\* @@
\*  16 :> [kind |-> StringKind,
\*         val  |-> "Body of Let/In"]
\* @@
\*  17 :> [kind     |-> UserDefinedOpKind,    \* 1ArgOp("1OpP") == Node 1
\*         name     |-> "Foo",
\*         body     |-> 18,
\*         labels   |-> << >>,
\*         arity    |-> 0,
\*         params   |-> << >> , \*  <<[name |-> "FooPar1", arity |-> 0]>>,
\*         defined  |-> TRUE,
\*         source   |-> null] 
\* @@
\*  18 :> [kind     |-> OpApplKind,            
\*         operands |-> <<42 >>,
\*         operator |-> 21,
\*         unboundedBoundSymbols |-> <<>>,
\*         boundedBoundSymbols |-> << >>,
\*         ranges |-> << >>]
\* @@
\*  19 :> [kind |-> StringKind,
\*         val  |-> "Arg1"]
\* @@
\*  20 :> [kind |-> StringKind,
\*         val  |-> "Arg2"]
\* @@
\*  21 :> [kind    |-> UserDefinedOpKind,    \* Foo2 == [rcd-lab1 |-> rcd-comp1,
\*         name     |-> "Foo2",              \*            ...
\*         body     |-> 34,                  \*          rcd-lab3 |-> rcd-comp3]
\*         labels   |->  << >>,
\*         arity    |-> 1,
\*         params   |-> <<[name |-> "p1",  arity |-> 1]>>,
\*         defined  |-> TRUE,
\*         source   |-> null   ]
\* @@ 
\*  22 :> [kind     |-> OpApplKind,            
\*         operands |-> <<10 (* 25 *) , 28, 31>>,
\*         operator |-> 23,
\*         unboundedBoundSymbols |-> <<>>,
\*         boundedBoundSymbols |-> << >>,
\*         ranges |-> << >>]
\* @@ 
\*  23 :> [kind  |-> BuiltInKind,
\*         name  |-> "$Except", \* "$Case", \* "$SetOfRcds", 
\*         arity |-> -1
\*        ]
\* @@ 
\*  24 :> [kind  |-> BuiltInKind,
\*         name  |-> "$Pair", 
\*         arity |-> 2
\*        ]
\* @@ 
\*  25 :> [kind     |-> OpApplKind,            
\*         operands |-> <<26,27>>,
\*         operator |-> 24,
\*         unboundedBoundSymbols |-> <<>>,
\*         boundedBoundSymbols |-> << >>,
\*         ranges |-> << >>]
\* @@ 
\*  26 :> [kind |-> StringKind,
\*         val  |-> "rcd-lab1"]
\* @@ 
\*  27 :> [kind |-> StringKind,
\*         val  |-> "rcd-comp1"]
\* 
\* @@ 
\*  28 :> [kind     |-> OpApplKind,            
\*         operands |-> <<29,30>>,
\*         operator |-> 24,
\*         unboundedBoundSymbols |-> <<>>,
\*         boundedBoundSymbols |-> << >>,
\*         ranges |-> << >>]
\* @@ 
\*  29 :> [kind |-> StringKind,
\*         val  |-> "rcd-lab2"]
\* @@ 
\*  30 :> [kind |-> StringKind,
\*         val  |-> "rcd-comp2"]
\* @@ 
\*  31 :> [kind     |-> OpApplKind,            
\*         operands |-> <<32,33>>,
\*         operator |-> 24,
\*         unboundedBoundSymbols |-> <<>>,
\*         boundedBoundSymbols |-> << >>,
\*         ranges |-> << >>]
\* @@ 
\*  32 :> [kind |-> StringKind,
\*         val  |-> "rcd-lab3"]
\* @@ 
\*  33 :> [kind |-> StringKind,
\*         val  |-> "rcd-comp3"]
\* @@
\*  34 :> [kind     |-> OpApplKind,            
\*         operands |-> <<35>>,
\*         operator |-> 36,
\*         unboundedBoundSymbols |-> <<>>,
\*         boundedBoundSymbols |-> << <<"b1", "b2">>, <<"b3">> >>,
\*         ranges |-> <<37, 38 >>]
\* @@ 
\*  35 :> [kind |-> StringKind,
\*         val  |-> "Fcn of b1, b2, b3"]
\* @@
\*  36 :> [kind  |-> BuiltInKind,
\*         name  |-> "$Pair", 
\*         arity |-> 2
\*        ]
\* @@ 
\*  37 :> [kind |-> StringKind,
\*         val  |-> "Range 1"]
\* @@ 
\*  38 :> [kind |-> StringKind,
\*         val  |-> "Range 2"]
\* @@ 
\*  39 :> [kind |-> StringKind,
\*         val  |-> "Arg3"]
\* @@ 
\*  40 :> [kind    |-> UserDefinedOpKind,    \* Inst!UserOp(p1, OpP) == Node 8
\*         name    |-> "UserOp",
\*         body    |-> 8,
\*         labels  |->  "Label1" :> 7,
\*         arity   |-> 1,
\*         params  |-> <<[name |-> "OpP", arity |-> 1]>>,
\*         defined |-> TRUE,
\*         source  |-> null   ]
\* @@
\*  41 :> [kind |-> StringKind,
\*         val  |-> "Body of 1ArgOp may dep on (x, y)"]
\* @@
\*  42 :> [kind  |-> OpArgKind,
\*         op    |-> 43,
\*         arity |-> 1,
\*         name  |-> "Foo3"]
\* @@
\*  43 :> [kind     |-> UserDefinedOpKind,    \* 1ArgOp("1OpP") == Node 1
\*         name     |-> "Foo3",
\*         body     |-> 18,
\*         labels   |-> << >>,
\*         arity    |-> 0,
\*         params   |-> << >>, \* <<[name |-> "FooPar1", arity |-> 0]>>,
\*         defined  |-> TRUE,
\*         source   |-> null] 
\* 
\* MCNodeId == 1..43
\* 
\* MCGlobalContext ==
\*   "Inst!UserOp" :> 4
\* @@
\*   "Inst" :> 5
\* @@
\*   "Foo" :> 17
\* @@
\*   "Foo2" :> 21
\* @@
\*   "Foo3" :> 43
\* \* @@
\* \*   "1ArgOp" :> 6
\* 
\* 
\* MCops == <<"Inst", "UserOp">> \* ,  "1">> 
\* MCargs ==   << <<1 >> , <<1>> >>

\* \* << <<1>>, <<19, 20, 33 >> >> \* <<1>>, <<10>>, << >>, <<4>> >>
\*      
\* MCexpectedArity == 0 \* -1 \* 5
***************************)

-----------------------------------------------------------------------------
(***************************************************************************)
(*                            THE ALGORITHM                                *)
(***************************************************************************)
(**************************************  
--algorithm Subexpression
variables 
  (*************************************************************************)
  (* The input variables.                                                  *)
  (*************************************************************************)
  ops = MCops,
  args = MCargs,
    (***********************************************************************)
    (* The sequences op and args described above.                          *)
    (***********************************************************************)
  expectedArity = MCexpectedArity,
    (***********************************************************************)
    (* The arity of the operator expected, or -1 if expecting a definition *)
    (* name.  It is 0 iff an expression is expected.  The result should be *)
    (* an OpArg node if expectedArity > 0, it should be an expression node *)
    (* if expectedArity = 0, and it should be a UserDefinedOpKind or a     *)
    (* ThmOrAssumpDefKind if expectedArity < 0.                            *)
    (***********************************************************************)
    
  (*************************************************************************)
  (* The major variables of the algorithm.                                 *)
  (*************************************************************************)
  substInPrefix = << >> ,
    (***********************************************************************)
    (* The sequence of SubstInNode or APSubstInNode sequence that will be  *)
    (* appended to body of the resulting OpApplNode                        *)
    (***********************************************************************)
  params = << >> ,
    (***********************************************************************)
    (* The sequence of FormalParamNode objects that are the formal         *)
    (* parameters if this produces a Lambda expression.  A Lambda          *)
    (* expression will be produced iff this is non-empty                   *)
    (***********************************************************************)
  allArgs = << >> ,
    (***********************************************************************)
    (* The sequence of all arguments.                                      *)
    (***********************************************************************)
  curNode = null,
    (***********************************************************************)
    (* If params = << >>, then the OpDefNode for the OpApplNode that is    *)
    (* produced.  If params # << >>, then the Expr node that will form the *)
    (* body of the Lambda expression.                                      *)
    (*                                                                     *)
    (* Note: in the Java implementation, this will actually be a ref to    *)
    (* the node--in terms of this spec, a NodeId.                          *)
    (***********************************************************************)
  subExprOf = "null",
    (***********************************************************************)
    (* The node UserDefinedOpDefKind or ThmOrAssumpDefKind within which    *)
    (* this subexpression is defined.                                      *)
    (***********************************************************************)
  result = null,
    (***********************************************************************)
    (* The actual output node.                                             *)
    (***********************************************************************)
    
  (*************************************************************************)
  (* The local variables.                                                  *)
  (*************************************************************************)
  idx = 1,
    (***********************************************************************)
    (* The element of the arrays op and args that the algorithm is         *)
    (* currently examining.                                                *)
    (***********************************************************************)
  mode = "FindingOpName",
    (***********************************************************************)
    (* The current mode describing what kind of selector it is expecting   *)
    (* next.  Its other possible values are "FollowingLabels" and          *)
    (* "FindingSubExpr".                                                   *)
    (***********************************************************************)
  prevMode = "",
    (***********************************************************************)
    (* The mode for the previously examined selector.                      *)
    (***********************************************************************)
  curContext = GlobalContext,
    (***********************************************************************)
    (* The context for looking up operator or label names.                 *)
    (***********************************************************************)
  curName = "" , 
    (***********************************************************************)
    (* When looking up an operator name, which may be something like       *)
    (* "Foo!Bar!Baz", this is the part that has been found so far.         *)
    (***********************************************************************)
  opDefArityFound = 0,
  opDefArgs = << >>,
    (***********************************************************************)
    (* The total arity and the sequence of arguments found so far for the  *)
    (* current operator--for example, opDefArityFound will equal 2 if the  *)
    (* algorithm has so far processed "Foo(a, b)!Bar"                      *)
    (***********************************************************************)
  firstFindingOpName = TRUE,
    (***********************************************************************)
    (* True iff have entered the FindingOpName only once (initially).      *)
    (***********************************************************************)
  opNode,
  newName,
  newNode,
  nodeArity,
  temp,
  tempArgs


(***************************************************************************)
(* A macro used for reporting an error and terminating the execution.      *)
(***************************************************************************)
macro Error(msg) begin print msg ;
                       if debug then (**************************************)
                                     (* Force the +cal translator to       *)
                                     (* insert a label so the error trace  *)
                                     (* shows the final state.             *)
                                     (**************************************)
                                     idx := idx ;
                                     idx := idx ;
                                     assert FALSE 
                                else goto Done
                       end if 
                 end macro ;

 begin

  (*************************************************************************)
  (* An assertion that checks that ops and args are consistent with each   *)
  (* other and with the value of expectedArity.  In an implementation,     *)
  (* some of these should be guaranteed by the context (e.g., Len(ops) =   *)
  (* Len(args) while others will be checked as part of the processing for  *)
  (* the particular value of idx.                                          *)
  (*************************************************************************)
  assert /\ expectedArity \in Int
         /\ ops  \in Seq(STRING)
         /\ args \in Seq(Seq(NodeId))
         /\ Len(ops) = Len(args)
         /\ \A i \in 1..Len(ops) :
              /\ \/ ops[i] \in {"<<", ">>", "@", ":"} \cup NumberOp 
                 \/ expectedArity # 0
                 => args[i] = << >>  
              /\ (ops[i] = "null") => (Len(args[i]) > 0) ;

  (*************************************************************************)
  (* The outer "for" loop on idx.                                          *)
  (*************************************************************************)
  while idx <= Len(ops) do
  if mode = "FindingOpName" then

\* The following code was modified by LL on 23 Sep 2009 to fix the following
\* bug.  The parser produced a bogus error on a reference to an identifier 
\* M!N that is imported by an unnamed INSTANCE of a module containing the
\* statement M == INSTANCE ... .  The original code essentially just 
\* contained the first iteration of the following while loop, and would
\* report an error if it found newNode = null.  Thus, it would report
\* an error in the identifier M!N when it found M to be undefined.
\*   
\* Corrected by LL on 9 Nov 2009 to handle arguments of those
\* undefined operators.  They are put into tempArgs when they are
\* found.

   newNode := null ;
   tempArgs := << >> ;
     (**********************************************************************)
     (* The number of arguments found in the following loop for the        *)
     (* undefined operators                                                *)
     (**********************************************************************)
   while newNode = null do
     if idx \geq Len(ops)
       then Error ("Unknown operator");
     end if;
     newName := IF IsName(ops[idx])
                  THEN IF curName = "" THEN ops[idx] 
                                       ELSE curName \o "!" \o ops[idx]
                  ELSE null ;
     if /\ curName = ""
        /\ ~ IsName(ops[idx])
       then (***************************************************************)
            (* I think that this error can only happen for idx = 1, and    *)
            (* should never happen in the implementation because the       *)
            (* parser should not allow a compound name that doesn't begi   *)
            (* with a name.                                                *)
            (***************************************************************)
            Error("Need an operator or label name or step number here")
       end if;
     newNode := IF newName # null THEN LookUp(newName, curContext) ELSE null ;
     if newName = null
       then tempArgs := tempArgs \o args[idx];
            idx := idx + 1;
     end if;
   end while ;     
   curNode := newNode ;
   curName := newName ;
   if curNode.kind \in 
          {UserDefinedOpKind, ThmOrAssumpDefKind,
             ModuleInstanceKind, ConstantDeclKind, VariableDeclKind, 
             FormalParamKind, BuiltInKind, BoundSymbolKind} 
     then if curNode.kind \in 
                  {ConstantDeclKind, VariableDeclKind, FormalParamKind, 
                   BuiltInKind, BoundSymbolKind}
             then if idx # 1 
                    then Error("Abort: Impossible naming of declaration "
                                \o "or built-in operator.")
                    else if Len(ops) # 1
                           then Error("Can't take subexpression of this");
                         end if
                 end if                 
          end if ;
          nodeArity := Arity(curNode) ;
          tempArgs := tempArgs \o args[idx];
          if expectedArity = 0
            then if opDefArityFound + Len(tempArgs) # nodeArity
                   then Error("Wrong number of arguments")
                 end if ;
                 if \E i \in 1..Len(tempArgs[idx]) :
                          Arity(Node[tempArgs[idx][i]]) #
                            ParamArity(curNode, i + opDefArityFound)
                    then Error("Argument has wrong arity")
                    else opDefArgs := opDefArgs \o tempArgs; 
                 end if ;
            else if expectedArity > 0
                   then if \E i \in 1..Len(curNode.params) :
                              curNode.params[i].arity > 0
                          then Error("Higher-order operator selected " 
                                       \o "as operator argument") 
                        end if
\*                   else Error(
\*                         "Abort: Don't yet handle expectedArity < 0")
                 end if
          end if ;
          opDefArityFound := nodeArity ;
          if curNode.kind \in {UserDefinedOpKind, ThmOrAssumpDefKind,
                               ConstantDeclKind, VariableDeclKind, 
                               FormalParamKind, BoundSymbolKind} 
            then if /\ curNode.kind = UserDefinedOpKind
                    /\ ~ curNode.defined 
                    /\ ~ Len(ops) = 1
                   then Error("Can't refer to subexpression of "
                               \o "operator inside its definition")
                 end if;
                 if /\ firstFindingOpName
                    /\ curNode.kind \in {UserDefinedOpKind, ThmOrAssumpDefKind}
                   then subExprOf := curNode
                 end if;               
                 if idx # Len(ops)
                   then params := params \o curNode.params ;
                        curName := "" ;
                        if IsName(ops[idx+1])
                          then mode := "FollowingLabels"
                          else mode := "FindingSubExpr" ;
                        end if ;
                        allArgs := allArgs \o opDefArgs ;
                        opDefArityFound := 0 ;
                        opDefArgs := << >> ;
                        newNode  := Node[curNode.body] ;
                        while newNode.kind = SubstInKind do
                          substInPrefix := substInPrefix \o <<newNode>>;
                          newNode := Node[newNode.body];  
                        end while ;
                        while newNode.kind \in {SubstInKind, APSubstInKind}
                           (************************************************)
                           (* Added APSubstInKind test on 13 Nov 2009.     *)
                           (************************************************)
                         do
                          substInPrefix := substInPrefix \o <<newNode>>;
                          newNode := Node[newNode.body];  
                        end while ;
                        (********************************************)
                        (* If the next op is an OpSel, then need to *)
                        (* skip over SubstInNodes, which are        *)
                        (* invisible to the user.                   *)
                        (********************************************)
                        if mode = "FindingSubExpr"
                          then curNode := newNode 
                        end if;
                 end if ;
           else  \* curNode.kind = ModuleInstanceKind
                 if (idx = Len(ops))
                   then Error("Operator name incomplete")
                 end if
          end if
   else Error("Unexpected node kind") ;
   end if ;
   prevMode := "FindingOpName" ;

        
  elsif mode = "FollowingLabels" then
     if prevMode = "FindingOpName"
       then assert curNode.kind \in {UserDefinedOpKind, ThmOrAssumpDefKind} ;
            newNode := LookUp(ops[idx], curNode.labels) ;
       else assert curNode.kind = LabelKind ;
            newNode := LookUp(ops[idx], curNode.labels) ;
     end if ;
     if newNode =  null
       then Error("Label not found")
     end if;
     curNode := newNode ;
     if expectedArity = 0
       then if Len(args[idx]) # curNode.arity 
              then Error("bad arity")
            end if ;
            if \E i \in 1..Len(args[idx]) :
                   Arity(Node[args[idx][i]]) # 0
              then Error("Operator argument given to label")
            end if;
            allArgs := allArgs \o args[idx] ;
     end if;
     params := params \o curNode.params ;                        
     if /\ idx < Len(ops)
        /\ ~IsName(ops[idx+1])
       then mode := "FindingSubExpr"
     end if ;
     if \/ mode = "FindingSubExpr"
        \/ idx = Len(ops)  
       then curNode := Node[curNode.body]
     end if;
     prevMode := "FollowingLabels";


  elsif mode = "FindingSubExpr" then
    if ops[idx] = ":" then 
      if \/ prevMode \notin {"FindingOpName", "FollowingLabels"}
         \/ ~ \/ /\ idx = Len(ops)
                 /\ prevMode = "FindingOpName"
              \/ /\ idx < Len(ops)
                 /\ IsName(ops[idx+1])
        then Error("`!:' can be used only after a name and either at the " \o
                   "end after an operator name or before an operator name.")
      end if 

    elsif curNode.kind = LetInKind then
      if ArgNum(ops[idx], 1) = 1
        then curNode := Node[curNode.body]
        else Error("A Let/In has only a single operand")
      end if ;

    elsif curNode.kind = OpApplKind then
      opNode := Node[curNode.operator] ;
      if opNode.kind 
              \in {FormalParamKind, ConstantDeclKind, UserDefinedOpKind} then
         (******************************************************************)
         (* Selecting an argument from something of the form Op(...).      *)
         (******************************************************************)
         temp := ArgNum(ops[idx], opNode.arity) ;
         if temp = -1
           then Error("Nonexistent operand specified")
           else curNode := Node[curNode.operands[temp]]
         end if
      elsif opNode.kind = BuiltInKind then 
              \*  See configuration/ConfigConstants for a list of all
              \*  BuiltInKind operators.
        if opNode.name \in {"$RcdConstructor", "$SetOfRcds"} then
          (*****************************************************************)
          (* curNode represents an expression                              *)
          (*   [a_1 |-> e_1, ... , a_n |-> e_n] or                         *)
          (*   [a_1  :  e_1, ... , a_n  :  e_n]                            *)
          (* Its i-th argument is the $Pair node (a_i, e_i)                *)
          (*****************************************************************)
          temp := ArgNum(ops[idx], Len(curNode.operands)) ;
          if temp = -1 
            then Error("Incorrect subexpression number")
          end if ;
          curNode := Node[curNode.operands[temp]] ;
          if \/ curNode.kind # OpApplKind
             \/ Node[curNode.operator].kind # BuiltInKind
             \/ Node[curNode.operator].name # "$Pair"
            then Error ("Expecting $Pair(...)")
            else curNode := Node[curNode.operands[2]]
          end if

        elsif opNode.name \in {"$Case"} then
          (*****************************************************************)
          (* The i-th clause is a $Pair node, where for the OTHER clause   *)
          (* the 1st element is null.                                      *)
          (*****************************************************************)
          if idx = Len(ops)
            then Error( "CASE subexpression must be of form !i!j")
          end if ;
          temp := ArgNum( ops[idx], Len(curNode.operands)) ;
          if temp = -1 
            then Error("Incorrect subexpression name")
          end if ;
          curNode := Node[curNode.operands[temp]] ;
          if \/ curNode.kind # OpApplKind
             \/ Node[curNode.operator].kind # BuiltInKind
             \/ Node[curNode.operator].name # "$Pair"
            then Error ("Expecting $Pair(...)")
          end if ;
          idx  := idx+1 ;
          temp := ArgNum(ops[idx], 2);
          if temp = -1 
            then Error("Incorrect subexpression name")
          end if ;
          curNode := Node[curNode.operands[temp]] ;
          if curNode = null
            then Error("Selecting OTHER")
          end if

        elsif opNode.name = "$Except" then
           (****************************************************************)
           (* For                                                          *)
           (*   [exp_1 ELSE !... = exp_2, ... , !.. = exp_n]               *)
           (* argument number i chooses exp_i.  For i > 1, exp_i is the    *)
           (* second argument of a $Pair operator.                         *)
           (****************************************************************)
           temp := ArgNum(ops[idx], Len(curNode.operands));
           if temp = -1 
             then Error("Bad argument selector.")
           end if;
           curNode := Node[curNode.operands[temp]] ;
           if temp > 1
             then if \/ curNode.kind # OpApplKind
                     \/ Node[curNode.operator].kind # BuiltInKind
                     \/ Node[curNode.operator].name # "$Pair"
                    then Error("Unexpected expression node found.")
                    else curNode := Node[curNode.operands[2]]
                  end if
           end if

        else
          (*****************************************************************)
          (* Operator handled by standard procedure.                       *)
          (*****************************************************************)
          if /\ Len(curNode.unboundedBoundSymbols) = 0 
             /\ Len(curNode.boundedBoundSymbols)   = 0
            then (**********************************************************)
                 (* Current subexpression has no bound variables.          *)
                 (**********************************************************)
                 temp := ArgNum(ops[idx], Len(curNode.operands)) ;
                 if temp = -1 
                   then Error("Incorrect subexpression selector")
                 end if;
                 curNode := Node[curNode.operands[temp]] ;
            else
                 (**********************************************************)
                 (* Current subexpression has bound variables.  If         *)
                 (* selector is "@" or null, then choosing body and adding *)
                 (* parameters.  Otherwise, must be selecting one of the   *)
                 (* bounds.                                                *)
                 (**********************************************************)
                 if ops[idx] \in {"null", "@"}
                   then (***************************************************)
                        (* Set temp to the sequence of parameters.         *)
                        (***************************************************)
                        temp := IF Len(curNode.unboundedBoundSymbols) > 0 
                                  THEN curNode.unboundedBoundSymbols
                                  ELSE SeqSeqToSeq(
                                          curNode.boundedBoundSymbols);

                        params := params \o 
                                   [i \in 1.. Len(temp) |->
                                     [name |-> temp[i], arity |-> 0]] ;
                        allArgs := allArgs \o args[idx] ;
                        if /\ ops[idx] = "null"
                           /\ Len(args[idx]) # Len(temp)
                          then Error("Wrong number of selector arguments");
                        end if;
                        curNode := Node[curNode.operands[1]];
                   else temp := ArgNum(ops[idx], Len(curNode.ranges)) ;
                        if temp = -1
                          then Error ("Selecting non-existent range") ;
                          else curNode := Node[curNode.ranges[temp]] 
                        end if
                 end if
          end if
        end if  \* opNode.name = ...
         
      else Error("Applying subexpression chooser to an expr" \o
                  " with no choosable subexpressions")
                            
      end if \* opNode.kind = ... 

    elsif curNode.kind = AssumeProveKind then
          temp := ArgNum(ops[idx], 1 + Len(curNode.assumes)) ;
          if temp = -1 
            then Error("Illegal argument number")
            else if temp <= Len(curNode.assumes) 
                   then curNode := Node[curNode.assumes[temp]]
                   else curNode := Node[curNode.prove]
                 end if
          end if

    elsif curNode.kind = OpArgKind then
      (*********************************************************************)
      (* The only kind of OpArgNode that has a subpart is a Lambda         *)
      (* expression.                                                       *)
      (*********************************************************************)
      opNode := Node[curNode.op] ;
      if \/ opNode.kind # UserDefinedOpKind
         \/ opNode.name # "LAMBDA"   then 
        Error("Selecting from operator argument that has no sub-part")
      elsif ops[idx] \notin {"null", "@"} then
        Error("Incorrect selection from LAMBDA")
      elsif /\ ops[idx] = "null"
            /\ Len(args[idx]) # Len(opNode.params)  then
        Error("Incorrect number of arguments for LAMBDA")        
      else params := params \o opNode.params ;
           allArgs := allArgs \o args[idx] ;
           curNode := Node[opNode.body] ;
      end if

    elsif curNode.kind \in {UserDefinedOpKind, BuiltInKind} then
      Error("Abort: should not have been able to choose this node.")

    elsif curNode.kind \in {AtNodeKind, DecimalKind, NumeralKind, StringKind,
                         FormalParamKind, ConstantDeclKind, VariableDeclKind,
                         BoundSymbolKind} then
         Error("Selected part has no subexpression")

    elsif curNode.kind = LabelKind then
      (*********************************************************************)
      (* Skip over label.                                                  *)
      (*********************************************************************)
      curNode := Node[curNode.body] ;
      idx := idx - 1  ;
    else 
       Error("Unexpected node kind found in expression")

    end if; \* ops[idx] = ":"

    if idx # Len(ops)
      then if IsName(ops[idx+1])
             then while curNode.kind = LabelKind do
                    curNode := Node[curNode.body]
                  end while ;                    
                  if curNode.kind = LetInKind
                    then curContext := curNode.context ;
                         mode := "FindingOpName" ;
                         firstFindingOpName := FALSE;
                    else Error("A name not following the selector of a LET")
                  end if
             else if ops[idx+1] = ":"
                    then Error("!: should not follow an operand selector")
                  end if ;
           end if ;
    end if ; \* ops[idx] = ":"
    prevMode := "FindingSubExpr";

  else Error("Bad value of mode")

  end if ; \* mode = ...

  idx := idx + 1;  
  end while ;

  if curNode.kind = AssumeProveKind 
    then Error("Selecting ASSUME/PROVE instead of expression")
  end if;

  if expectedArity < 0
    then if \/ prevMode # "FindingOpName" 
            \/ curNode.kind \notin {UserDefinedOpKind, ThmOrAssumpDefKind}
           then Error("Should have selected a definition, but didn't.")
         end if;
         result := curNode ;
         goto Finished 
  end if;

  if expectedArity > 0 
     then temp := Len(params) + IF \/ prevMode = "FindingOpName" 
                                   \/ curNode.kind = OpArgKind 
                                  THEN Arity(curNode)
                                  ELSE 0 ;
          if expectedArity # temp
            then Error("Expect arity = " \o ToString(expectedArity)
                           \o ", but found arity = " \o ToString(temp))
          end if
  end if;


  (*************************************************************************)
  (* If found an operator def and there are parameters or substitutions,   *)
  (* then set curNode to the operator applied to new parameters, add those *)
  (* parameters to params and add the arguments to allArgs.  Note: need to *)
  (* do this even if operator takes no parameters because we need to put   *)
  (* the operator in a LAMBDA expression whose body is an expression       *)
  (*************************************************************************)
  if /\ prevMode = "FindingOpName"
     /\ Len(params) + Len(substInPrefix) > 0
    then temp := [i \in 1..Len(curNode.params) |->
                             [curNode.params[i] EXCEPT !.name = "New " \o @]] ;
           (****************************************************************)
           (* temp := new formal parameters for the operator, with the     *)
           (*         same arities as the original parameters.             *)
           (****************************************************************)

         curNode := [kind     |-> OpApplKind,
                     operands |-> temp,
                     operator |-> curNode,
                     unboundedBoundSymbols |-> <<>>,
                     boundedBoundSymbols |-> << >>,
                     ranges |-> << >>] ;
         params := params \o temp ;
         allArgs := allArgs \o opDefArgs ;
  end if ;

  if curNode.kind = OpArgKind
    then if expectedArity = 0 then 
           Error("Selected Operator Argument when expression expected.")
         elsif expectedArity # Len(params) + curNode.arity then
           Error("Selected operator has wrong arity.")
         else 
           if Len(params) + Len(substInPrefix) > 0
              then (********************************************************)
                   (* If curNode is a LAMBDA, then this will eventually    *)
                   (* produce an OpArg node whose operator is a LAMBDA     *)
                   (* whose body is an OpApplNode that applies the         *)
                   (* curNode's LAMBDA to parameters of the outer LAMBDA.  *)
                   (* This result can be simplified to a LAMBDA whose body *)
                   (* is the body of curNode.  However, that               *)
                   (* simplification is what one will get by selecting the *)
                   (* body of the LAMBDA, so we keep this complicated      *)
                   (* expression in this case.                             *)
                   (********************************************************)
                   temp := [i \in 1..curNode.arity |-> 
                             [name |-> "NewParam" \o NumToString(i), 
                              arity |-> 0]] ;
                   curNode := [kind     |-> OpApplKind,
                               operands |-> temp,
                               operator |-> Node[curNode.op],
                               unboundedBoundSymbols |-> <<>>,
                               boundedBoundSymbols |-> << >>,
                               ranges |-> << >>] ;
                   params := params \o temp
           end if
         end if
  end if ;

  if curNode.kind \in {UserDefinedOpKind, ConstantDeclKind, VariableDeclKind, 
                       FormalParamKind, BuiltInKind, BoundSymbolKind,
                       ThmOrAssumpDefKind}   then 
    (***********************************************************************)
    (* There are no params or substitutions, so this is an easy case.      *)
    (***********************************************************************)
    if expectedArity > 0 then 
      result := [kind  |-> OpArgKind,
                 name  |-> curNode.name,
                 op    |-> curNode,
                 arity |-> expectedArity]
    elsif expectedArity = 0 then
      result := [kind |-> OpApplKind,
                 operands |-> opDefArgs,
                 operator |-> curNode,
                 unboundedBoundSymbols |-> <<>>,
                 boundedBoundSymbols |-> << >>,
                 ranges |-> << >>,
                 subExprOf |-> subExprOf]
    end if
  elsif curNode.kind = OpArgKind then
    (***********************************************************************)
    (* There are no params or substitutions, so this is an easy case.      *)
    (***********************************************************************)
    result := curNode ;
  else (******************************************************************)
       (* curNode should be an expression node.                          *)
       (******************************************************************)
       temp := Len(substInPrefix) ;
       while temp > 0 do
         curNode := [kind  |-> substInPrefix[temp].kind, 
                               (********************************************)
                               (* Changed on 13 Nov 2009 from SubstInKind. *)
                               (********************************************)
                     body  |-> curNode ,
                     subst |-> substInPrefix[temp].subst ] ;
         temp := temp - 1;
       end while;

       if expectedArity > 0
         then if Len(params) # expectedArity
                then Error ("Selection has wrong arity")
              end if ;
              result := [kind |-> OpArgKind,
                         op   |-> [kind    |-> UserDefinedOpKind,
                                   name    |-> "LAMBDA",
                                   body    |-> curNode,
                                   params  |-> params,
                                   arity   |-> Len(params),
                                   defined |-> TRUE,
                                   source  |-> null],
                         name |-> "LAMBDA"]
         else if Len(params) # Len(allArgs)
                then Error("Abort: number of params # num of args")
              end if ;
              if Len(params) = 0
                then (******************************************************)
                     (* This is the one case with expectedArity = 0 in     *)
                     (* which the result is not a newly-constructed node.  *)
                     (* In this case, we construct a dummy label node so   *)
                     (* we have a node to which the implementation can     *)
                     (* attach the syntax node.                            *)
                     (******************************************************)
                     result := [kind  |-> LabelKind,
                                name  |-> "$Subexpression",                  
                                arity  |-> 0,
                                params |-> << >>,
                                body   |-> curNode,
                                subExprOf |-> subExprOf]

                else result := [kind     |-> OpApplKind,
                                operator |-> [kind    |-> UserDefinedOpKind,
                                              name    |-> "LAMBDA",
                                              body    |-> curNode,
                                              params  |-> params,
                                              arity   |-> Len(params),
                                              defined |-> TRUE,
                                              source  |-> null],
                                operands |-> allArgs,
                                unboundedBoundSymbols |-> <<>>,
                                boundedBoundSymbols |-> << >>,
                                ranges |-> << >>,
                                subExprOf |-> subExprOf]
              end if
         end if

  end if;

Finished:
  print "Result: " ;
  print result ;
 
end algorithm
*********************************************************************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES ops, args, expectedArity, substInPrefix, params, allArgs, curNode, 
          subExprOf, result, idx, mode, prevMode, curContext, curName, 
          opDefArityFound, opDefArgs, firstFindingOpName, opNode, newName, 
          newNode, nodeArity, temp, tempArgs, pc

vars == << ops, args, expectedArity, substInPrefix, params, allArgs, curNode, 
           subExprOf, result, idx, mode, prevMode, curContext, curName, 
           opDefArityFound, opDefArgs, firstFindingOpName, opNode, newName, 
           newNode, nodeArity, temp, tempArgs, pc >>

Init == (* Global variables *)
        /\ ops = MCops
        /\ args = MCargs
        /\ expectedArity = MCexpectedArity
        /\ substInPrefix = << >>
        /\ params = << >>
        /\ allArgs = << >>
        /\ curNode = null
        /\ subExprOf = "null"
        /\ result = null
        /\ idx = 1
        /\ mode = "FindingOpName"
        /\ prevMode = ""
        /\ curContext = GlobalContext
        /\ curName = ""
        /\ opDefArityFound = 0
        /\ opDefArgs = << >>
        /\ firstFindingOpName = TRUE
        /\ opNode = defaultInitValue
        /\ newName = defaultInitValue
        /\ newNode = defaultInitValue
        /\ nodeArity = defaultInitValue
        /\ temp = defaultInitValue
        /\ tempArgs = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(/\ expectedArity \in Int
                   /\ ops  \in Seq(STRING)
                   /\ args \in Seq(Seq(NodeId))
                   /\ Len(ops) = Len(args)
                   /\ \A i \in 1..Len(ops) :
                        /\ \/ ops[i] \in {"<<", ">>", "@", ":"} \cup NumberOp
                           \/ expectedArity # 0
                           => args[i] = << >>
                        /\ (ops[i] = "null") => (Len(args[i]) > 0), 
                   "Failure of assertion at line line 1906, column 3.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                         allArgs, curNode, subExprOf, result, idx, mode, 
                         prevMode, curContext, curName, opDefArityFound, 
                         opDefArgs, firstFindingOpName, opNode, newName, 
                         newNode, nodeArity, temp, tempArgs >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF idx <= Len(ops)
               THEN /\ IF mode = "FindingOpName"
                          THEN /\ newNode' = null
                               /\ tempArgs' = << >>
                               /\ pc' = "Lbl_3"
                               /\ UNCHANGED << params, allArgs, curNode, idx, 
                                               opNode, temp >>
                          ELSE /\ IF mode = "FollowingLabels"
                                     THEN /\ IF prevMode = "FindingOpName"
                                                THEN /\ Assert(curNode.kind \in {UserDefinedOpKind, ThmOrAssumpDefKind}, 
                                                               "Failure of assertion at line line 2053, column 13.")
                                                     /\ newNode' = LookUp(ops[idx], curNode.labels)
                                                ELSE /\ Assert(curNode.kind = LabelKind, 
                                                               "Failure of assertion at line line 2055, column 13.")
                                                     /\ newNode' = LookUp(ops[idx], curNode.labels)
                                          /\ IF newNode' =  null
                                                THEN /\ PrintT("Label not found")
                                                     /\ IF debug
                                                           THEN /\ idx' = idx
                                                                /\ pc' = "Lbl_22"
                                                           ELSE /\ pc' = "Done"
                                                                /\ UNCHANGED idx
                                                ELSE /\ pc' = "Lbl_23"
                                                     /\ UNCHANGED idx
                                          /\ UNCHANGED << params, allArgs, 
                                                          curNode, opNode, 
                                                          temp >>
                                     ELSE /\ IF mode = "FindingSubExpr"
                                                THEN /\ IF ops[idx] = ":"
                                                           THEN /\ IF \/ prevMode \notin {"FindingOpName", "FollowingLabels"}
                                                                      \/ ~ \/ /\ idx = Len(ops)
                                                                              /\ prevMode = "FindingOpName"
                                                                           \/ /\ idx < Len(ops)
                                                                              /\ IsName(ops[idx+1])
                                                                      THEN /\ PrintT("`!:' can be used only after a name and either at the " \o
                                                                                     "end after an operator name or before an operator name.")
                                                                           /\ IF debug
                                                                                 THEN /\ idx' = idx
                                                                                      /\ pc' = "Lbl_29"
                                                                                 ELSE /\ pc' = "Done"
                                                                                      /\ UNCHANGED idx
                                                                      ELSE /\ pc' = "Lbl_63"
                                                                           /\ UNCHANGED idx
                                                                /\ UNCHANGED << params, 
                                                                                allArgs, 
                                                                                curNode, 
                                                                                opNode, 
                                                                                temp >>
                                                           ELSE /\ IF curNode.kind = LetInKind
                                                                      THEN /\ IF ArgNum(ops[idx], 1) = 1
                                                                                 THEN /\ curNode' = Node[curNode.body]
                                                                                      /\ pc' = "Lbl_63"
                                                                                      /\ UNCHANGED idx
                                                                                 ELSE /\ PrintT("A Let/In has only a single operand")
                                                                                      /\ IF debug
                                                                                            THEN /\ idx' = idx
                                                                                                 /\ pc' = "Lbl_30"
                                                                                            ELSE /\ pc' = "Done"
                                                                                                 /\ UNCHANGED idx
                                                                                      /\ UNCHANGED curNode
                                                                           /\ UNCHANGED << params, 
                                                                                           allArgs, 
                                                                                           opNode, 
                                                                                           temp >>
                                                                      ELSE /\ IF curNode.kind = OpApplKind
                                                                                 THEN /\ opNode' = Node[curNode.operator]
                                                                                      /\ IF opNode'.kind
                                                                                                 \in {FormalParamKind, ConstantDeclKind, UserDefinedOpKind}
                                                                                            THEN /\ temp' = ArgNum(ops[idx], opNode'.arity)
                                                                                                 /\ IF temp' = -1
                                                                                                       THEN /\ PrintT("Nonexistent operand specified")
                                                                                                            /\ IF debug
                                                                                                                  THEN /\ idx' = idx
                                                                                                                       /\ pc' = "Lbl_31"
                                                                                                                  ELSE /\ pc' = "Done"
                                                                                                                       /\ UNCHANGED idx
                                                                                                            /\ UNCHANGED curNode
                                                                                                       ELSE /\ curNode' = Node[curNode.operands[temp']]
                                                                                                            /\ pc' = "Lbl_63"
                                                                                                            /\ UNCHANGED idx
                                                                                                 /\ UNCHANGED << params, 
                                                                                                                 allArgs >>
                                                                                            ELSE /\ IF opNode'.kind = BuiltInKind
                                                                                                       THEN /\ IF opNode'.name \in {"$RcdConstructor", "$SetOfRcds"}
                                                                                                                  THEN /\ temp' = ArgNum(ops[idx], Len(curNode.operands))
                                                                                                                       /\ IF temp' = -1
                                                                                                                             THEN /\ PrintT("Incorrect subexpression number")
                                                                                                                                  /\ IF debug
                                                                                                                                        THEN /\ idx' = idx
                                                                                                                                             /\ pc' = "Lbl_32"
                                                                                                                                        ELSE /\ pc' = "Done"
                                                                                                                                             /\ UNCHANGED idx
                                                                                                                             ELSE /\ pc' = "Lbl_33"
                                                                                                                                  /\ UNCHANGED idx
                                                                                                                       /\ UNCHANGED << params, 
                                                                                                                                       allArgs, 
                                                                                                                                       curNode >>
                                                                                                                  ELSE /\ IF opNode'.name \in {"$Case"}
                                                                                                                             THEN /\ IF idx = Len(ops)
                                                                                                                                        THEN /\ PrintT("CASE subexpression must be of form !i!j")
                                                                                                                                             /\ IF debug
                                                                                                                                                   THEN /\ idx' = idx
                                                                                                                                                        /\ pc' = "Lbl_36"
                                                                                                                                                   ELSE /\ pc' = "Done"
                                                                                                                                                        /\ UNCHANGED idx
                                                                                                                                        ELSE /\ pc' = "Lbl_37"
                                                                                                                                             /\ UNCHANGED idx
                                                                                                                                  /\ UNCHANGED << params, 
                                                                                                                                                  allArgs, 
                                                                                                                                                  curNode, 
                                                                                                                                                  temp >>
                                                                                                                             ELSE /\ IF opNode'.name = "$Except"
                                                                                                                                        THEN /\ temp' = ArgNum(ops[idx], Len(curNode.operands))
                                                                                                                                             /\ IF temp' = -1
                                                                                                                                                   THEN /\ PrintT("Bad argument selector.")
                                                                                                                                                        /\ IF debug
                                                                                                                                                              THEN /\ idx' = idx
                                                                                                                                                                   /\ pc' = "Lbl_46"
                                                                                                                                                              ELSE /\ pc' = "Done"
                                                                                                                                                                   /\ UNCHANGED idx
                                                                                                                                                   ELSE /\ pc' = "Lbl_47"
                                                                                                                                                        /\ UNCHANGED idx
                                                                                                                                             /\ UNCHANGED << params, 
                                                                                                                                                             allArgs, 
                                                                                                                                                             curNode >>
                                                                                                                                        ELSE /\ IF /\ Len(curNode.unboundedBoundSymbols) = 0
                                                                                                                                                   /\ Len(curNode.boundedBoundSymbols)   = 0
                                                                                                                                                   THEN /\ temp' = ArgNum(ops[idx], Len(curNode.operands))
                                                                                                                                                        /\ IF temp' = -1
                                                                                                                                                              THEN /\ PrintT("Incorrect subexpression selector")
                                                                                                                                                                   /\ IF debug
                                                                                                                                                                         THEN /\ idx' = idx
                                                                                                                                                                              /\ pc' = "Lbl_50"
                                                                                                                                                                         ELSE /\ pc' = "Done"
                                                                                                                                                                              /\ UNCHANGED idx
                                                                                                                                                              ELSE /\ pc' = "Lbl_51"
                                                                                                                                                                   /\ UNCHANGED idx
                                                                                                                                                        /\ UNCHANGED << params, 
                                                                                                                                                                        allArgs, 
                                                                                                                                                                        curNode >>
                                                                                                                                                   ELSE /\ IF ops[idx] \in {"null", "@"}
                                                                                                                                                              THEN /\ temp' = (IF Len(curNode.unboundedBoundSymbols) > 0
                                                                                                                                                                                 THEN curNode.unboundedBoundSymbols
                                                                                                                                                                                 ELSE SeqSeqToSeq(
                                                                                                                                                                                         curNode.boundedBoundSymbols))
                                                                                                                                                                   /\ params' = params \o
                                                                                                                                                                                 [i \in 1.. Len(temp') |->
                                                                                                                                                                                   [name |-> temp'[i], arity |-> 0]]
                                                                                                                                                                   /\ allArgs' = allArgs \o args[idx]
                                                                                                                                                                   /\ IF /\ ops[idx] = "null"
                                                                                                                                                                         /\ Len(args[idx]) # Len(temp')
                                                                                                                                                                         THEN /\ PrintT("Wrong number of selector arguments")
                                                                                                                                                                              /\ IF debug
                                                                                                                                                                                    THEN /\ idx' = idx
                                                                                                                                                                                         /\ pc' = "Lbl_52"
                                                                                                                                                                                    ELSE /\ pc' = "Done"
                                                                                                                                                                                         /\ UNCHANGED idx
                                                                                                                                                                         ELSE /\ pc' = "Lbl_53"
                                                                                                                                                                              /\ UNCHANGED idx
                                                                                                                                                                   /\ UNCHANGED curNode
                                                                                                                                                              ELSE /\ temp' = ArgNum(ops[idx], Len(curNode.ranges))
                                                                                                                                                                   /\ IF temp' = -1
                                                                                                                                                                         THEN /\ PrintT("Selecting non-existent range")
                                                                                                                                                                              /\ IF debug
                                                                                                                                                                                    THEN /\ idx' = idx
                                                                                                                                                                                         /\ pc' = "Lbl_54"
                                                                                                                                                                                    ELSE /\ pc' = "Done"
                                                                                                                                                                                         /\ UNCHANGED idx
                                                                                                                                                                              /\ UNCHANGED curNode
                                                                                                                                                                         ELSE /\ curNode' = Node[curNode.ranges[temp']]
                                                                                                                                                                              /\ pc' = "Lbl_63"
                                                                                                                                                                              /\ UNCHANGED idx
                                                                                                                                                                   /\ UNCHANGED << params, 
                                                                                                                                                                                   allArgs >>
                                                                                                       ELSE /\ PrintT("Applying subexpression chooser to an expr" \o
                                                                                                                       " with no choosable subexpressions")
                                                                                                            /\ IF debug
                                                                                                                  THEN /\ idx' = idx
                                                                                                                       /\ pc' = "Lbl_55"
                                                                                                                  ELSE /\ pc' = "Done"
                                                                                                                       /\ UNCHANGED idx
                                                                                                            /\ UNCHANGED << params, 
                                                                                                                            allArgs, 
                                                                                                                            curNode, 
                                                                                                                            temp >>
                                                                                 ELSE /\ IF curNode.kind = AssumeProveKind
                                                                                            THEN /\ temp' = ArgNum(ops[idx], 1 + Len(curNode.assumes))
                                                                                                 /\ IF temp' = -1
                                                                                                       THEN /\ PrintT("Illegal argument number")
                                                                                                            /\ IF debug
                                                                                                                  THEN /\ idx' = idx
                                                                                                                       /\ pc' = "Lbl_56"
                                                                                                                  ELSE /\ pc' = "Done"
                                                                                                                       /\ UNCHANGED idx
                                                                                                            /\ UNCHANGED curNode
                                                                                                       ELSE /\ IF temp' <= Len(curNode.assumes)
                                                                                                                  THEN /\ curNode' = Node[curNode.assumes[temp']]
                                                                                                                  ELSE /\ curNode' = Node[curNode.prove]
                                                                                                            /\ pc' = "Lbl_63"
                                                                                                            /\ UNCHANGED idx
                                                                                                 /\ UNCHANGED << params, 
                                                                                                                 allArgs, 
                                                                                                                 opNode >>
                                                                                            ELSE /\ IF curNode.kind = OpArgKind
                                                                                                       THEN /\ opNode' = Node[curNode.op]
                                                                                                            /\ IF \/ opNode'.kind # UserDefinedOpKind
                                                                                                                  \/ opNode'.name # "LAMBDA"
                                                                                                                  THEN /\ PrintT("Selecting from operator argument that has no sub-part")
                                                                                                                       /\ IF debug
                                                                                                                             THEN /\ idx' = idx
                                                                                                                                  /\ pc' = "Lbl_57"
                                                                                                                             ELSE /\ pc' = "Done"
                                                                                                                                  /\ UNCHANGED idx
                                                                                                                       /\ UNCHANGED << params, 
                                                                                                                                       allArgs, 
                                                                                                                                       curNode >>
                                                                                                                  ELSE /\ IF ops[idx] \notin {"null", "@"}
                                                                                                                             THEN /\ PrintT("Incorrect selection from LAMBDA")
                                                                                                                                  /\ IF debug
                                                                                                                                        THEN /\ idx' = idx
                                                                                                                                             /\ pc' = "Lbl_58"
                                                                                                                                        ELSE /\ pc' = "Done"
                                                                                                                                             /\ UNCHANGED idx
                                                                                                                                  /\ UNCHANGED << params, 
                                                                                                                                                  allArgs, 
                                                                                                                                                  curNode >>
                                                                                                                             ELSE /\ IF /\ ops[idx] = "null"
                                                                                                                                        /\ Len(args[idx]) # Len(opNode'.params)
                                                                                                                                        THEN /\ PrintT("Incorrect number of arguments for LAMBDA")
                                                                                                                                             /\ IF debug
                                                                                                                                                   THEN /\ idx' = idx
                                                                                                                                                        /\ pc' = "Lbl_59"
                                                                                                                                                   ELSE /\ pc' = "Done"
                                                                                                                                                        /\ UNCHANGED idx
                                                                                                                                             /\ UNCHANGED << params, 
                                                                                                                                                             allArgs, 
                                                                                                                                                             curNode >>
                                                                                                                                        ELSE /\ params' = params \o opNode'.params
                                                                                                                                             /\ allArgs' = allArgs \o args[idx]
                                                                                                                                             /\ curNode' = Node[opNode'.body]
                                                                                                                                             /\ pc' = "Lbl_63"
                                                                                                                                             /\ UNCHANGED idx
                                                                                                       ELSE /\ IF curNode.kind \in {UserDefinedOpKind, BuiltInKind}
                                                                                                                  THEN /\ PrintT("Abort: should not have been able to choose this node.")
                                                                                                                       /\ IF debug
                                                                                                                             THEN /\ idx' = idx
                                                                                                                                  /\ pc' = "Lbl_60"
                                                                                                                             ELSE /\ pc' = "Done"
                                                                                                                                  /\ UNCHANGED idx
                                                                                                                       /\ UNCHANGED curNode
                                                                                                                  ELSE /\ IF curNode.kind \in {AtNodeKind, DecimalKind, NumeralKind, StringKind,
                                                                                                                                            FormalParamKind, ConstantDeclKind, VariableDeclKind,
                                                                                                                                            BoundSymbolKind}
                                                                                                                             THEN /\ PrintT("Selected part has no subexpression")
                                                                                                                                  /\ IF debug
                                                                                                                                        THEN /\ idx' = idx
                                                                                                                                             /\ pc' = "Lbl_61"
                                                                                                                                        ELSE /\ pc' = "Done"
                                                                                                                                             /\ UNCHANGED idx
                                                                                                                                  /\ UNCHANGED curNode
                                                                                                                             ELSE /\ IF curNode.kind = LabelKind
                                                                                                                                        THEN /\ curNode' = Node[curNode.body]
                                                                                                                                             /\ idx' = idx - 1
                                                                                                                                             /\ pc' = "Lbl_63"
                                                                                                                                        ELSE /\ PrintT("Unexpected node kind found in expression")
                                                                                                                                             /\ IF debug
                                                                                                                                                   THEN /\ idx' = idx
                                                                                                                                                        /\ pc' = "Lbl_62"
                                                                                                                                                   ELSE /\ pc' = "Done"
                                                                                                                                                        /\ UNCHANGED idx
                                                                                                                                             /\ UNCHANGED curNode
                                                                                                            /\ UNCHANGED << params, 
                                                                                                                            allArgs, 
                                                                                                                            opNode >>
                                                                                                 /\ UNCHANGED temp
                                                ELSE /\ PrintT("Bad value of mode")
                                                     /\ IF debug
                                                           THEN /\ idx' = idx
                                                                /\ pc' = "Lbl_68"
                                                           ELSE /\ pc' = "Done"
                                                                /\ UNCHANGED idx
                                                     /\ UNCHANGED << params, 
                                                                     allArgs, 
                                                                     curNode, 
                                                                     opNode, 
                                                                     temp >>
                                          /\ UNCHANGED newNode
                               /\ UNCHANGED tempArgs
               ELSE /\ IF curNode.kind = AssumeProveKind
                          THEN /\ PrintT("Selecting ASSUME/PROVE instead of expression")
                               /\ IF debug
                                     THEN /\ idx' = idx
                                          /\ pc' = "Lbl_70"
                                     ELSE /\ pc' = "Done"
                                          /\ UNCHANGED idx
                          ELSE /\ pc' = "Lbl_71"
                               /\ UNCHANGED idx
                    /\ UNCHANGED << params, allArgs, curNode, opNode, newNode, 
                                    temp, tempArgs >>
         /\ UNCHANGED << ops, args, expectedArity, substInPrefix, subExprOf, 
                         result, mode, prevMode, curContext, curName, 
                         opDefArityFound, opDefArgs, firstFindingOpName, 
                         newName, nodeArity >>

Lbl_69 == /\ pc = "Lbl_69"
          /\ idx' = idx + 1
          /\ pc' = "Lbl_2"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF newNode = null
               THEN /\ IF idx \geq Len(ops)
                          THEN /\ PrintT("Unknown operator")
                               /\ IF debug
                                     THEN /\ idx' = idx
                                          /\ pc' = "Lbl_4"
                                     ELSE /\ pc' = "Done"
                                          /\ UNCHANGED idx
                          ELSE /\ pc' = "Lbl_5"
                               /\ UNCHANGED idx
                    /\ UNCHANGED << curNode, curName >>
               ELSE /\ curNode' = newNode
                    /\ curName' = newName
                    /\ IF curNode'.kind \in
                              {UserDefinedOpKind, ThmOrAssumpDefKind,
                                 ModuleInstanceKind, ConstantDeclKind, VariableDeclKind,
                                 FormalParamKind, BuiltInKind, BoundSymbolKind}
                          THEN /\ IF curNode'.kind \in
                                          {ConstantDeclKind, VariableDeclKind, FormalParamKind,
                                           BuiltInKind, BoundSymbolKind}
                                     THEN /\ IF idx # 1
                                                THEN /\ PrintT("Abort: Impossible naming of declaration "
                                                                \o "or built-in operator.")
                                                     /\ IF debug
                                                           THEN /\ idx' = idx
                                                                /\ pc' = "Lbl_8"
                                                           ELSE /\ pc' = "Done"
                                                                /\ UNCHANGED idx
                                                ELSE /\ IF Len(ops) # 1
                                                           THEN /\ PrintT("Can't take subexpression of this")
                                                                /\ IF debug
                                                                      THEN /\ idx' = idx
                                                                           /\ pc' = "Lbl_9"
                                                                      ELSE /\ pc' = "Done"
                                                                           /\ UNCHANGED idx
                                                           ELSE /\ pc' = "Lbl_10"
                                                                /\ UNCHANGED idx
                                     ELSE /\ pc' = "Lbl_10"
                                          /\ UNCHANGED idx
                          ELSE /\ PrintT("Unexpected node kind")
                               /\ IF debug
                                     THEN /\ idx' = idx
                                          /\ pc' = "Lbl_20"
                                     ELSE /\ pc' = "Done"
                                          /\ UNCHANGED idx
         /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                         allArgs, subExprOf, result, mode, prevMode, 
                         curContext, opDefArityFound, opDefArgs, 
                         firstFindingOpName, opNode, newName, newNode, 
                         nodeArity, temp, tempArgs >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ newName' = IF IsName(ops[idx])
                         THEN IF curName = "" THEN ops[idx]
                                              ELSE curName \o "!" \o ops[idx]
                         ELSE null
         /\ IF /\ curName = ""
               /\ ~ IsName(ops[idx])
               THEN /\ PrintT("Need an operator or label name or step number here")
                    /\ IF debug
                          THEN /\ idx' = idx
                               /\ pc' = "Lbl_6"
                          ELSE /\ pc' = "Done"
                               /\ UNCHANGED idx
               ELSE /\ pc' = "Lbl_7"
                    /\ UNCHANGED idx
         /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                         allArgs, curNode, subExprOf, result, mode, prevMode, 
                         curContext, curName, opDefArityFound, opDefArgs, 
                         firstFindingOpName, opNode, newNode, nodeArity, temp, 
                         tempArgs >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ idx' = idx
         /\ Assert(FALSE, 
                   "Failure of assertion at line line 1892, column 38 of macro called at line 1956, column 13.")
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                         allArgs, curNode, subExprOf, result, mode, prevMode, 
                         curContext, curName, opDefArityFound, opDefArgs, 
                         firstFindingOpName, opNode, newName, newNode, 
                         nodeArity, temp, tempArgs >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ newNode' = (IF newName # null THEN LookUp(newName, curContext) ELSE null)
         /\ IF newName = null
               THEN /\ tempArgs' = tempArgs \o args[idx]
                    /\ idx' = idx + 1
               ELSE /\ TRUE
                    /\ UNCHANGED << idx, tempArgs >>
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                         allArgs, curNode, subExprOf, result, mode, prevMode, 
                         curContext, curName, opDefArityFound, opDefArgs, 
                         firstFindingOpName, opNode, newName, nodeArity, temp >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ idx' = idx
         /\ Assert(FALSE, 
                   "Failure of assertion at line line 1892, column 38 of macro called at line 1942, column 13.")
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                         allArgs, curNode, subExprOf, result, mode, prevMode, 
                         curContext, curName, opDefArityFound, opDefArgs, 
                         firstFindingOpName, opNode, newName, newNode, 
                         nodeArity, temp, tempArgs >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ nodeArity' = Arity(curNode)
          /\ tempArgs' = tempArgs \o args[idx]
          /\ IF expectedArity = 0
                THEN /\ IF opDefArityFound + Len(tempArgs') # nodeArity'
                           THEN /\ PrintT("Wrong number of arguments")
                                /\ IF debug
                                      THEN /\ idx' = idx
                                           /\ pc' = "Lbl_11"
                                      ELSE /\ pc' = "Done"
                                           /\ UNCHANGED idx
                           ELSE /\ pc' = "Lbl_12"
                                /\ UNCHANGED idx
                ELSE /\ IF expectedArity > 0
                           THEN /\ IF \E i \in 1..Len(curNode.params) :
                                         curNode.params[i].arity > 0
                                      THEN /\ PrintT("Higher-order operator selected "
                                                       \o "as operator argument")
                                           /\ IF debug
                                                 THEN /\ idx' = idx
                                                      /\ pc' = "Lbl_14"
                                                 ELSE /\ pc' = "Done"
                                                      /\ UNCHANGED idx
                                      ELSE /\ pc' = "Lbl_15"
                                           /\ UNCHANGED idx
                           ELSE /\ pc' = "Lbl_15"
                                /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, temp >>

Lbl_12 == /\ pc = "Lbl_12"
          /\ IF \E i \in 1..Len(tempArgs[idx]) :
                      Arity(Node[tempArgs[idx][i]]) #
                        ParamArity(curNode, i + opDefArityFound)
                THEN /\ PrintT("Argument has wrong arity")
                     /\ IF debug
                           THEN /\ idx' = idx
                                /\ pc' = "Lbl_13"
                           ELSE /\ pc' = "Done"
                                /\ UNCHANGED idx
                     /\ UNCHANGED opDefArgs
                ELSE /\ opDefArgs' = opDefArgs \o tempArgs
                     /\ pc' = "Lbl_15"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_13 == /\ pc = "Lbl_13"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 1990, column 26.")
          /\ pc' = "Lbl_15"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_11 == /\ pc = "Lbl_11"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 1985, column 25.")
          /\ pc' = "Lbl_12"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_14 == /\ pc = "Lbl_14"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 1996, column 32.")
          /\ pc' = "Lbl_15"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_15 == /\ pc = "Lbl_15"
          /\ opDefArityFound' = nodeArity
          /\ IF curNode.kind \in {UserDefinedOpKind, ThmOrAssumpDefKind,
                                  ConstantDeclKind, VariableDeclKind,
                                  FormalParamKind, BoundSymbolKind}
                THEN /\ IF /\ curNode.kind = UserDefinedOpKind
                           /\ ~ curNode.defined
                           /\ ~ Len(ops) = 1
                           THEN /\ PrintT("Can't refer to subexpression of "
                                           \o "operator inside its definition")
                                /\ IF debug
                                      THEN /\ idx' = idx
                                           /\ pc' = "Lbl_16"
                                      ELSE /\ pc' = "Done"
                                           /\ UNCHANGED idx
                           ELSE /\ pc' = "Lbl_17"
                                /\ UNCHANGED idx
                ELSE /\ IF (idx = Len(ops))
                           THEN /\ PrintT("Operator name incomplete")
                                /\ IF debug
                                      THEN /\ idx' = idx
                                           /\ pc' = "Lbl_19"
                                      ELSE /\ pc' = "Done"
                                           /\ UNCHANGED idx
                           ELSE /\ pc' = "Lbl_21"
                                /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArgs, firstFindingOpName, 
                          opNode, newName, newNode, nodeArity, temp, tempArgs >>

Lbl_17 == /\ pc = "Lbl_17"
          /\ IF /\ firstFindingOpName
                /\ curNode.kind \in {UserDefinedOpKind, ThmOrAssumpDefKind}
                THEN /\ subExprOf' = curNode
                ELSE /\ TRUE
                     /\ UNCHANGED subExprOf
          /\ IF idx # Len(ops)
                THEN /\ params' = params \o curNode.params
                     /\ curName' = ""
                     /\ IF IsName(ops[idx+1])
                           THEN /\ mode' = "FollowingLabels"
                           ELSE /\ mode' = "FindingSubExpr"
                     /\ allArgs' = allArgs \o opDefArgs
                     /\ opDefArityFound' = 0
                     /\ opDefArgs' = << >>
                     /\ newNode' = Node[curNode.body]
                     /\ pc' = "Lbl_18"
                ELSE /\ pc' = "Lbl_21"
                     /\ UNCHANGED << params, allArgs, mode, curName, 
                                     opDefArityFound, opDefArgs, newNode >>
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, curNode, 
                          result, idx, prevMode, curContext, 
                          firstFindingOpName, opNode, newName, nodeArity, temp, 
                          tempArgs >>

Lbl_18 == /\ pc = "Lbl_18"
          /\ IF newNode.kind = SubstInKind
                THEN /\ substInPrefix' = substInPrefix \o <<newNode>>
                     /\ newNode' = Node[newNode.body]
                     /\ pc' = "Lbl_18"
                     /\ UNCHANGED curNode
                ELSE /\ IF mode = "FindingSubExpr"
                           THEN /\ curNode' = newNode
                           ELSE /\ TRUE
                                /\ UNCHANGED curNode
                     /\ pc' = "Lbl_21"
                     /\ UNCHANGED << substInPrefix, newNode >>
          /\ UNCHANGED << ops, args, expectedArity, params, allArgs, subExprOf, 
                          result, idx, mode, prevMode, curContext, curName, 
                          opDefArityFound, opDefArgs, firstFindingOpName, 
                          opNode, newName, nodeArity, temp, tempArgs >>

Lbl_16 == /\ pc = "Lbl_16"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2010, column 25.")
          /\ pc' = "Lbl_17"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_19 == /\ pc = "Lbl_19"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2043, column 25.")
          /\ pc' = "Lbl_21"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ idx' = idx
         /\ Assert(FALSE, 
                   "Failure of assertion at line line 1892, column 38 of macro called at line 1974, column 26.")
         /\ pc' = "Lbl_10"
         /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                         allArgs, curNode, subExprOf, result, mode, prevMode, 
                         curContext, curName, opDefArityFound, opDefArgs, 
                         firstFindingOpName, opNode, newName, newNode, 
                         nodeArity, temp, tempArgs >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ idx' = idx
         /\ Assert(FALSE, 
                   "Failure of assertion at line line 1892, column 38 of macro called at line 1977, column 33.")
         /\ pc' = "Lbl_10"
         /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                         allArgs, curNode, subExprOf, result, mode, prevMode, 
                         curContext, curName, opDefArityFound, opDefArgs, 
                         firstFindingOpName, opNode, newName, newNode, 
                         nodeArity, temp, tempArgs >>

Lbl_20 == /\ pc = "Lbl_20"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2046, column 9.")
          /\ pc' = "Lbl_21"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_21 == /\ pc = "Lbl_21"
          /\ prevMode' = "FindingOpName"
          /\ pc' = "Lbl_69"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, idx, mode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_23 == /\ pc = "Lbl_23"
          /\ curNode' = newNode
          /\ IF expectedArity = 0
                THEN /\ IF Len(args[idx]) # curNode'.arity
                           THEN /\ PrintT("bad arity")
                                /\ IF debug
                                      THEN /\ idx' = idx
                                           /\ pc' = "Lbl_24"
                                      ELSE /\ pc' = "Done"
                                           /\ UNCHANGED idx
                           ELSE /\ pc' = "Lbl_25"
                                /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_28"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_25 == /\ pc = "Lbl_25"
          /\ IF \E i \in 1..Len(args[idx]) :
                    Arity(Node[args[idx][i]]) # 0
                THEN /\ PrintT("Operator argument given to label")
                     /\ IF debug
                           THEN /\ idx' = idx
                                /\ pc' = "Lbl_26"
                           ELSE /\ pc' = "Done"
                                /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_27"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_26 == /\ pc = "Lbl_26"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2068, column 20.")
          /\ pc' = "Lbl_27"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_27 == /\ pc = "Lbl_27"
          /\ allArgs' = allArgs \o args[idx]
          /\ pc' = "Lbl_28"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          curNode, subExprOf, result, idx, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_24 == /\ pc = "Lbl_24"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2064, column 20.")
          /\ pc' = "Lbl_25"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_28 == /\ pc = "Lbl_28"
          /\ params' = params \o curNode.params
          /\ IF /\ idx < Len(ops)
                /\ ~IsName(ops[idx+1])
                THEN /\ mode' = "FindingSubExpr"
                ELSE /\ TRUE
                     /\ UNCHANGED mode
          /\ IF \/ mode' = "FindingSubExpr"
                \/ idx = Len(ops)
                THEN /\ curNode' = Node[curNode.body]
                ELSE /\ TRUE
                     /\ UNCHANGED curNode
          /\ prevMode' = "FollowingLabels"
          /\ pc' = "Lbl_69"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, allArgs, 
                          subExprOf, result, idx, curContext, curName, 
                          opDefArityFound, opDefArgs, firstFindingOpName, 
                          opNode, newName, newNode, nodeArity, temp, tempArgs >>

Lbl_22 == /\ pc = "Lbl_22"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2059, column 13.")
          /\ pc' = "Lbl_23"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_63 == /\ pc = "Lbl_63"
          /\ IF idx # Len(ops)
                THEN /\ IF IsName(ops[idx+1])
                           THEN /\ pc' = "Lbl_64"
                                /\ UNCHANGED idx
                           ELSE /\ IF ops[idx+1] = ":"
                                      THEN /\ PrintT("!: should not follow an operand selector")
                                           /\ IF debug
                                                 THEN /\ idx' = idx
                                                      /\ pc' = "Lbl_66"
                                                 ELSE /\ pc' = "Done"
                                                      /\ UNCHANGED idx
                                      ELSE /\ pc' = "Lbl_67"
                                           /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_67"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_64 == /\ pc = "Lbl_64"
          /\ IF curNode.kind = LabelKind
                THEN /\ curNode' = Node[curNode.body]
                     /\ pc' = "Lbl_64"
                     /\ UNCHANGED << idx, mode, curContext, firstFindingOpName >>
                ELSE /\ IF curNode.kind = LetInKind
                           THEN /\ curContext' = curNode.context
                                /\ mode' = "FindingOpName"
                                /\ firstFindingOpName' = FALSE
                                /\ pc' = "Lbl_67"
                                /\ UNCHANGED idx
                           ELSE /\ PrintT("A name not following the selector of a LET")
                                /\ IF debug
                                      THEN /\ idx' = idx
                                           /\ pc' = "Lbl_65"
                                      ELSE /\ pc' = "Done"
                                           /\ UNCHANGED idx
                                /\ UNCHANGED << mode, curContext, 
                                                firstFindingOpName >>
                     /\ UNCHANGED curNode
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, prevMode, curName, 
                          opDefArityFound, opDefArgs, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_65 == /\ pc = "Lbl_65"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2294, column 26.")
          /\ pc' = "Lbl_67"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_66 == /\ pc = "Lbl_66"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2297, column 26.")
          /\ pc' = "Lbl_67"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_67 == /\ pc = "Lbl_67"
          /\ prevMode' = "FindingSubExpr"
          /\ pc' = "Lbl_69"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, idx, mode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_29 == /\ pc = "Lbl_29"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2091, column 14.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_30 == /\ pc = "Lbl_30"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2098, column 14.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_31 == /\ pc = "Lbl_31"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2110, column 17.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_33 == /\ pc = "Lbl_33"
          /\ curNode' = Node[curNode.operands[temp]]
          /\ IF \/ curNode'.kind # OpApplKind
                \/ Node[curNode'.operator].kind # BuiltInKind
                \/ Node[curNode'.operator].name # "$Pair"
                THEN /\ PrintT("Expecting $Pair(...)")
                     /\ IF debug
                           THEN /\ idx' = idx
                                /\ pc' = "Lbl_34"
                           ELSE /\ pc' = "Done"
                                /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_35"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_35 == /\ pc = "Lbl_35"
          /\ curNode' = Node[curNode.operands[2]]
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, idx, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_34 == /\ pc = "Lbl_34"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2131, column 18.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_32 == /\ pc = "Lbl_32"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2125, column 18.")
          /\ pc' = "Lbl_33"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_37 == /\ pc = "Lbl_37"
          /\ temp' = ArgNum( ops[idx], Len(curNode.operands))
          /\ IF temp' = -1
                THEN /\ PrintT("Incorrect subexpression name")
                     /\ IF debug
                           THEN /\ idx' = idx
                                /\ pc' = "Lbl_38"
                           ELSE /\ pc' = "Done"
                                /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_39"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, tempArgs >>

Lbl_38 == /\ pc = "Lbl_38"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2145, column 18.")
          /\ pc' = "Lbl_39"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_39 == /\ pc = "Lbl_39"
          /\ curNode' = Node[curNode.operands[temp]]
          /\ IF \/ curNode'.kind # OpApplKind
                \/ Node[curNode'.operator].kind # BuiltInKind
                \/ Node[curNode'.operator].name # "$Pair"
                THEN /\ PrintT("Expecting $Pair(...)")
                     /\ IF debug
                           THEN /\ idx' = idx
                                /\ pc' = "Lbl_40"
                           ELSE /\ pc' = "Done"
                                /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_41"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_40 == /\ pc = "Lbl_40"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2151, column 18.")
          /\ pc' = "Lbl_41"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_41 == /\ pc = "Lbl_41"
          /\ idx' = idx+1
          /\ temp' = ArgNum(ops[idx'], 2)
          /\ IF temp' = -1
                THEN /\ PrintT("Incorrect subexpression name")
                     /\ IF debug
                           THEN /\ pc' = "Lbl_42"
                           ELSE /\ pc' = "Done"
                ELSE /\ pc' = "Lbl_44"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, tempArgs >>

Lbl_42 == /\ pc = "Lbl_42"
          /\ idx' = idx
          /\ pc' = "Lbl_43"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_43 == /\ pc = "Lbl_43"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2156, column 18.")
          /\ pc' = "Lbl_44"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_44 == /\ pc = "Lbl_44"
          /\ curNode' = Node[curNode.operands[temp]]
          /\ IF curNode' = null
                THEN /\ PrintT("Selecting OTHER")
                     /\ IF debug
                           THEN /\ idx' = idx
                                /\ pc' = "Lbl_45"
                           ELSE /\ pc' = "Done"
                                /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_63"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_45 == /\ pc = "Lbl_45"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2160, column 18.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_36 == /\ pc = "Lbl_36"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2141, column 18.")
          /\ pc' = "Lbl_37"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_47 == /\ pc = "Lbl_47"
          /\ curNode' = Node[curNode.operands[temp]]
          /\ IF temp > 1
                THEN /\ IF \/ curNode'.kind # OpApplKind
                           \/ Node[curNode'.operator].kind # BuiltInKind
                           \/ Node[curNode'.operator].name # "$Pair"
                           THEN /\ PrintT("Unexpected expression node found.")
                                /\ IF debug
                                      THEN /\ idx' = idx
                                           /\ pc' = "Lbl_48"
                                      ELSE /\ pc' = "Done"
                                           /\ UNCHANGED idx
                           ELSE /\ pc' = "Lbl_49"
                                /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_63"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_49 == /\ pc = "Lbl_49"
          /\ curNode' = Node[curNode.operands[2]]
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, idx, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_48 == /\ pc = "Lbl_48"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2179, column 26.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_46 == /\ pc = "Lbl_46"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2172, column 19.")
          /\ pc' = "Lbl_47"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_51 == /\ pc = "Lbl_51"
          /\ curNode' = Node[curNode.operands[temp]]
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, idx, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_50 == /\ pc = "Lbl_50"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2195, column 25.")
          /\ pc' = "Lbl_51"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_53 == /\ pc = "Lbl_53"
          /\ curNode' = Node[curNode.operands[1]]
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, idx, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_52 == /\ pc = "Lbl_52"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2220, column 32.")
          /\ pc' = "Lbl_53"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_54 == /\ pc = "Lbl_54"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2225, column 32.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_55 == /\ pc = "Lbl_55"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2232, column 12.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_56 == /\ pc = "Lbl_56"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2240, column 18.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_57 == /\ pc = "Lbl_57"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2255, column 9.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_58 == /\ pc = "Lbl_58"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2257, column 9.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_59 == /\ pc = "Lbl_59"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2260, column 9.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_60 == /\ pc = "Lbl_60"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2267, column 7.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_61 == /\ pc = "Lbl_61"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2272, column 10.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_62 == /\ pc = "Lbl_62"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2281, column 8.")
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_68 == /\ pc = "Lbl_68"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2303, column 8.")
          /\ pc' = "Lbl_69"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_70 == /\ pc = "Lbl_70"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2311, column 10.")
          /\ pc' = "Lbl_71"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_71 == /\ pc = "Lbl_71"
          /\ IF expectedArity < 0
                THEN /\ IF \/ prevMode # "FindingOpName"
                           \/ curNode.kind \notin {UserDefinedOpKind, ThmOrAssumpDefKind}
                           THEN /\ PrintT("Should have selected a definition, but didn't.")
                                /\ IF debug
                                      THEN /\ idx' = idx
                                           /\ pc' = "Lbl_72"
                                      ELSE /\ pc' = "Done"
                                           /\ UNCHANGED idx
                           ELSE /\ pc' = "Lbl_73"
                                /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_74"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_73 == /\ pc = "Lbl_73"
          /\ result' = curNode
          /\ pc' = "Finished"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, idx, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_72 == /\ pc = "Lbl_72"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2317, column 17.")
          /\ pc' = "Lbl_73"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_74 == /\ pc = "Lbl_74"
          /\ IF expectedArity > 0
                THEN /\ temp' = (Len(params) + IF \/ prevMode = "FindingOpName"
                                                  \/ curNode.kind = OpArgKind
                                                 THEN Arity(curNode)
                                                 ELSE 0)
                     /\ IF expectedArity # temp'
                           THEN /\ PrintT("Expect arity = " \o ToString(expectedArity)
                                              \o ", but found arity = " \o ToString(temp'))
                                /\ IF debug
                                      THEN /\ idx' = idx
                                           /\ pc' = "Lbl_75"
                                      ELSE /\ pc' = "Done"
                                           /\ UNCHANGED idx
                           ELSE /\ pc' = "Lbl_76"
                                /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_76"
                     /\ UNCHANGED << idx, temp >>
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, tempArgs >>

Lbl_75 == /\ pc = "Lbl_75"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2329, column 18.")
          /\ pc' = "Lbl_76"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_76 == /\ pc = "Lbl_76"
          /\ IF /\ prevMode = "FindingOpName"
                /\ Len(params) + Len(substInPrefix) > 0
                THEN /\ temp' = [i \in 1..Len(curNode.params) |->
                                            [curNode.params[i] EXCEPT !.name = "New " \o @]]
                     /\ curNode' = [kind     |-> OpApplKind,
                                    operands |-> temp',
                                    operator |-> curNode,
                                    unboundedBoundSymbols |-> <<>>,
                                    boundedBoundSymbols |-> << >>,
                                    ranges |-> << >>]
                     /\ params' = params \o temp'
                     /\ allArgs' = allArgs \o opDefArgs
                ELSE /\ TRUE
                     /\ UNCHANGED << params, allArgs, curNode, temp >>
          /\ IF curNode'.kind = OpArgKind
                THEN /\ IF expectedArity = 0
                           THEN /\ PrintT("Selected Operator Argument when expression expected.")
                                /\ IF debug
                                      THEN /\ idx' = idx
                                           /\ pc' = "Lbl_77"
                                      ELSE /\ pc' = "Done"
                                           /\ UNCHANGED idx
                           ELSE /\ IF expectedArity # Len(params') + curNode'.arity
                                      THEN /\ PrintT("Selected operator has wrong arity.")
                                           /\ IF debug
                                                 THEN /\ idx' = idx
                                                      /\ pc' = "Lbl_78"
                                                 ELSE /\ pc' = "Done"
                                                      /\ UNCHANGED idx
                                      ELSE /\ IF Len(params') + Len(substInPrefix) > 0
                                                 THEN /\ pc' = "Lbl_79"
                                                 ELSE /\ pc' = "Lbl_80"
                                           /\ UNCHANGED idx
                ELSE /\ pc' = "Lbl_80"
                     /\ UNCHANGED idx
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, subExprOf, 
                          result, mode, prevMode, curContext, curName, 
                          opDefArityFound, opDefArgs, firstFindingOpName, 
                          opNode, newName, newNode, nodeArity, tempArgs >>

Lbl_77 == /\ pc = "Lbl_77"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2363, column 12.")
          /\ pc' = "Lbl_80"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_78 == /\ pc = "Lbl_78"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2365, column 12.")
          /\ pc' = "Lbl_80"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_79 == /\ pc = "Lbl_79"
          /\ temp' = [i \in 1..curNode.arity |->
                       [name |-> "NewParam" \o NumToString(i),
                        arity |-> 0]]
          /\ curNode' = [kind     |-> OpApplKind,
                         operands |-> temp',
                         operator |-> Node[curNode.op],
                         unboundedBoundSymbols |-> <<>>,
                         boundedBoundSymbols |-> << >>,
                         ranges |-> << >>]
          /\ params' = params \o temp'
          /\ pc' = "Lbl_80"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, allArgs, 
                          subExprOf, result, idx, mode, prevMode, curContext, 
                          curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, tempArgs >>

Lbl_80 == /\ pc = "Lbl_80"
          /\ IF curNode.kind \in {UserDefinedOpKind, ConstantDeclKind, VariableDeclKind,
                                  FormalParamKind, BuiltInKind, BoundSymbolKind,
                                  ThmOrAssumpDefKind}
                THEN /\ IF expectedArity > 0
                           THEN /\ result' = [kind  |-> OpArgKind,
                                              name  |-> curNode.name,
                                              op    |-> curNode,
                                              arity |-> expectedArity]
                           ELSE /\ IF expectedArity = 0
                                      THEN /\ result' = [kind |-> OpApplKind,
                                                         operands |-> opDefArgs,
                                                         operator |-> curNode,
                                                         unboundedBoundSymbols |-> <<>>,
                                                         boundedBoundSymbols |-> << >>,
                                                         ranges |-> << >>,
                                                         subExprOf |-> subExprOf]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED result
                     /\ pc' = "Finished"
                     /\ UNCHANGED temp
                ELSE /\ IF curNode.kind = OpArgKind
                           THEN /\ result' = curNode
                                /\ pc' = "Finished"
                                /\ UNCHANGED temp
                           ELSE /\ temp' = Len(substInPrefix)
                                /\ pc' = "Lbl_81"
                                /\ UNCHANGED result
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, idx, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, tempArgs >>

Lbl_81 == /\ pc = "Lbl_81"
          /\ IF temp > 0
                THEN /\ curNode' = [kind  |-> SubstInKind,
                                    body  |-> curNode ,
                                    subst |-> substInPrefix[temp].subst ]
                     /\ temp' = temp - 1
                     /\ pc' = "Lbl_81"
                     /\ UNCHANGED idx
                ELSE /\ IF expectedArity > 0
                           THEN /\ IF Len(params) # expectedArity
                                      THEN /\ PrintT("Selection has wrong arity")
                                           /\ IF debug
                                                 THEN /\ idx' = idx
                                                      /\ pc' = "Lbl_82"
                                                 ELSE /\ pc' = "Done"
                                                      /\ UNCHANGED idx
                                      ELSE /\ pc' = "Lbl_83"
                                           /\ UNCHANGED idx
                           ELSE /\ IF Len(params) # Len(allArgs)
                                      THEN /\ PrintT("Abort: number of params # num of args")
                                           /\ IF debug
                                                 THEN /\ idx' = idx
                                                      /\ pc' = "Lbl_84"
                                                 ELSE /\ pc' = "Done"
                                                      /\ UNCHANGED idx
                                      ELSE /\ pc' = "Lbl_85"
                                           /\ UNCHANGED idx
                     /\ UNCHANGED << curNode, temp >>
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, tempArgs >>

Lbl_83 == /\ pc = "Lbl_83"
          /\ result' = [kind |-> OpArgKind,
                        op   |-> [kind    |-> UserDefinedOpKind,
                                  name    |-> "LAMBDA",
                                  body    |-> curNode,
                                  params  |-> params,
                                  arity   |-> Len(params),
                                  defined |-> TRUE,
                                  source  |-> null],
                        name |-> "LAMBDA"]
          /\ pc' = "Finished"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, idx, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_85 == /\ pc = "Lbl_85"
          /\ IF Len(params) = 0
                THEN /\ result' = [kind  |-> LabelKind,
                                   name  |-> "$Subexpression",
                                   arity  |-> 0,
                                   params |-> << >>,
                                   body   |-> curNode,
                                   subExprOf |-> subExprOf]
                ELSE /\ result' = [kind     |-> OpApplKind,
                                   operator |-> [kind    |-> UserDefinedOpKind,
                                                 name    |-> "LAMBDA",
                                                 body    |-> curNode,
                                                 params  |-> params,
                                                 arity   |-> Len(params),
                                                 defined |-> TRUE,
                                                 source  |-> null],
                                   operands |-> allArgs,
                                   unboundedBoundSymbols |-> <<>>,
                                   boundedBoundSymbols |-> << >>,
                                   ranges |-> << >>,
                                   subExprOf |-> subExprOf]
          /\ pc' = "Finished"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, idx, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_82 == /\ pc = "Lbl_82"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2431, column 22.")
          /\ pc' = "Lbl_83"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Lbl_84 == /\ pc = "Lbl_84"
          /\ idx' = idx
          /\ Assert(FALSE, 
                    "Failure of assertion at line line 1892, column 38 of macro called at line 2443, column 22.")
          /\ pc' = "Lbl_85"
          /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                          allArgs, curNode, subExprOf, result, mode, prevMode, 
                          curContext, curName, opDefArityFound, opDefArgs, 
                          firstFindingOpName, opNode, newName, newNode, 
                          nodeArity, temp, tempArgs >>

Finished == /\ pc = "Finished"
            /\ PrintT("Result: ")
            /\ PrintT(result)
            /\ pc' = "Done"
            /\ UNCHANGED << ops, args, expectedArity, substInPrefix, params, 
                            allArgs, curNode, subExprOf, result, idx, mode, 
                            prevMode, curContext, curName, opDefArityFound, 
                            opDefArgs, firstFindingOpName, opNode, newName, 
                            newNode, nodeArity, temp, tempArgs >>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_69 \/ Lbl_3 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7
           \/ Lbl_4 \/ Lbl_10 \/ Lbl_12 \/ Lbl_13 \/ Lbl_11 \/ Lbl_14 \/ Lbl_15
           \/ Lbl_17 \/ Lbl_18 \/ Lbl_16 \/ Lbl_19 \/ Lbl_8 \/ Lbl_9 \/ Lbl_20
           \/ Lbl_21 \/ Lbl_23 \/ Lbl_25 \/ Lbl_26 \/ Lbl_27 \/ Lbl_24 \/ Lbl_28
           \/ Lbl_22 \/ Lbl_63 \/ Lbl_64 \/ Lbl_65 \/ Lbl_66 \/ Lbl_67 \/ Lbl_29
           \/ Lbl_30 \/ Lbl_31 \/ Lbl_33 \/ Lbl_35 \/ Lbl_34 \/ Lbl_32 \/ Lbl_37
           \/ Lbl_38 \/ Lbl_39 \/ Lbl_40 \/ Lbl_41 \/ Lbl_42 \/ Lbl_43 \/ Lbl_44
           \/ Lbl_45 \/ Lbl_36 \/ Lbl_47 \/ Lbl_49 \/ Lbl_48 \/ Lbl_46 \/ Lbl_51
           \/ Lbl_50 \/ Lbl_53 \/ Lbl_52 \/ Lbl_54 \/ Lbl_55 \/ Lbl_56 \/ Lbl_57
           \/ Lbl_58 \/ Lbl_59 \/ Lbl_60 \/ Lbl_61 \/ Lbl_62 \/ Lbl_68 \/ Lbl_70
           \/ Lbl_71 \/ Lbl_73 \/ Lbl_72 \/ Lbl_74 \/ Lbl_75 \/ Lbl_76 \/ Lbl_77
           \/ Lbl_78 \/ Lbl_79 \/ Lbl_80 \/ Lbl_81 \/ Lbl_83 \/ Lbl_85 \/ Lbl_82
           \/ Lbl_84 \/ Finished
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

NotDone == pc # "Done"
  (*************************************************************************)
  (* To print a trace of an execution that doesn't produce an error, add   *)
  (* "INVARIANT NotDone" to Subexpression.cfg .                            *)
  (*************************************************************************)
=============================================================================


************************* end file Subexpression.tla ****************************/

