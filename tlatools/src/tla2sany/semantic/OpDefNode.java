// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.


// last modified on Sat 28 June 2008 at  0:45:44 PST by lamport
/***************************************************************************
* The OpDefNode constructor is invoked only in semantic/Generator.java     *
* and configuration/Configuration.java.  The latter invokes it only to     *
* construct OpDefNode objects to represent the built-in TLA+ operators,    *
* which are put in the initial context.  (I don't remember why these were  *
* represented as OpDefNode objects rather than OpDecl objects in the       *
* spec.)                                                                   *
***************************************************************************/

/***************************************************************************
* For a recursive operator definition, the OpDefNode is created when the   *
* RECURSIVE statement is processed.  The syntax tree node returned by      *
* getTreeNode() is the one for the symbol's declaration in the RECURSIVE   *
* statement.  Only after processing the actual definition is the syntax    *
* tree node changed to the N_OperatorDefinition node.                      *
***************************************************************************/

/***************************************************************************
* To minimize the number of changes that must be made to the existing      *
* code, a lambda expression is represented as an OpDefNode of kind         *
* UserDefinedOpKind with name "LAMBDA".  To avoid putting this name in     *
* any symbol table, the constructor should be called for a lambda          *
* expression with the SymbolTable argument equal to null.                  *
***************************************************************************/

package tla2sany.semantic;

import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.st.Location;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.utilities.Vector;
import util.UniqueString;
import util.WrongInvocationException;

  /**
   * An OpDefNode can have one of the following kinds:                    
   *                                                                      
   *     ModuleInstanceKind                                               
   *        Represents a module instantiation name, such as the M         
   *        in  M(a, b) == INSTANCE ...                                   
   *                                                                      
   *     UserDefinedOpKind                                                
   *        Represents a user definition, for example the definition      
   *        of the symbol Foo in  Foo(A, B) == expr.                      
   *                                                                      
   *     BuiltInKind                                                      
   *        An imaginary declaration for a built-in operator of TLA+      
   *        such as \cup.                                                 
   *                                                                      
   *     NumberedProofStepKind
   *        Represents a numbered proof step that is not an assertion
   *        (so it doesn't get represented as a theorem).  It seems
   *        useful to keep those step numbers in the appropriate
   *        symbol tables in case the user refers to them even
   *        where inappropriate, if only to generate better error 
   *        messages.  Currently, the only legal reference to a proof 
   *        number of such a step is to a definition step in
   *        the DEF clause of a USE or HIDE step or a BY proof.
   *                                                                      
   * All TLA+ constructs such as record constructors that produce an      
   * expression are represented as OppApplNodes for special operators.    
   * There is an OpDefNode of kind BuiltInKind for each of these special  
   * operators.  The special operators are:                               
   *                                                                      
   *     $FcnApply                                                        
   *        f[x] is represented as $FcnApply(f, x), and f[x,y]            
   *        is represented as $FcnApply(f, <<x, y>>).                     
   *                                                                      
   *     $RcdSelect                                                       
   *        r.c is represented as $RcdSelect(r, "c").  Note that,         
   *        semantically, $RcdSelect(r, "c") is equivalent to             
   *        $FcnApply(r, "c").  But, a tool might want to handle          
   *        records differently from other functions for efficiency.      
   *                                                                      
   *     $NonRecursiveFcnSpec                                             
   *        The definition  f[x \in S] == exp  is represented as          
   *        $NonRecursiveFcnSpec(x, S, exp) if f does not appear in exp.  
   *                                                                      
   *     $RecursiveFcnSpec                                                
   *        Similar to $NonRecursiveFcnSpec, except for recursive         
   *        function definitions.                                         
   *                                                                      
   *     $Pair                                                            
   *     $RcdConstructor                                                  
   *        We represent [L1 |-> e1, L2 |-> e2] as                        
   *        $RcdConstructor($Pair("L1", e1), $Pair("L2", e2))             
   *                                                                      
   *     $SetOfRcds                                                          
   *        Used to represent [L1 : e1, L2 : e2] much like                
   *        $RcdConstructor.                                              
   *                                                                      
   *     $Except                                                          
   *     $Seq                                                             
   *        We represent [f EXCEPT ![a].b[q] = c, ![d,u][v] = e]          
   *        as $Except(f, $Pair( $Seq(a, "b", q), c ),                     
   *                      $Pair( $Seq(<<d,u>>, v), e )).                   
   *        We are representing the equivalent expressions                
   *        [r EXCEPT !["a"] = b] and [r EXCEPT !.a = b] the same, even   
   *        though we represent r["a"] and r.a differently.  This         
   *        inconsistency resulted from a compromise between supporting   
   *        efficient implementation and keeping the api simple.  If      
   *        consistency is desired, we should probably eliminate          
   *        $RcdSelect.                                                   
   *                                                                      
   *     $Tuple                                                           
   *        We represent <<a, b, c>> as $Tuple(a, b, c).                  
   *                                                                      
   *     $CartesianProd                                                   
   *        Represents  A \X B \X C  as  $CartesianProd(A, B, C)          
   *                                                                      
   *     $BoundedChoose                                                   
   *        Represents CHOOSE x \in S : P                                 
   *                                                                      
   *     $UnboundedChoose                                                 
   *        Represents CHOOSE x : P.                                      
   *                                                                      
   *     $BoundedForall                                                   
   *        Represents \A x \in S : P.                                    
   *                                                                      
   *     $UnboundedForall                                                 
   *        Represents \A x : P.                                          
   *                                                                      
   *     $BoundedExists                                                   
   *        Represents \E x \in S : P.                                    
   *                                                                      
   *     $UnboundedExists                                                 
   *        Represents \E x : P.                                          
   *                                                                      
   *     $SetEnumerate                                                    
   *        Represents {a, b, c}.                                         
   *                                                                      
   *     $SubsetOf                                                        
   *        Represents {x \in S : p}.                                     
   *                                                                      
   *     $SetOfAll                                                        
   *        Represents {e : x \in S}.                                     
   *                                                                      
   *     $FcnConstructor                                                  
   *        Represents [x \in S |-> e].                                   
   *                                                                      
   *     $SetOfFcns                                                       
   *        Represents [S -> T].                                          
   *                                                                      
   *     $IfThenElse                                                      
   *     $ConjList                                                        
   *     $DisjList                                                        
   *         These are fairly obvious.                                    
   *                                                                      
   *     $Case                                                            
   *        We represent CASE p1 -> e1 [] p2 -> e2 as                     
   *        $Case( $Pair(p1, e1), $Pair(p2, e2) ) and we represent        
   *        CASE p1 -> e1 [] p2 -> e2 [] OTHER -> e3  as                  
   *        $Case( $Pair(p1, e1), $Pair(p2, e2), $Pair(null, e3))         
   *                                                                      
   *     $SquareAct                                                       
   *        We represent [A]_e as $SquareAct(A, e).                       
   *                                                                      
   *     $AngleAct                                                        
   *        We represent <<A>>_e as $AngleAct(A, e).                      
   *                                                                      
   *     $WF(e, A)                                                        
   *     $SF(e, A)                                                        
   *        We represent WF_e(A) as $WF(e, A), etc.                       
   *                                                                      
   *     $TemporalExists                                                  
   *     $TemporalForall                                                  
   *        Represent \EE and \AA.        
   *        
   *  On 24 Oct 2012, LL added the AnyDefNode interface and made the OpDefNode 
   *  class implement it.  He also added the getIsLeibnizArg method.  See
   *  the comments in AnyDefNode.java for an explanation.
   */

public class OpDefNode extends OpDefOrDeclNode 
         implements OpDefOrLabelNode, AnyDefNode {


/*************************************************************************
* The fields.                                                            *
*************************************************************************/
  private boolean           local  = false;  
     // Is this definition local to the module?
  private ExprNode          body   = null;   
    // the expression that is the def'n of the operator
  private FormalParamNode[] params = null;   
    // Array of FormalParamNodes that this operator takes

  private LevelNode stepNode = null;
    /***********************************************************************
    * For a NumberedProofStepKind, this is the step node it's numbering.   *
    * It can be a DefStepNode, UseOrHideNode, or InstanceNode.  Otherwise, *
    * it is null.                                                          *
    ***********************************************************************/
  
  /** 
   * This is the module from which this definition is ultimately obtained.
   * The field originallyDefinedInModule purports to be that, but when the
   * definition is instantiated, this can create a new OpDefNode whose
   * originallyDefinedInModule field is the instantiating module.  In that
   * case, the sourceModule field is the same as that of the OpDefNode of
   * the instantiated definition.  Hence, this really is the module containing
   * the ultimate source of the definition.
   * 
   * This field added by LL on 1 Nov 2012 to fix a bug in which the exact 
   * same definition imported by two different routes generated a warning.
   * (This warning was originally harmless, but it became a problem when
   * it was decided that the Toolbox would regard warnings as errors.) 
   * 
   */
//  private ModuleNode sourceModule = null ;
//
//  public ModuleNode getSourceModule() {
//      return sourceModule ;
//  }
  
  /*************************************************************************
  * The following fields state if an operator is recursively defined, and  *
  * give some potentially useful information having to do with recursive   *
  * operator definitions.                                                  *
  *************************************************************************/
  int letInLevel = -1 ;
    /***********************************************************************
    * The let/in level of a node is 0 if it does not occur within a        *
    * LET/IN statement, and it has level i > 0 if it occurs directly       *
    * within a LET/IN statement that occurs at level i-1.                  *
    ***********************************************************************/

  boolean inRecursive = false;
    /***********************************************************************
    * True iff this node's operator appears in a RECURSIVE statement.      *
    ***********************************************************************/
  public boolean getInRecursive() { return inRecursive; }
  
/***************************************************************************
* XXXXX The uses of "recursive section" in the names of the next two       *
* fields do not have the same meaning.  Hence, one of these names should   *
* be changed.                                                              *
***************************************************************************/

  boolean inRecursiveSection = false ;
    /***********************************************************************
    * This field is set true iff this node's operator appears in a         *
    * RECURSIVE statement, or if the definition represented by this OpDef  *
    * node comes between a RECURSIVE statement at the same let/in level    *
    * and the definition of some operator declared in that recursive       *
    * statement.                                                           *
    ***********************************************************************/

  int recursiveSection = -1 ;
    /***********************************************************************
    * A recursive section is any maximal region of the spec within which   *
    * some operator has been declared in a RECURSIVE statement but not     *
    * yet defined.  This field is positive iff the object represents a     *
    * definition that occurs within a recursive section.  (This can be     *
    * true iff inRecursiveSection = false because the definition can       *
    * occur in a LET that is within a recursive section but contains no    *
    * RECURSIVE statement.)  Two OpDefNode objects with the same           *
    * non-negative recursiveSection value appeared in the same recursive   *
    * section.                                                             *
    ***********************************************************************/

// The following fields (except for isDefined) were removed by LL on 7 Apr
// 2007 (after being added by LL).  They were to be used for computing and
// displaying the connected components in the dependency graph, as
// explained in the comments.  They may be added back later if those
// dependencies are ever computed.

//  OpDefNode nextDependency = null ;
    /***********************************************************************
    * When the complete semantic tree has been constructed this field has  *
    * the following property.                                              *
    *                                                                      *
    * For OpDefNode objects n1 and n2, we say that n1 depends on n2,       *
    * written n1 -> n2, iff the operator defined by n2 occurs in the       *
    * definition of b1, some operator with OpDefNode n3 such that either   *
    * n1=n3 or n1 -> n3.                                                   *
    *                                                                      *
    * Define the dependency graph to be the graph with nodes all           *
    * OpDefNode objects and with edges defined by ->.                      *
    *                                                                      *
    * Define a dependency component C to be a strongly connected           *
    * component of the dependency graph, except that C consists of a       *
    * single node n only if n -> n.  Thus, a node belongs to a dependency  *
    * component iff it is contained in some cycle in the dependency        *
    * graph.                                                               *
    *                                                                      *
    * If a node n occurs in a dependency component then all nodes in that  *
    * component can be found by following nextDependency pointers.  In     *
    * otherwords, the nodes in any dependency component can be ordered to  *
    * form a sequence <<s[1], ...  , s[k]>> such that s[i].nextDependency  *
    * = s[i+1] for 1 \leq i < k and s[k].nextDependency = s[1].            *
    *                                                                      *
    * A node n does not occur in a dependency cycle iff n.nextDependency   *
    * = null.                                                              *
    ***********************************************************************/
  
  /*************************************************************************
  * The following fields are used in constructing the semantic tree.  They *
  * are of no use when the tree has been constructed, but we don't bother  *
  * getting rid of them.  They're not private because they're used by      *
  * methods in semantic/Generator.java.                                    *
  *                                                                        *
  * The first field is used to check that an operator that is defined in   *
  * a RECURSIVE statement is defined exactly once.                         *
  *************************************************************************/
  boolean isDefined = false;
    /***********************************************************************
    * If the operator is declared in a RECURSIVE statement, then the       *
    * OpDefNode is created when the RECURSIVE statement is processed and   *
    * this field is set false.  It is set true when processing the         *
    * operator's actual definition.                                        *
    *                                                                      *
    * This is used in the obvious way to detect duplicate definitions of   *
    * the operator.  It is used as follows to detect if the operator was   *
    * declared in a RECURSIVE statement but never defined.  A stack of     *
    * counts of not-yet defined operators at different levels is kept so   *
    * that, upon finishing the processing of a LET/IN or of the entire     *
    * module, we can detect that some operator has been declared but not   *
    * defined.  We can then use the data structure described by the        *
    * fields below constructed to compute dependency components to find    *
    * the undefined operator(s).                                           *
    ***********************************************************************/

  /*************************************************************************
  * The following fields are used to implement a version of Tarjan's       *
  * algorithm for computing connected-components that computes the         *
  * dependency components (and sets the nextDependency fields of the       *
  * nodes).  See the file semantic/Generator.java for a description of     *
  * this algorithm.                                                        *
  *************************************************************************/
//  boolean participating = false ;
    /***********************************************************************
    * True iff the node is participating in the current dependency         *
    * component computation.  An OpDefNode can appear in a connected       *
    * component only if it is represents a definition that appears in a    *
    * region where some operator has been declared in a RECURSIVE          *
    * statement but not yet defined.  This field is set to true if the     *
    * OpDefNode is constructed when this is the case.  The dependency      *
    * component computation is then run on all participating objects,      *
    * setting their participating fields false.                            *
    ***********************************************************************/

  /*************************************************************************
  * The remaining fields are meaningful, and have the indicated meaning,   *
  * only when participating = true.                                        *
  *************************************************************************/
//  Vector nbrs = null ;
    /***********************************************************************
    * This is a vector of OpDefNode objects containing all the OpDefNode   *
    * objects whose operators occur in the definition of this node's       *
    * operator.  The same object may appear multiple times.  Tarjan's      *
    * algorithm works with multiple copies (they're equivalent to          *
    * multiple arcs between the same two nodes), and it's easier and       *
    * faster to just add nodes to nbrs without checking if they're         *
    * already there.                                                       *
    ***********************************************************************/

//  int lowlink      = -1 ;
//  int dfs          = -1 ;
//  boolean examined = false;
    /***********************************************************************
    * These fields are used in Tarjan's algorithm.  See the file           *
    * Tarjan.tla for a +Cal version of the algorithm and an explanation    *
    * of what these fields are used for.                                   *
    ***********************************************************************/

    /***********************************************************************
    * The following field is used to implement the OpDefOrLabel interface. *
    * It is a hashtable of OpDefNode objects representing labels within    *
    * the body that are not within the scope of an inner label or LET      *
    * definition.                                                          *
    ***********************************************************************/
    private Hashtable labels = null ;    

    private OpDefNode source = null ;
      /*********************************************************************
      * If this OpDefNode was created through a chain of INSTANCEs, then   *
      * this field points to the original OpDefNode object from where it   *
      * came.  Otherwise, it equals null.  It is accessed with             *
      * getSource().                                                       *
      *********************************************************************/
      
/***************************************************************************
* The constructors.                                                        *
***************************************************************************/
  /* Used only for creating nullODN */
  public OpDefNode(UniqueString us) {
    super(us, 0, -2, null, null, SyntaxTreeNode.nullSTN); 
    if (st != null) {
      st.addSymbol(us, this);
    }
  }

  /* Invoked in configuration.Configuration for built-in ops */
  public OpDefNode(UniqueString us, int k, int ar, FormalParamNode[] parms,
                   boolean localness, ExprNode exp, ModuleNode oModNode,
                   SymbolTable symbolTable, TreeNode stn) {
    super(us, k, (parms == null ? -1 : parms.length), oModNode, symbolTable, stn);
    params = parms;
   
    // Create phony FormalParamNodes for built-in operators
    if ( arity >= 0 ) {
      for (int i = 0; i < params.length; i++ ) {
        params[i] = new FormalParamNode(UniqueString.uniqueStringOf("Formal_" + i),
                                        0, null, symbolTable, oModNode);
      }
    }
    if (st != null) {
      st.addSymbol(us, this);
    }
    isDefined = true ;
      /*********************************************************************
      * All built-in operators are obviously defined.                      *
      *********************************************************************/
  }   

  /* Invoked by ordinary operator definition. */
   /************************************************************************
   * This constructor is invoked only in semantic/Generator, by            *
   * the following methods:                                                *
   *                                                                       *
   *    processOperator (by call to startOpDefNode)                        *
   *       To produce a node for an operator definition, either at module  *
   *       level or in a LET/IN                                            *
   *                                                                       *
   *    processFunction                                                    *
   *       To produce a node for a function definition, either at module   *
   *       level or in a LET/IN                                            *
   *                                                                       *
   *    generateLambda                                                     *
   *       To produce a lambda expression                                  *
   *                                                                       *
   *    processModuleDefinition                                            *
   *       Twice to construct a clone of a node from the instantiated      *
   *       module.  (It also has another call to a differerent             *
   *       constructor--see below.)                                        *
   *                                                                       *
   *    generateInstance -                                                 *
   *       Three times, both times to construct a clone of a node from     *
   *       the instantiated module                                         *
   *                                                                       *
   * Note: the defined argument sets the isDefined field.  It is used      *
   * when the OpDefNode is being created before it is actually defined.    *
   * See semantic/Generator.java/startOpDefNode, and its uses.  This       *
   * argument was added by LL on 7 Apr 2007.                               *
   ************************************************************************/
   public OpDefNode(UniqueString us, 
                    int k,                   // The kind
                    FormalParamNode[] parms, 
                    boolean localness, 
                    ExprNode exp,             // The body
                    ModuleNode oModNode,      // Originally defining module.
                    SymbolTable symbolTable, 
                    TreeNode stn, 
                    boolean defined,
                    OpDefNode src             // The source                 
                   ) {
    super(us, k, (parms != null ? parms.length : 0), 
          oModNode, symbolTable, stn);
    this.local = localness;
    this.params = (parms != null ? parms : new FormalParamNode[0]);
    this.body = exp;
    this.isDefined = defined ;
    this.source = src ;
    /***********************************************************************
    * Initialize maxLevels to the least restrictive value and weights to   *
    * 0; initialize isLeibniz and all isLeibniz[i] to true.                *
    ***********************************************************************/
    this.maxLevels    = new int[this.params.length];
    this.weights      = new int[this.params.length];
    this.isLeibniz    = true;
    this.isLeibnizArg = new boolean[this.params.length];
    for (int i = 0 ; i < this.params.length ; i++) {
      this.maxLevels[i] = MaxLevel ;
      this.weights[i] = 0 ;
      this.isLeibnizArg[i] = true ;
      } ;

    if (st != null) {
      st.addSymbol(us, this);
    }
  }

  /* Used for ModuleInstance names */
  /*************************************************************************
  * This constructor is missing the following parameters that are present  *
  * in the preceding constructor:                                          *
  *    kind    - always ModuleInstanceKind,                                *
  *    body    - there is none                                             *
  *    defined - always true because it can't be declared RECURSIVE.       *
  *************************************************************************/
  public OpDefNode(UniqueString us, 
                   FormalParamNode[] parms, 
                   boolean localness, 
                   ModuleNode oModNode, 
                   SymbolTable symbolTable, 
                   TreeNode stn,
                   OpDefNode src  // the source
                  ) {
    super(us, ModuleInstanceKind, (parms == null ? -1 : parms.length), 
          oModNode, symbolTable, stn);
    this.params = parms;
    this.local = localness;
    this.source = src;
    if (st != null) {
      st.addSymbol(us, this);
    }
  }

  /*************************************************************************
  * Constructor for NumberedProofStepKind nodes.  It should never be       *
  * called with symbolTable null.                                          *
  *************************************************************************/
  public OpDefNode(UniqueString us,  LevelNode step, ModuleNode oModNode, 
                   SymbolTable symbolTable, TreeNode stn) {
    super(us, NumberedProofStepKind, 0, oModNode, symbolTable, stn) ;
    this.stepNode = step ;
    st.addSymbol(us, this);
   } 
  /*************************************************************************
  * The methods that return or check properties of the node.               *
  *************************************************************************/
  /**
   * When applied to a user-defined op node or a built-in op
   * with a fixed number of params, returns an array of the formal 
   * parameter nodes associated with this operator.  For example,
   * with
   *
   *   F(A(_,_), b, c) == A(b,c)
   *
   * it returns an array of length 3.
   * 
   * When applied to a module instance node, returns (new) parameter
   * nodes introduced by that module instance. For example, with
   *
   *   D(x,y) == INSTANCE FooMod WITH c <- +
   *
   * it returns an array of length 2.
   * 
   * When applied to a builtin op with a variable number of args, returns null.
   */
  public final FormalParamNode[] getParams() { return this.params; }

  /*************************************************************************
  * The setParams method is invoked in semantic/Generator.java to set the  *
  * params field for a node that was originally constructed with a dummy   *
  * field when processing a RECURSIVE declaration.                         *
  *************************************************************************/
  public final void setParams(FormalParamNode[] pms) { this.params = pms ;}


  /**
   * For a UserDefinedOp node, the getBody() method returns the
   * definition.  For other kinds of OpDefNodes, the method is 
   * meaningless and should return null.  For example, if nOp is the    
   * UserDefinedOp node for the operator Op defined by                  
   *                                                                    
   *    Op(a, b) == expr                                                
   *                                                                    
   * then nOp.getBody() is a ref to the ExprNode for expr.              
   *                                                                    
   * A tool can use the setBody method to change the definition of a
   * user-defined operator.  For example, TLC can implement the
   * replacement A <- B by setting the Body of A's UserDefinedOp node
   * to equal the Body of B's UserDefinedOp node.
   *                                                                    
   * The setBody method checks that body.getParent() equals the
   * current node, and raises an exception if it doesn't.
   */
  public final ExprNode getBody() { return this.body; }

  /**
   * Sets the body of this definition to the expression in body.  See
   * documentation for getBody();
   */
  /*************************************************************************
  * setBody() is also used by semantic/Generator.endOpDefNode.             *
  *************************************************************************/
  public final void setBody(ExprNode body) { this.body = body; }


  /*************************************************************************
  * Return the source node--the original OpDefNode from which this one     *
  * came.  It is different from this node iff the node was created by a    *
  * chain of instantiations.                                               *
  *************************************************************************/
  public final OpDefNode getSource() {
    return (this.source == null)? this : this.source ;
    }

  /**
   * Returns true iff this definition is declared LOCAL; definitions
   * that are in fact local, e.g. in LETs or inner modules, but that do not 
   * get declared so using the LOCAL modifier are NOT
   * local for this purpose.
   */
  public final boolean isLocal() { return this.local; }

  /**
   * Returns the arity of this operator, or -1 in the case of an operator
   * that takes a variable number of args.
   */
  public final int getArity() { return this.arity; } 

  public final LevelNode getStepNode() {return this.stepNode ;} 

  /**
   * This method tests whether an operand is a legal instance of an
   * operator being passed as argument to another operator
   */
  private boolean matchingOpArgOperand (ExprOrOpArgNode arg, int i) {
    return ((arg instanceof OpArgNode) &&
            params[i].getArity() == ((OpArgNode)arg).getArity());
  }

  /* This method shortens the match() method right after it */
  private boolean errReport(Location loc, String s) {
    errors.addError(loc, s);
    return false;
  }

  /**
   * This method is called at the end of OpApplNode constructors to
   * make sure the OpApplNode is correct by "matching" the argument
   * expressions against the parameter list requirements.
   *
   * The OpApplNode must have the same number of args as parameters,
   * unless the operator takes a variable number of parameters.  Also,
   * FormalParamNodes that specify operators of arity > 0 must be
   * matched by arguments that OpArgNodes of the appropriate arity.
   *
   * Constructor argument oan is an OpApplNode having THIS OpDefNode
   * as its operator part.  This method decides whether the arguments
   * to oan (i.e args[]) match the argument pattern required by THIS
   * OpDefNode in terms of arity, etc.
   */
  public final boolean match(OpApplNode oanParent, ModuleNode mn) throws AbortException {
    ExprOrOpArgNode[] args       = oanParent.getArgs();  // arg expr's that THIS operator is being applied to
    boolean           result     = true;                 // Remains true unless an error is detected
    boolean           tempResult = true;

    Location loc = (oanParent.getTreeNode() != null 
                    ? oanParent.getTreeNode().getLocation()
                    : null);

    // If THIS OpDefNode defines a module instance, then something is clearly wrong
    //   since a module instance node should not be under an OpApplNode 
    if (this.getKind() == ModuleInstanceKind) {
      errors.addError(loc, "Module instance identifier where operator should be.");
      result = false;
    }
    else if ( arity == -1 ) {
      // if THIS OpDefNode is for an operator that takes a variable number of args ...
      if ( args != null ) { // args vector may have length zero, but should not be null
        for ( int i = 0; i < args.length; i++ ) {
          if (args[i] instanceof OpArgNode) {
            errors.addError(loc, "Illegal expression used as argument " + (i+1) + 
                            " to operator '" + this.getName() + "'.");
            result = false;
          }
        }
      }
      else  {// null arg vector; supposedly cannot happen
        errors.addAbort(loc, "Internal error: null args vector for operator '" +
                        this.getName() + "' that should take variable number of args.",true);
      }
    }
    else {
      // It is an operator with a fixed number of params (possibly zero)
      if (args == null | params == null) { // args vector should never be null
        errors.addAbort(loc, "Internal error: Null args or params vector for operator '" + 
                        this.getName() + "'.", true);
      }
      else { // Normal case: params != null & args != null
        // if the number of args does not match the number of params 
        if (params.length != args.length) {
          errors.addError(loc, "Wrong number of arguments (" + args.length +
                          ") given to operator '" + this.getName() + "', \nwhich requires " +
                          params.length + " arguments.");
          result = false;
        }
        else {
          // we have the correct number of args
          // if the operator is a built-in op... (We separate out the logic for the builtin ops 
          // because there are no FormalParamNodes in the semantic tree to describe their arguments
          if ( this.getKind() == BuiltInKind ) {
            // for each arg, check that an expression, not an operator, is used as argument,
            // since no built-in operators take operators as arguments
            for ( int i = 0; i < params.length; i++ ) {
              if (args[i] instanceof OpArgNode) {
                errors.addError(loc, "Non-expression used as argument number " + (i + 1)
                                + " to BuiltIn operator '" 
                                + this.getName() + "'.");
                result = false;
              }
            }
          }
          else if ( this.getKind() == UserDefinedOpKind ) {
            // for each formal parameter to THIS OpDef
            for (int i = 0; i < params.length; i++ ) {
              // if i'th FormalParamNode shows arity == 0, then an expression is expected as argument
              if (params[i].getArity() == 0) {
                if (args[i] instanceof OpArgNode) {
                  // No ops can be passed in this parm position
                  errors.addError(loc, "Operator used in argument number " + (i+1) 
                                  + " has incorrect number of arguments.");
                  result = false;
                }
              }
              else if (params[i].getArity() > 0) {
                // OpArgNode of correct arity must be passed in this arg position
                if (! matchingOpArgOperand(args[i],i)) {
                  errors.addError(loc, "Argument number " + (i+1) + " to operator '"  
                                  + this.getName() + "' \nshould be a " + params[i].getArity() 
                                  + "-parameter operator.");
                  result = false;
                }
              } else { // if params[i].getArity() < 0
                errors.addError(loc,
                                "Internal error: Operator '" + this.getName() +
                                "' indicates that it requires \na negative number of arguments.");
              }
            } // end for
          }
          else {
            errors.addAbort(null,
                            "Internal error: operator neither BuiltIn nor UserDefined" +
                            " \nin call to OpDefNode.match()", true);
          }
        }
      } // end "normal case"
    } // end "arity != -1" case

    return result;
  } // end match()

  /*************************************************************************
  * The following methods implement the OpDefOrLabel interface.            *
  *                                                                        *
  * These are the same as the other classes that implement the interface.  *
  * There doesn't seem to be any easy way to write these methods only      *
  * once.                                                                  *
  *************************************************************************/
  public void setLabels(Hashtable ht) {labels = ht; }
    /***********************************************************************
    * Sets the set of labels.                                              *
    ***********************************************************************/
    
  public LabelNode getLabel(UniqueString us) {
    /***********************************************************************
    * If the hashtable `labels' contains a LabelNode with name `us',       *
    * then that LabelNode is returned; otherwise null is returned.         *
    ***********************************************************************/
    if (labels == null) {return null;} ;
    return (LabelNode) labels.get(us) ;    
   }

  public boolean addLabel(LabelNode odn) {
    /***********************************************************************
    * If the hashtable `labels' contains no OpDefNode with the same name   *
    * as odn, then odn is added to the set and true is return; else the    *
    * set is unchanged and false is returned.                              *
    ***********************************************************************/
    if (labels == null) {labels = new Hashtable(); } ;
    if (labels.containsKey(odn)) {return false ;} ;
    labels.put(odn.getName(), odn) ;
    return true;
   }
  
  public LabelNode[] getLabels() {
    /***********************************************************************
    * Returns an array containing the Label objects in the hashtable       *
    * `labels'.                                                            *
    ***********************************************************************/
    if (labels == null) {return new LabelNode[0];} ;
    Vector v = new Vector() ;
    Enumeration e = labels.elements() ;
    while (e.hasMoreElements()) { v.addElement(e.nextElement()); } ;
    LabelNode[] retVal = new LabelNode[v.size()] ;
    for (int i = 0 ; i < v.size() ; i++) 
      {retVal[i] = (LabelNode) v.elementAt(i); } ;
    return retVal ;
   }

  public Hashtable  getLabelsHT() {
    /***********************************************************************
    * Return the labels field.  Used to "clone" an OpDefNode for module    *
    * instantiation.                                                       *
    ***********************************************************************/
    return labels ;
   }

  /*************************************************************************
  * The fields used for level checking.                                    *
  *************************************************************************/

// These fields are now present in all LevelNode subclasses
//  private boolean levelCorrect;
//  private int level;
//  private HashSet levelParams;
//  private SetOfLevelConstraints levelConstraints;
//  private SetOfArgLevelConstraints argLevelConstraints;
//  private HashSet argLevelParams;

  int[] maxLevels;
  int[] weights;
  int[][] minMaxLevel;
    /***********************************************************************
    * According to LevelSpec.tla, if this is the OpDefNode for the         *
    * definition of op, then op.minMaxLevel[i][k] is the minimum value of  *
    * oparg.maxLevels[k] for the i-th argument of Op.  Thus,               *
    * op.minMaxLevels[i] is a sequence whose length is the number of       *
    * arguments taken by the i-th argument of Op.  (It equals 0 if the     *
    * i-th argument of Op is not an operator argument.)                    *
    ***********************************************************************/

  boolean[] isLeibnizArg;
  boolean   isLeibniz;
    /***********************************************************************
    * If this is the OpDefNode for the definition of op, then              *
    * isLeibnizArg[i] is true iff the i-th argument of op is Leibniz, and  *
    * isLeibniz = \A i : isLeibnizArg[i]                                   *
    ***********************************************************************/
  /**
   * This "getters" for isLeibnizArg and isLeibniz were added by LL on 24 Oct 2012. 
   *  See the comments in AnyDefNode.java for an explanation of why.
   */
  public boolean[] getIsLeibnizArg() {
      return isLeibnizArg; 
  }
  public boolean getIsLeibniz() {
      return isLeibniz; 
  }
  
  
  private boolean[][][] opLevelCond;
    /***********************************************************************
    * According to LevelSpec.tla, if this is the OpDefNode for the         *
    * definition of op, then op.opLevelCond[i][j][k] is true iff           *
    * the i-th argument of op is an operator argument opArg, and the       *
    * definition of op contains an expression in which the j-th formal     *
    * parameter of the definition of op appears within the k-th argument   *
    * of opArg.                                                            *
    ***********************************************************************/
    
  /* Set the level information for this builtin operator. */
  public final void setBuiltinLevel(BuiltInLevel.Data d) {
    if (d.arity == -1) {
      if (d.argMaxLevels.length > 0) {     
        /*******************************************************************
        * This test added on 3 Aug 2007 because the newly-introduced       *
        * $Witness builtin operator has arity -1 but no arguments.         *
        *******************************************************************/
        this.maxLevels = new int[1];
        this.maxLevels[0] = d.argMaxLevels[0];
        this.weights = new int[1];
        this.weights[0] = d.argWeights[0];
        
       }
      else {
        this.maxLevels = new int[0];
        this.weights = new int[0];
       }
    }
    else {
      this.maxLevels = d.argMaxLevels;
      this.weights = d.argWeights;
    };

    /***********************************************************************
    * Set Leibniz fields.                                                  *
    ***********************************************************************/
    this.isLeibniz = true;
    this.isLeibnizArg = new boolean[d.argWeights.length] ;
    for (int i = 0 ; i < d.argWeights.length ; i++) {
      this.isLeibnizArg[i] = (d.argWeights[i] > 0) ;
      this.isLeibniz = this.isLeibniz && isLeibnizArg[i] ;
     } ;
    
    this.level              = d.opLevel;
    this.levelChecked       = 99 ;
      /*********************************************************************
      * Never need to level-check a built-in operator.                     *
      *********************************************************************/
// These are now the default values
//    this.levelCorrect        = true;
//    this.levelParams         = EmptySet;
//    this.levelConstraints    = EmptyLC;
//    this.argLevelConstraints = EmptyALC;
//    this.argLevelParams      = EmptySet;
  }
  
  public final boolean levelCheck(int itr) {
    if (   (this.levelChecked >= itr)
        || (    (! inRecursiveSection) 
             && (this.levelChecked > 0))) return this.levelCorrect;
      /*********************************************************************
      * Need only level-check the definition once if not in a recursive    *
      * section.                                                           *
      *********************************************************************/
    this.levelChecked = itr ;

    if (this.getKind() == NumberedProofStepKind) {
      /*********************************************************************
      * We should never have to level check a NumberedProofStepKind node,  *
      * but just in case some reorganization of things causes it to        *
      * happen...                                                          *
      *********************************************************************/
      LevelNode[] subs = new LevelNode[1] ;
      subs[0] = stepNode ;
      this.levelCorrect = this.stepNode.levelCheck(itr);
      return this.levelCheckSubnodes(itr, subs) ;
     }
    
    // Level check the body:
      this.levelCorrect = this.body.levelCheck(itr);
    /***********************************************************************
    * Modified for recursive checking so the level never decreases with    *
    * repeated computation.                                                *
    ***********************************************************************/
    // Calculate level information:
    this.level = Math.max(this.level, this.body.getLevel());

     SetOfLevelConstraints lcSet = this.body.getLevelConstraints();
    for (int i = 0; i < this.params.length; i++) {
      /*********************************************************************
      * Modified to never increase maxLevels[i].                           *
      *********************************************************************/
      Object plevel = lcSet.get(params[i]);
      if (plevel != null) {
        this.maxLevels[i] = Math.min(this.maxLevels[i],
                                     ((Integer)plevel).intValue());
      }
    }

   /************************************************************************
   * For handling of recursive level checking, we now modify the           *
   * computation of weights so they never get decreased.  (This is         *
   * probably not necessary.)                                              *
   ************************************************************************/
//    this.weights = new int[this.params.length];
    for (int i = 0; i < this.params.length; i++) {
      if (this.body.getLevelParams().contains(this.params[i])) {
        this.weights[i] = Math.max(this.weights[i], 1);
      }
    }

    this.minMaxLevel = new int[this.params.length][];
    SetOfArgLevelConstraints alcSet = this.body.getArgLevelConstraints();
    for (int i = 0; i < this.params.length; i++) {
      int alen = this.params[i].getArity();
      this.minMaxLevel[i] = new int[alen];
      for (int j = 0; j < alen; j++) {
        Object alevel = alcSet.get(new ParamAndPosition(this.params[i], j));
        if (alevel == null) {
          this.minMaxLevel[i][j] = MinLevel;
        }
        else {
          this.minMaxLevel[i][j] = ((Integer)alevel).intValue();
        }
      }
    }

    this.opLevelCond = new boolean[this.params.length][this.params.length][];
    HashSet alpSet = this.body.getArgLevelParams();
    for (int i = 0; i < this.params.length; i++) {
      for (int j = 0; j < this.params.length; j++) {
        this.opLevelCond[i][j] = new boolean[this.params[i].getArity()];
        for (int k = 0; k < this.params[i].getArity(); k++) {
          ArgLevelParam alp = new ArgLevelParam(this.params[i], k, this.params[j]);
          this.opLevelCond[i][j][k] = alpSet.contains(alp);
        }
      }
    }

    /***********************************************************************
    * Modified for recursive definition handling so levelParams increases  *
    * monotonically with multiple computations.                            *
    *                                                                      *
    * allParams and nonLeibnizParams are also handled in the same way.     *
    ***********************************************************************/
    this.levelParams.addAll(this.body.getLevelParams());
    this.allParams.addAll(this.body.getAllParams());
    this.nonLeibnizParams.addAll(this.body.getNonLeibnizParams());
    for (int i = 0; i < this.params.length; i++) {
      this.levelParams.remove(this.params[i]);
      this.allParams.remove(this.params[i]);
      if (this.nonLeibnizParams.contains(this.params[i])) {
        /*******************************************************************
        * The i-th argument is non-Leibniz if this.params[i] is in the     *
        * body's nonLeibnizParams hashset (and hence now in this node's    *
        * nonLeibnizParams hashset.                                        *
        *******************************************************************/
        this.nonLeibnizParams.remove(this.params[i]) ;
        this.isLeibnizArg[i] = false ;
        this.isLeibniz = false ;
       } ;
    }

    this.levelConstraints = (SetOfLevelConstraints)lcSet.clone();
    for (int i = 0; i < this.params.length; i++) {
      this.levelConstraints.remove(this.params[i]);
    }

    this.argLevelConstraints = (SetOfArgLevelConstraints)alcSet.clone();
    for (int i = 0; i < this.params.length; i++) {
      int alen = this.params[i].getArity();
      for (int j = 0; j < alen; j++) {
        this.argLevelConstraints.remove(new ParamAndPosition(this.params[i], j));
      }
    }

//    this.argLevelParams = new HashSet();
    Iterator iter = alpSet.iterator();
    while (iter.hasNext()) {
      ArgLevelParam alp = (ArgLevelParam)iter.next();
      if (!alp.op.occur(this.params) ||
          !alp.param.occur(this.params)) {
        this.argLevelParams.add(alp);
      }
    }
    return this.levelCorrect;
  }

// These get... methods now use the default ones defined in
// the superclass LevelNode
//
//  public final int getLevel() {
//    this.levelCheck();
//    return this.level;
//  }
//
//  public final HashSet getLevelParams() {
//    this.levelCheck();
//    return this.levelParams;
//  }
//
//  public final SetOfLevelConstraints getLevelConstraints() {
//    this.levelCheck();    
//    return this.levelConstraints;
//  }
//
//  public final SetOfArgLevelConstraints getArgLevelConstraints() {
//    this.levelCheck();    
//    return this.argLevelConstraints;
//  }
//
//  public final HashSet getArgLevelParams() {
//    this.levelCheck();    
//    return this.argLevelParams;
//  }

/***************************************************************************
* The following Asserts can be removed after debugging.                    *
***************************************************************************/
  public final int getMaxLevel(int i) {
    if (this.levelChecked == 0) 
      {throw new WrongInvocationException("getMaxLevel called before levelCheck");};
    int idx = (this.getArity() == -1) ? 0 : i;
    return this.maxLevels[idx];
  }

  public final int getWeight(int i) {
    if (this.levelChecked == 0) 
      {throw new WrongInvocationException("getWeight called before levelCheck");};
    int idx = (this.getArity() == -1) ? 0 : i;
    return this.weights[idx];
  }  

  public final int getMinMaxLevel(int i, int j) {
    if (this.levelChecked == 0) 
      {throw new WrongInvocationException("getMinMaxLevel called before levelCheck");};
    if (this.minMaxLevel == null) {
      return ConstantLevel;
    }
    return this.minMaxLevel[i][j];
  }

  public final boolean getOpLevelCond(int i, int j, int k) {
    if (this.levelChecked == 0) 
      {throw new WrongInvocationException("getOpLevelCond called before levelCheck");};
    if (this.opLevelCond == null) {
      return false;
    }
    return this.opLevelCond[i][j][k];
  }

  /**
   * toString, levelDataToString, and walkGraph methods to implement
   * ExploreNode interface
   */
  public final String levelDataToString() { 
    if (   (this.getKind() == ModuleInstanceKind)
        || (this.getKind() == NumberedProofStepKind)) {return "";} ;
        /*******************************************************************
        * A ModuleInstanceKind node is never level checked, and I don't    *
        * think a NumberedProofStepKind is either.                         *
        *******************************************************************/
    if (this.arity < 0) {
      return "Arity: "               + this.arity                   + "\n" +
             "Level: "               + this.getLevel()              + "\n" +
             "MaxLevel: "            + this.maxLevels[0]            + "\n";
    }
    else {
      /*********************************************************************
      * Modified by LL on 24 Mar 2007 to print the maxLevels array         *
      * properly.                                                          *
      *********************************************************************/
      String maxLevelStr = "" ;
        for (int i = 0; i < this.maxLevels.length; i++) {
           if (i > 0) {maxLevelStr = maxLevelStr + ", ";};
           maxLevelStr = maxLevelStr + this.maxLevels[i];
           } ;
      String isLeibnizArgStr = "" ;
        for (int i = 0; i < this.isLeibnizArg.length; i++) {
           if (i > 0) {isLeibnizArgStr = isLeibnizArgStr + ", ";};
           isLeibnizArgStr = isLeibnizArgStr + this.isLeibnizArg[i];
           } ;
      String opLevelCondStr = "" ;
      if (opLevelCond != null) {
        opLevelCondStr = "[" ;
        for (int i = 0; i < opLevelCond.length; i++) {
          opLevelCondStr = opLevelCondStr + " [" ;
          for (int j = 0; j < opLevelCond[i].length; j++) {
            opLevelCondStr = opLevelCondStr + " [" ;
            for (int k = 0; k < opLevelCond[i][j].length; k++) {
               String foo = " " ;
               if (k==0) {foo = "";}
               opLevelCondStr = opLevelCondStr + foo +
                   this.opLevelCond[i][j][k] ;
             } // for k
            opLevelCondStr = opLevelCondStr + "]" ;
           } // for j
          opLevelCondStr = opLevelCondStr + "]" ;
         } ; // for i
        opLevelCondStr = opLevelCondStr + "]" ;
       } ; // if (opLevelCond != null)
      return "Arity: "               + this.arity                    + "\n" +
             "Level: "               + this.getLevel()               + "\n" +
             "LevelParams: "         + this.getLevelParams()         + "\n" +
             "LevelConstraints: "    + this.getLevelConstraints()    + "\n" +
             "ArgLevelConstraints: " + this.getArgLevelConstraints() + "\n" +
             "ArgLevelParams: "      + ALPHashSetToString(this.getArgLevelParams()) + "\n" +
             "MaxLevel: "            + maxLevelStr                   + "\n" +
             "opLevelCond: "         + opLevelCondStr                + "\n" +
             "AllParams: "           + HashSetToString(this.getAllParams()) + "\n" +
             "NonLeibnizParams: "    + HashSetToString(this.getNonLeibnizParams()) + "\n" +
             "IsLeibniz: "           + this.isLeibniz                + "\n" +
             "isLeibnizArg: "       + isLeibnizArgStr               + "\n" ;
    }
  }

  
  /**
   * The body is the node's only child.
   */
  
  public SemanticNode[] getChildren() {
    return new SemanticNode[] {this.body};
  }
  
  /**
   * walkGraph finds all reachable nodes in the semantic graph
   * and inserts them in the Hashtable semNodesTable for use by 
   * the Explorer tool.
   */
  public final void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(uid, this);
    if (params != null && params.length > 0) {
      for (int i = 0; i < params.length; i++) {
        if (params[i] != null) params[i].walkGraph(semNodesTable);
      }
    }
    if (body != null) body.walkGraph(semNodesTable);
    if (stepNode != null) stepNode.walkGraph(semNodesTable);
  }

  /**
   * Displays this node as a String, implementing ExploreNode
   * interface; depth parameter is a bound on the depth of the portion
   * of the tree that is displayed.
   */
  public final String toString(int depth) {
    if (depth <= 0) return "";

    String ret = "\n*OpDefNode: " + this.getName().toString() 
                + "\n  " 
                + super.toString(depth) 
                + "\n  local: " + local
                + "\n  letInLevel: " + letInLevel
                + "\n  inRecursive: " + inRecursive
                + "\n  inRecursiveSection: " + inRecursiveSection
                + "\n  recursiveSection: " + recursiveSection
                + "\n  local: " + local 
                + "\n  source: " + 
                  ((source == null) ? "this" : 
                       (source.getName().toString() + 
                            " (uid: " + source.myUID + ")"))
                + "\n  originallyDefinedInModule: " + 
                     ((originallyDefinedInModule == null) ? "null" :
                       (originallyDefinedInModule.getName().toString() +
                          " (uid: " + originallyDefinedInModule.myUID + ")"))
                + ((stepNode == null) ? "" : 
                        ("\n  stepNode: " + 
                          Strings.indent(4,stepNode.toString(depth-3)))) 
                                                   ;

//  nextDependency has been removed.
//                + "\n  nextDependency: " ;  
//    if(nextDependency == null) {ret = ret + "null";}
//     else {ret = ret + nextDependency.getName().toString();} ;
    if (params != null) {
      String tempString = "\n  Formal params: " + params.length;
      for (int i = 0; i < params.length; i++) {
        tempString += Strings.indent(4, ((params[i] != null)
                                         ? params[i].toString(depth-1) 
                                         : "\nnull"));
      }
      ret += tempString;
    }
    else {
      ret += Strings.indent(2, "\nFormal params: null");
    }

    // Only print this stuff if user asks for a larger than necessary depth
    if (depth > 1) {
      if (st != null) {
        ret += "\n  SymbolTable: non-null";
      }
      else {
        ret += "\n  SymbolTable: null";
      }
    }
    if (body != null) {
      ret += Strings.indent(2,"\nBody:" + Strings.indent(2,body.toString(depth-1)));
    }
    else {
      ret += Strings.indent(2,"\nBody: null");
    }

    /***********************************************************************
    * The following is the same for all classes that implement the         *
    * OpDefOrLabelNode interface.                                          *
    ***********************************************************************/
    if (labels != null) {
       ret += "\n  Labels: " ;
       Enumeration list = labels.keys() ;
       while (list.hasMoreElements()) {
          ret += ((UniqueString) list.nextElement()).toString() + "  " ;
         } ;
      }  
    else {ret += "\n  Labels: null";};

    return ret;
  }

}
