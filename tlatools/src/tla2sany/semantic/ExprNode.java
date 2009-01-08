// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import tla2sany.st.TreeNode;

/**
 * An ExprNode is a node that represents some kind of expression 
 * (i.e., not an operator argument).  
 *
 * Exception as of 18 May 2008 modification made by LL. LabelNode
 * extends ExprNode, but it can represent a labeled ASSUME/PROVE as
 * well as a labeled expression.
 *
 * It is extended by AtNode, DecimalNode, LetInNode, NumeralNode, 
 *                   OpApplNode, StringNode, SubstInNode
 *
 * It extends the ExprOrOpArgNode class.
 *
 * It contains the methods getLevel and getLevelParams that specify the    
 * expression's level, where the level indicates the TLA level of the   
 * expression as follows.                                               
 *                                                                      
 *   0 : Constant Level                                                 
 *   1 : State Level                                                    
 *   2 : Action Level                                                   
 *   3 : Temporal Level                                                 
 *                                                                      
 * In general, the expression will be in the scope of some formal       
 * parameters, so its level will depend on the level of the expressions 
 * substituted for some of those parameters.  For example, if p and q   
 * are formal parameters, and x is a declared variable, then the level  
 * of the expression                                                    
 *                                                                      
 *    ENABLED(p' = x) /\ q                                              
 *                                                                      
 * is the maximum of 1 (the level of the ENABLED expression) and the    
 * level of q.  For the ExprNode n that represents this expression,     
 * n.getLevel() equals 1 and n.getLevelParams() is the array of length 1
 * whose single element is (a ref to) the FormalParamNode for q.        
 *                                                                      
 * Now suppose that an expression e in a constant module contains a     
 * declared constant c.  If the module is instantiated, then the level  
 * of the instantiated version of e will depend on the level of the     
 * expression substituted for c.  In that case, the array               
 * getLevelParams() for the node representing e will contain a ref to   
 * the OpDeclNode for the declaration of c.  Note that an instantiation 
 * of a nonconstant module must substitute a constant expression for a  
 * constant parameter, so in this case there's no need to put any refs  
 * to constant declarations in the array getLevelParams().              
 *                                                                      
 * Implementation Note.  A module is a constant module iff the following
 * conditions are satisfied:                                            
 *                                                                      
 *   1. It contains no VARIABLE declarations (or other nonCONSTANT      
 *      declarations in an ASSUME).                                     
 *   2. It contains no nonconstant operators such as prime ('), ENABLED,
 *      or [].                                                          
 *   3. It extends and instantiates only constant modules.              
 *                                                                      
 * The Front End can thus easily determine during the parsing phase     
 * whether or not a module is a constant module.  Thus, it can have that
 * information available when building the semantic tree.               
 */
public abstract class ExprNode extends ExprOrOpArgNode {

    // This class is empty. It inherits all the methods it requires
    // from the ExprOrOpArgNode class.

    public SymbolNode subExpressionOf = null ;
      /*********************************************************************
      * For an expression that is constructed as a subexpression of a      *
      * UserDefinedOpNode or ThmOrAssumpDefNode, this field equals that    *
      * node.                                                              *
      *********************************************************************/

    ExprNode(int kind, TreeNode stn) { super(kind, stn); }
}
