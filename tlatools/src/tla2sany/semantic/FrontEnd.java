// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

/***************************************************************************
* This module seems not to be used anywhere.  Almost all its methods have  *
* null implementations.                                                    *
***************************************************************************/


import tla2sany.parser.ParseException;
import tla2sany.st.TreeNode;
import util.FilenameToStream;
import util.NamedInputStream;

public class FrontEnd implements ASTConstants {
  /**
   * This class contains the methods by which a tool calls the Front End
   * to parse input and to create a semantic tree, and for various other
   * interactions.  The canonical code to produce a semantic analysis of
   * the module specified by file name M is:                            
   *                                                                    
   *    // First define ntfs to be a NameToFileIStream object.  (This   
   *    // object has no fields, and is used to pass a toStream method a
   *    // an argument to the parseAll method.)                         
   *    StringToNamedInputStream ntfs = new NameToFileIStream();               
   *                                                                    
   *    // Next set astn to an array of CST nodes of parsed             
   *    // modules--the last element of the array being the CST node    
   *    // for module M, and the other elements being for modules       
   *    // extended or instantiated (perhaps indirectly) by M.          
   *    TreeNode[] astn =                                                
   *          parseAll(NameToFileIStream.toStream(M), // the input stream
   *                   SemanticNode.ModuleKind,       // it's a module
   *                   ntfs)                                         
   *                                                                    
   *    // Successively analyze each of the modules in the context      
   *    // produced by analyzing the previous ones.                     
   *    Context ctxt = Context.InitialContext ;  // the initial context
   *    SemanticNode node ;   
   *    for (int i = 0; i < astn.length; i++){                          
   *      // Set node to the result of analyzing astn[i] in the        
   *      // context ctxt                                               
   *      node = semanticAnalysis(astn[i], ctxt);     
   *    }
   *
   *    ModuleNode node = (ModuleNode)node;
   *    // node is now the ModuleNode corresponding to module M.        
   */

  /**
   * This method calls the parser to parse the NamedInputStream
   * istream as a CST node of type cstNodeType.  Initially, this might
   * be implemented only when cstNodeType specifies a module node.  If
   * the parser encounters an EXTENDS or INSTANCE statement with a
   * module name "Foo", it uses cobj.toIStream("Foo") as the
   * NamedInputStream that should contain module "Foo".
   *                                                                  
   * The method returns an array of TreeNode's.  The last is the CSTNod
   * obtained by parsing istream as a node of type cstNodeType.  The  
   * first elements of the array are module nodes obtained by parsing 
   * the extended or instantiated modules.  These are listed in "logic
   * order"--that is, if module M1 extends or instances module M2, the
   * the TreeNode of M2 precedes that of M1 in the array.              
   *                                                                  
   * A tool, such as a specification browser, might need to know about
   * all the included modules as well as the module that constitutes the
   * specification.
   */
  public static TreeNode[] parseAll(NamedInputStream nis, int nkind,
				    FilenameToStream cobj)
  throws ParseException {
    return null;
  }

  /**
   * This method parses just the single stream to create a TreeNode.
   * It does not look for any of the modules that appear in EXTENDS or
   * INSTANCE statements.  This method is included for completeness.
   * It's not clear what tool would use it.  (Perhaps an interactive
   * editor that wants to do a quick check of what the user has just
   * typed?)
   */
  public static TreeNode parseOne(NamedInputStream nis, int nkind)
    throws ParseException {
    return null;
  }

  /**
   * This method returns a SemanticNode.  The SemanticNode is the 
   * meaning of the TreeNode cst, interpreted in the context ctxt, to  
   * produce a node whose kind field is nkind.  The context ctxt is
   * updated to include the context information from analyzing cst.
   * The precise meaning of this new context is not yet specified in      
   * general.  However, when nkind specifies a module node, and ctxt is
   * the context obtained by a series of calls of semanticAnalysis for
   * module nodes, then the returned Context is ctxt augmented by the 
   * assignment of the name of the module cst to the returned SemNode.
   */
  public static SemanticNode semanticAnalysis(TreeNode cst, int nkind,
					      Context ctxt)
    throws ParseException {
    return null;
  }

  /* Returns a new, unused tool id.  */
  private static int idCnt = 0;

  public static int getToolId() { return idCnt++; }
  
}
