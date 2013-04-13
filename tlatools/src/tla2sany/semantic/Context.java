// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// Last modified on Tue 15 May 2007 at  9:35:56 PST by lamport
/***************************************************************************
* 2 Mar 2007: enum <- Enum                                                 *
***************************************************************************/

package tla2sany.semantic;

import java.util.Enumeration;
import java.util.Hashtable;

import tla2sany.explorer.ExploreNode;
import tla2sany.st.Location;
import tla2sany.utilities.Strings;
import tla2sany.utilities.Vector;
import util.UniqueString;

// A context contains def/declNodes only.
// Implements a simple context for symbol decls and defs. Also
// supports the intial (or global) context of built-in operators.

// The pair construct is used to maintain a linked list of
// definitions.  This in turn will allow the extraction of a full
// context from anywhere in the tree, from the englobing definition.

// Merging: different forms of merging should be offered, depending
// what is being merged.  We always start with a clone of the
// initialContext.  Alterwards, we can Extend or Instantiate.  In one
// case, we import defs and decls; in the other, only defs; but we
// need to keep track of substitutions.

/**
 * A Context is an assignment of meanings to module names and to
 * symbol names, where a meaning is a SemNode.  At the moment, there
 * seems to be no need to provide methods to manipulate or do anything
 * with contexts except pass them to the Front End.
 */
public class Context implements ExploreNode {

  class Pair {
    Pair       link;
    SymbolNode info;

    // Note: Does not set lastPair
    Pair(Pair lnk, SymbolNode inf) {
      this.link = lnk;
      this.info = inf;
    }     

    // Note: Does set lastPair
    Pair(SymbolNode inf) {
      this.link = lastPair;
      this.info = inf;
      lastPair = this;
    }
    
    public SymbolNode getSymbol() { return this.info; }
    
    /**
     * For a Pair node pr, let List(pr) be the sequence of
     * Pair nodes of length n defined by 
     * 
     *   List(pr)[1] = pr
     *   List(pr)[n].link = null
     *   \A i \in 1..(n-1) : List(pr)[i+1] = List(pr)[i].link
     *   
     * Then reversePairList() is a Pair node such that
     * List(reversePairList()) has the same length n as
     * List(this), and whose elements are new Pair nodes such
     * that 
     * 
     *   \A i \in 1..n : List(reversePairList())[i].info = 
     *                      List(this)[n-i+1].info
     */
    public Pair reversePairList() {
        Pair curResult = new Pair(null, this.info) ;
        Pair nextOriginal = this.link  ;
        while (nextOriginal != null) {
            curResult = new Pair(curResult, nextOriginal.info) ;
            nextOriginal = nextOriginal.link ;
        }
        return curResult ;
    }
  } // class Pair

  public class InitialSymbolEnumeration {

    Enumeration e = initialContext.content();

    public boolean hasMoreElements() { return e.hasMoreElements(); }

    public SymbolNode nextElement() {
      return (SymbolNode)(((Pair)(e.nextElement())).getSymbol());
    }
  }

  public class ContextSymbolEnumeration {

    Enumeration e = Context.this.content();

    public boolean hasMoreElements() { return e.hasMoreElements(); }

    public SymbolNode nextElement() {
      return ((Pair)(e.nextElement())).getSymbol();
    }
  }

  private static Context initialContext = new Context(null, new Errors());
                                      // the one, static unique Context with builtin operators
                                      // null ModuleTable arg because this is shared by all modules

  private ExternalModuleTable exMT;   // The external ModuleTable that this context's SymbolTable
                                      // belongs to is null for global contex shared by all modules.

  private Errors         errors;      // Object in which to register errors
  private Hashtable      table;       // Mapping from symbol name to Pair's that include SymbolNode's
  private Pair           lastPair;    // Pair added last to the this.table

  /**
   * exMT is the ExternalModuleTable containing the module whose
   * SymbolTable this Context is part of (or null).
   */
  public Context(ExternalModuleTable mt, Errors errs) { 
    table = new Hashtable(); 
    this.exMT = mt;
    this.errors = errs;
    this.lastPair = null;
  }

  /*
   * Reinitialize the initialContext module so that a new spec file
   * can be parsed; must be called at the beginning of each root file
   * of a spec.
   */
  public static void reInit() {
    initialContext =  new Context(null, new Errors()); // null because outside of any module
  }

  /**
   * This method returns a copy of the context that contains
   * declarations only of the built-in operators of TLA+.  This
   * context assigns no meanings to module names.
   */
  public static Context getGlobalContext() { 
    return initialContext; 
  }

  public Errors getErrors() { return errors; }

  // Adds a symbol to the (unique) initialContext; aborts if already there
  public static void addGlobalSymbol(UniqueString name, SymbolNode sn, Errors errors) 
  throws AbortException {
    if (initialContext.getSymbol(name) != null) {
      errors.addAbort(Location.nullLoc,
		      "Error building initial context: Multiply-defined builtin operator " +
		      name + " at " + sn, false );
    }
    else {
      initialContext.addSymbolToContext( name, sn );
      return;
    }
  }

  /**
   * Returns symbol node associated with "name" in this Context, if
   * one exists; else returns null
   */
  public SymbolNode getSymbol(Object name) {
    Pair r = (Pair)table.get(name);
    if (r != null) {
      return r.info;
    }
    return null;
  }

  /**
   * Adds a (UniqueString, SymbolNode) pair to this context; no-op if
   * already present
   * @param name the UniqueString representing the string, see {@link UniqueString#uniqueStringOf(String)}
   * @param s the symbol node to be put in
   */
  public void addSymbolToContext(Object name, SymbolNode s) {
    table.put(name, new Pair(s));    // Links to & updates lastPair
  }

  
  /**
   * Tests whether a name is present in this context
   * @param name the UniqueString representing the string, see {@link UniqueString#uniqueStringOf(String)}
   * @return true iff the UniqueString provided occurs as a key in the symbol table 
   */
  public boolean occurSymbol(Object name) { 
    return table.containsKey(name); 
  }

  /**
   * Returns Enumeration of the elements of the Hashtable "Table",
   * which are pair of the form (Pair link, SymbolNode sn)
   */
  public Enumeration content() { 
    return table.elements(); 
  }

  /**
   * Returns a new ContextSymbolEnumeration object, which enumerates
   * the SymbolNodes of THIS context
   */
  public ContextSymbolEnumeration getContextSymbolEnumeration() {
    return new ContextSymbolEnumeration();
  }

  /**
   * Returns a Vector of those SymbolNodes in this Context that are
   * instances of class "template" (or one of its subclasses)
   */
  public Vector getByClass( Class template ) {
    Vector result = new Vector();
    Enumeration list = table.elements();
    while (list.hasMoreElements()) {
      Pair elt = (Pair)list.nextElement();
      if (template.isInstance(elt.info)) {
        result.addElement( elt.info );
      }
    }
    return result;
  }

  /** 
   * Returns a Vector of those SymbolNodes in this Context that are
   * instances of class OpDefNode and that are NOT of kind BuiltInKind
   * or ModuleInstanceKind
   */
  public Vector getOpDefs() {
      // SZ Apr 21, 2009: not used instance
      // Class template = OpDefNode.class;
    Pair nextPair = lastPair;

    Vector result = new Vector();
    while (nextPair != null) {
      if ( nextPair.info instanceof OpDefNode &&     // true for superclasses too.
           ((OpDefNode)nextPair.info).getKind() != ASTConstants.ModuleInstanceKind &&
           ((OpDefNode)nextPair.info).getKind() != ASTConstants.BuiltInKind  )
        result.addElement( (OpDefNode)(nextPair.info) );
      nextPair = nextPair.link;
    }
    return result;
  }

  /*************************************************************************
  * Returns a Vector of those SymbolNodes in this Context that are         *
  * instances of class ThmOrAssumpDefNode or ModuleInstanceKind            *
  * Code copied from getOpDefs().                                          *
  *************************************************************************/
  public Vector getThmOrAssDefs() {
      // SZ Apr 21, 2009: not used instance
      // Class template = ThmOrAssumpDefNode.class;
    Pair nextPair = lastPair;

    Vector result = new Vector();
    while (nextPair != null) {
      if ( nextPair.info instanceof ThmOrAssumpDefNode)
        { result.addElement( (ThmOrAssumpDefNode)(nextPair.info) );} ;
      nextPair = nextPair.link;
    }
    return result;
  }

  /** 
   * Returns vector of OpDeclNodes that represent CONSTANT declarations 
   */
  public Vector getConstantDecls() {
    Class templateClass = OpDeclNode.class;
    Enumeration list = table.elements();

    Vector result = new Vector();
    while (list.hasMoreElements()) {
      Pair elt = (Pair)list.nextElement();
      if (templateClass.isInstance(elt.info) &&     // true for superclasses too.
         ((OpDeclNode)elt.info).getKind() == ASTConstants.ConstantDeclKind  )
        result.addElement( (SemanticNode)(elt.info) );

    }
    return result;
  }

  /* Returns vector of OpDeclNodes that represent CONSTANT declarations  */
  public Vector getVariableDecls() {
    Class templateClass = OpDeclNode.class;
    Enumeration list = table.elements();

    Vector result = new Vector();
    while (list.hasMoreElements()) {
      Pair elt = (Pair)list.nextElement();
      if (templateClass.isInstance(elt.info) &&     // true for superclasses too.
           ((OpDeclNode)elt.info).getKind() == ASTConstants.VariableDeclKind  )
        result.addElement( (SemanticNode)(elt.info) );
    }
    return result;
  }

  /** 
   * Returns a Vector of those SymbolNodes in this Context that are
   * instances of class ModuleNode
   */
  public Vector getModDefs() {
    Class template = ModuleNode.class;
    Enumeration list = table.elements();

    Vector result = new Vector();
    while (list.hasMoreElements()) {
      Pair elt = (Pair)list.nextElement();
      if (template.isInstance(elt.info))    // true for superclasses too.
        result.addElement( (SemanticNode)(elt.info) );
    }
    return result;
  }

  // The following is a revised version of mergeExendContext that
  // fixes an apparent bug in the original in which elements of 
  // Context ct are added to this context in the inverse order.
  // Corrected version written by LL on 12 Mar 2013
  /**
   * Restricted Context merge.  Invoked once in Generator class.
   * Merges Context "ct" into THIS Context, except for local symbols
   * in "ct" Two symbols clash if they have the same name AND a different
   * class; that is an error.  If they have the same name and class, they
   * are considered to be two inheritances of the same (or at least
   * compatible) declarations, and there is only a warning.  Returns
   * true if there is no error or there are only warnings; returns
   * false if there is an error.
   * 
   * The original implementation added the elements of Context ct to
   * this context in the inverse order as they appear in ct.  It was 
   * changed on 12 Mar 2013 by LL to add them in the same order.
   */
  public boolean mergeExtendContext(Context ct) {
    boolean erc = true;

    // check locality, and multiplicity
    // the .reversePairList was added to the following statement
    // by LL on 12 Mar 2013
    Pair p = ct.lastPair.reversePairList();
    while (p != null) {
      // Walk back along the list of pairs added to Context "ct"
      SymbolNode sn = p.info;

      // Ignore local symbols in Context "ct"
      if (!sn.isLocal()) {
	Object sName;
	if (sn instanceof ModuleNode) {
	  sName = new SymbolTable.ModuleName(sn.getName());
	}
	else {
	  sName = sn.getName();
	}

        if (!table.containsKey(sName)) {
	  // If this context DOES NOT contain this name, add it:
	  table.put(sName, new Pair(sn));
        }
	else {
	  // If this Context DOES contain this name
          SymbolNode symbol = ((Pair)table.get(sName)).info;
          if (symbol != sn) {
	    // if the two SymbolNodes with the same name are distinct nodes,
	    // We issue a warning or do nothing if they are instances of the same Java 
        // class--i.e. FormalParamNode, OpDeclNode, OpDefNode, or ModuleNode--doing
        // nothing if they are both definitions coming from the same module.
	    // otherwise, it is considered to be an error.
        // Option of doing nothing if from same module added by LL on 31 Oct 2012 to
        // fix problem caused by the same module being both EXTENDed and imported with 
        // a LOCAL INSTANCE.  Previously, it always added the warning.
	    if (symbol.getClass() == sn.getClass()) {
	        if (! symbol.sameOriginallyDefinedInModule(sn)) {
              errors.addWarning( sn.getTreeNode().getLocation(),
                                 "Warning: the " + kindOfNode(symbol) +  " of '" + 
                                 sName.toString() + 
                                 "' conflicts with \nits " + kindOfNode(symbol) + " at " + 
                                 symbol.getTreeNode().getLocation() + ".");
	        }
         }
	    else {
              errors.addError( sn.getTreeNode().getLocation(),
                               "The " + kindOfNode(symbol) +  " of '" + 
                               sName.toString() + 
                               "' conflicts with \nits " + kindOfNode(symbol) + " at " + 
                               symbol.getTreeNode().getLocation() + ".");
                      
//                               "Incompatible multiple definitions of symbol '" + 
//                               sName.toString() + 
//                               "'; \nthe conflicting declaration is at " + 
//                               symbol.getTreeNode().getLocation()+ ".");
              erc = false;
            } //end else
          } // end if
        } // end else
      }
      p  = p.link;
    }
    return erc;
  }

  private static String kindOfNode(SymbolNode symbol) {
      if (symbol instanceof OpDefNode) {return "definition";}
      if (symbol instanceof FormalParamNode) {return "definition";}
      return "declaration";
  }
  
  /**
   * Returns a duplicate of this Context.  Called once from
   * SymbolTable class.  The tricky part is duplicating the
   * linked-list of Pairs starting from this.lastpair. 
   */
  public Context duplicate(ExternalModuleTable exMT) {    // Added argument exMT (DRJ)
    Context dup       = new Context(exMT, errors);
    Pair    p         = this.lastPair;
    Pair    current   = null;
    boolean firstTime = true;

    while (p != null) {
      if (firstTime) {
        current = new Pair(null, p.info);     // Does NOT link to or update this.lastPair
        dup.lastPair = current;
        firstTime = false;
      }
      else {
	current.link = new Pair(null,p.info); // Note: causes sharing of reference in link.info
        current = current.link;
      }
      dup.table.put(current.info.getName(), current);
      p = p.link;
    }
    return dup;
  }

  /**
   * toString, levelDataToString, and walkGraph methods to implement
   * ExploreNode interface
   */
  public String levelDataToString() { return "Dummy level string"; }

  public String toString(int depth) {
    return "Please use Context.getContextEntryStringVector()" +
      " instead of Context.toString()";
  }  

  /* Returns a vector of strings */

  /*************************************************************************
  * When trying to use SANY's -d (debug) option, this method throws a      *
  * NullPointerException if the spec has an inner module.  See the         *
  * comment in the walkGraph method of this file for a bit more            *
  * information.                                                           *
  *************************************************************************/
  public Vector getContextEntryStringVector(int depth, boolean b) {
    Vector ctxtEntries = new Vector(100);  // vector of Strings
    Context naturalsContext = 
               exMT.getContext(UniqueString.uniqueStringOf("Naturals"));

    if (depth <= 0) return ctxtEntries;

    Pair p = lastPair;
    while (p != null) {
      UniqueString key = p.info.getName();

      // If b is false, don't bother printing the initialContext--too long--
      // and, don't bother printing elements of the Naturals module either
      if (b || (!initialContext.table.containsKey(key) &&
		(naturalsContext == null || 
		 !naturalsContext.table.containsKey(key)))) {
        SymbolNode symbNode  = ((Pair)(table.get(key))).info;
	ctxtEntries.addElement("\nContext Entry: " + key.toString() + "  " 
                    + String.valueOf(((SemanticNode)symbNode).myUID).toString() + " " 
                    + Strings.indentSB(2,(symbNode.toString(depth-1))));
      }
      p = p.link;
    }

    // Reverse the order of elements in the vector so they print properly
    Object obj;
    int n = ctxtEntries.size();
    for (int i = 0; i < n/2; i++) {
      obj = ctxtEntries.elementAt(i);
      ctxtEntries.setElementAt(ctxtEntries.elementAt(n-1-i),i);
      ctxtEntries.setElementAt(obj, n-1-i);
    }
    return ctxtEntries;
  }

  public void walkGraph(Hashtable semNodesTable) {
    UniqueString key;
    Enumeration  Enum = table.keys();

    while (Enum.hasMoreElements()) {
      /*********************************************************************
      * Bug fix attempted by LL on 19 Apr 2007.                            *
      *                                                                    *
      * The original code expected Enum.nextElement() to be a              *
      * UniqueString.  However, it can also be a SymbolTable.ModuleName    *
      * for an inner module.  I attempted to fix that by just getting key  *
      * from the right place in the object.  However, that caused a        *
      * NullPointerException because table.get(key) equaled null.  So, I   *
      * just had the code print a warning and ignore the entry for the     *
      * inner module.  However, this caused a NullPointerException in      *
      * getContextEntryStringVector later on.  I decided to stop wasting   *
      * time on this.                                                      *
      *********************************************************************/
      Object next = Enum.nextElement();
      if (next instanceof SymbolTable.ModuleName) {
         key = ((SymbolTable.ModuleName) next).name ;
         System.out.println("Bug in debugging caused by inner module " + 
                             key.toString());
         System.out.println("SANY will throw a null pointer exception.");
        }
      else { 
        key = (UniqueString) next; 
        ((Pair)table.get(key)).info.walkGraph(semNodesTable);
       } ;
    }

  }

}
