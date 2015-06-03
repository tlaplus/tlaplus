// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// last modified on Fri 16 Mar 2007 at 17:22:54 PST by lamport
package tla2sany.semantic;

import java.util.Hashtable;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

import tla2sany.explorer.ExploreNode;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.st.Location;
import tla2sany.st.TreeNode;
import tla2sany.xml.XMLExportable;
import util.ToolIO;

/**
 * SemanticNode is the (abstract) superclass of all nodes in the
 * semantic tree.
 *
 * It defines a unique identifier for each instance, which should be
 * used to check for equality.
 */
public abstract class SemanticNode
 implements ASTConstants, ExploreNode, LevelConstants, Comparable, XMLExportable /* interface for exporting into XML */ {

  private static final Object[] EmptyArr = new Object[0];

  private static int uid = 0;  // the next unique ID for any semantic node

  protected static Errors errors;

  public    int      myUID;    // the unique ID of THIS semantic node
  public    TreeNode stn;      // the concrete syntax tree node associated with THIS semantic node
  private   Object[] tools;    // each tool has a location in this array where
                               //   it may store an object for its own purposes
  private   int      kind;     // indicates what kind of semantic node this is;
                               //   strongly correlated with the Java type of the node

  public SemanticNode(int kind, TreeNode stn) {
    myUID = uid++;
    this.kind = kind;
    this.stn = stn;
    this.tools = EmptyArr;
  }

  public static void setError(Errors errs) { errors = errs; }

  public static String levelToString(int level) {
    switch (level) {
      case ConstantLevel: return level + " (Constant)";
      case VariableLevel: return level + " (Variable)";
      case ActionLevel:   return level + " (Action)";
      case TemporalLevel: return level + " (Temporal)";
      default:            return level + " (Illegal)";
    }
  }

  /**
   * This returns a unique identifier for the SemanticNode object.  In
   * principle, one could simply take the object itself (i.e., a ref to
   * it) as its unique id.  However, Java makes it more convenient to
   * work with int's than with ref's.
   */
  public final int getUid() { return this.myUID; }

  /**
   * The object's tools field is a sequence of objects that can be
   * used by different tools to keep tool-specific information.  A
   * tool calls FrontEnd.getToolId() to obtain a tool number t, and it
   * calls these two methods with toolId = t to read and write this
   * information.
   */
  public final Object getToolObject(int toolId) {
    if (this.tools.length <= toolId) return null;
    return this.tools[toolId];
  }

  /* Sets tool number toolId to obj.   */
  public final void setToolObject(int toolId, Object obj) {
    if (this.tools.length <= toolId) {
      Object[] newTools = new Object[toolId+1];
      System.arraycopy(this.tools, 0, newTools, 0, this.tools.length);
      this.tools = newTools;
    }
    this.tools[toolId] = obj;
    ToolIO.registerSemanticNode(this, toolId);
  }

  /**
   * These methods read and set the node's kind, which is a value
   * indicating what kind of node it is.  The value of the kind field
   * identifies the subclass of SemNode to which a node belongs.  All
   * the objects of a subclass have the same kind value, except for
   * OpDefOrDeclNode objects, which can have any of 6 different kinds.
   * The setKind method for each subclass checks that this is a legal
   * kind for that subclass, and raise an exception if it isn't.  See
   * the ASTConstants interface for a list of all the kinds of
   * semantic nodes.
   */
  public final int getKind() { return this.kind; }

  /* Sets the kind field of this object to k.  */
  public final void setKind(int k) { this.kind = k; }

  /* Returns the same concrete syntax tree node. */
  public final TreeNode getTreeNode() { return this.stn; }

  /**
   * Returns the array of comments immediately preceding the first
   * token of the spec that produces this semantic node.
   */
  public String[] getPreComments() { return ((SyntaxTreeNode) this.stn).getAttachedComments() ; }

  /**
   * Returns the result of getPreComments poorly formatted for
   * printing.  To be used in the toString methods for the various
   * node types.
   */
  public String getPreCommentsAsString() { return SyntaxTreeNode.PreCommentToString(this.getPreComments()) ; }

  /**
   * This returns the context of the node in the semantic tree.  It is
   * not defined what that means.  Here's the idea behind this method.
   * Suppose a tool wants to allow the user to edit the part of a spec
   * corresponding to a SemanticNode n.  After calling parseAll to obtain
   * the new CSTNode cst, the tool will call
   *
   *    semanticAnalysis(cst, n.getKind(), n.getContext())
   *
   * to obtain the new SemanticNode newsn.  As part of "plugging" the
   * node newsn into the semantic tree, the tool can call
   * newsn.setParent(n.getParent()).  It's likely that, for an
   * arbitrary node n in the semantic tree, n.getContext() is likely
   * to be just a wrapper for a pointer to n.
   */
  /*
  public Context getContext() throws AbortException {
    errors.addAbort(Location.nullLoc,
                    "Internal error: method getContext in SemanticNode not supported",true);
    return null;
  }
  */

  /**
   *  Returns the children of this node in the semantic tree.  For a
   *  node that normally has no children, it should return null.  In
   *  general, a child of a semantic node is a SemanticNode that describes
   *  a piece of the module whose location is within the location of that
   *  node.  If it's not obvious what the children should be for some kinds
   *  of semantic node, check the method for the particular kind of node to find
   *  out what it actually returns.
   *  <p>
   *  Initially, this method is not implemented for all kinds of semantic
   *  nodes.  It will be implemented as needed for whatever we decide to
   *  use it for.  The initial implementation is for being able to
   *  walk down the semantic tree to find the definition or declaration
   *  of a symbol.
   *  <p>
   *  This should probably be optimized by adding a field to a semantic
   *  node to cache the value of getChildren() when it's computed.
   *  However, perhaps that's only necessary for a ModuleNode.
   *
   *  This default method returns null.
   */
  public SemanticNode[] getChildren() {
      return null;
  }

  /**
   * Default implementations of walkGraph() to be inherited by subclasses
   * of SemanticNode for implementing ExploreNode interface; the purpose
   * of walkgraph is to find all reachable nodes in the semantic graph
   * and insert them in a Hashtable for use by the Explorer tool.
   */
  public void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(new Integer(myUID), this);
  }

  /**
   * Default implementation of toString() to be inherited by subclasses
   * of SemanticNode for implementing ExploreNode interface; the depth
   * parameter is a bound on the depth of the tree that is converted to String.
   */
  public String toString(int depth) {
    if (depth <= 0) return "";
    return ("  uid: " + myUID +
	    "  kind: " + (kind == -1 ? "<none>" : kinds[kind])
	    + getPreCommentsAsString());
  }

  // YY's code
  public final Location getLocation() {
    return this.stn.getLocation();
  }

  /**
   * This compareTo method is for use in sorting SemanticNodes in the
   * same module according to their starting location.  It returns
   * 0 (equal) iff they have the same starting location--that is,
   * if getLocation() returns locations with equal values of
   * beginLine() and  beginColumn().  Thus, compare(s1, s2) == 0
   * is NOT equivalent to equals(s1, s2).
   *
   * @param s1
   * @param s2
   * @return
   */
  public int compareTo(Object s) {
       Location loc1 = this.stn.getLocation();
       Location loc2 = ((SemanticNode) s).stn.getLocation();
       if (loc1.beginLine() < loc2.beginLine())
        {
           return -1;
       }
       if (loc1.beginLine() > loc2.beginLine()) {
           return 1;
       }
       if (loc1.beginColumn() == loc2.beginColumn()) {
           return 0;
       }
       return (loc1.beginColumn() < loc2.beginColumn())?-1:1;
  }

/***************************************************************************
* XXXXX A test for getLocation() returning null should be added            *
*       to the following two toString methods.                             *
***************************************************************************/
  public final void toString(StringBuffer sb, String padding) {
// Uncomment the code to print the actual image instead of file locations.	  
//	  TreeNode treeNode = getTreeNode();
//	  if (treeNode instanceof SyntaxTreeNode) {
//		  SyntaxTreeNode stn = (SyntaxTreeNode) treeNode;
//		  sb.append(stn.getHumanReadableImage());
//	  } else {
		  sb.append(this.getLocation());
//	  }
  }

  public String toString() {
//	  TreeNode treeNode = getTreeNode();
//	  if (treeNode instanceof SyntaxTreeNode) {
//		  SyntaxTreeNode stn = (SyntaxTreeNode) treeNode;
//		  return stn.getHumanReadableImage();
//	  }
    return this.getLocation().toString();
  }

    /**
     * August 2014 - TL
     * All nodes inherit from semantic node, which just attach location to the returned node
     */

  protected Element getSemanticElement(Document doc, tla2sany.xml.SymbolContext context) {
      throw new UnsupportedOperationException("xml export is not yet supported for: " + getClass() + " with toString: " + toString(100));
    }

    /**
     * August 2014 - TL
     * returns location information for XML exporting as attributes to
     * the element returned by getElement
     */
    protected Element getLocationElement(Document doc) {
      Location loc = getLocation();
      Element e = doc.createElement("location");
      Element ecol = doc.createElement("column");
      Element eline = doc.createElement("line");
      Element fname = doc.createElement("filename");

      Element bl = doc.createElement("begin");
      Element el = doc.createElement("end");
      Element bc = doc.createElement("begin");
      Element ec = doc.createElement("end");

      bc.appendChild(doc.createTextNode(Integer.toString(loc.beginColumn())));
      ec.appendChild(doc.createTextNode(Integer.toString(loc.endColumn())));
      bl.appendChild(doc.createTextNode(Integer.toString(loc.beginLine())));
      el.appendChild(doc.createTextNode(Integer.toString(loc.endLine())));

      fname.appendChild(doc.createTextNode(stn.getFilename()));

      ecol.appendChild(bc);
      ecol.appendChild(ec);
      eline.appendChild(bl);
      eline.appendChild(el);

      e.appendChild(ecol);
      e.appendChild(eline);
      e.appendChild(fname);

      return e;
    }

    /**
     * TL - auxiliary functions
     */
    protected Element appendElement(Document doc, String el, Element e2) {
      Element e = doc.createElement(el);
      e.appendChild(e2);
      return e;
    }
    protected Element appendText(Document doc, String el, String txt) {
      Element e = doc.createElement(el);
      Node n = doc.createTextNode(txt);
      e.appendChild(n);
      return e;
    }


    /** August 2014 - TL
     * A location element is prepannded to an implementing element
     */
  public Element export(Document doc, tla2sany.xml.SymbolContext context) {
      try {
        Element e = getSemanticElement(doc, context);
        try {
          Element loc = getLocationElement(doc);
          e.insertBefore(loc,e.getFirstChild());
        } catch (UnsupportedOperationException uoe) {
          uoe.printStackTrace();
          throw uoe;
        } catch (RuntimeException ee) {
          // do nothing if no location
        }
        return e;
      } catch (RuntimeException ee) {
        System.err.println("failed for node.toString(): " + toString() + "\n with error ");
        ee.printStackTrace();
        throw ee;
      }
    }
}
