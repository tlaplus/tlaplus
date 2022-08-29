// Copyright (c) 2007 Microsoft Corporation.  All rights reserved.

// last modified on Fri 23 Nov 2007 at 17:21:52 PST by lamport
/***************************************************************************
 * The NewSymbNode constructor is invoked in semantic/Generator.java to     *
 * construct the nodes corresponding to a NewSymb syntactic node in an      *
 * AssumeProve.  The NewSymb node represents a declaration in an ASSUME,    *
 * such as "ASSUME CONSTANT x \in S ".                                      *
 *                                                                          *
 * The node has two descendants in the semantic tree, returned              *
 * by these methods:                                                        *
 *   OpDeclNode getOpDeclNode()                                             *
 *     An OpDeclNode for the declaration.                                   *
 *                                                                          *
 *   ExprNode getSet()                                                      *
 *     If the node represents a declaration such as "CONSTANT x \in S",     *
 *     then this returns the ExprNode for S. Otherwise, it returns null.    *
 ***************************************************************************/

package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;

import java.util.Hashtable;

public class NewSymbNode extends LevelNode {

    /*************************************************************************
     * Fields.                                                                *
     *************************************************************************/
    private final OpDeclNode opDeclNode;
    /***********************************************************************
     * The OpDeclNode for the declaration represented by the NewSymbNode    *
     * object.                                                              *
     ***********************************************************************/
    private final ExprNode set;
    /***********************************************************************
     * The ExprNode for expression S in "CONSTANT id \in S".                *
     ***********************************************************************/
// There's now a level field for all LevelNode subclasses, and this.levelChecked
// indicates if levelCheck has been callsed
//  private int       level = -1;
//    /***********************************************************************
//    * The level.  The value of -1 indicates that levelCheck has not yet    *
//    * been called.                                                         *
//    ***********************************************************************/

// Role subsumed by this.levelCorrect

    /*************************************************************************
     * The Constructor.                                                       *
     *************************************************************************/
    public NewSymbNode(
            final OpDeclNode opDeclNode, // The OpDeclNode for the declaration.
            final ExprNode set,        // Expression S in "CONSTANT x \in S",
            //   null for other kinds of declaration.
            final TreeNode stn             // The syntax node.
    ) {
        super(NewSymbKind, stn);
        this.set = set;
        this.opDeclNode = opDeclNode;
    }


    /*************************************************************************
     * Methods particular to the NewSymb node.                                *
     *************************************************************************/
    public final ExprNode getSet() {
        return set;
    }

    public final OpDeclNode getOpDeclNode() {
        return opDeclNode;
    }

    /*************************************************************************
     * The implementation of the LevelNode abstract methods.                  *
     *                                                                        *
     * The level of the node is the maximum of opDeclNode's level and the     *
     * level of the `set' expression, if it's non-null.  Any other level      *
     * information comes from the `set' expression.                           *
     *************************************************************************/
    @Override
    public boolean levelCheck(final int iter) {

        if (levelChecked < iter) {
            /*********************************************************************
             * This is the first call of levelCheck, so the level information     *
             * must be computed.  Actually, with the current implementation,      *
             * there's no need to call opDeclNode.levelCheck, since that just     *
             * returns true.  However, we do it anyway in case the OpDeclNode     *
             * class is changed to make levelCheck do something.                  *
             *********************************************************************/
            levelChecked = iter;
            final boolean opDeclLevelCheck = opDeclNode.levelCheck(iter);
            level = opDeclNode.getLevel();
            if (set != null) {
                levelCorrect = set.levelCheck(iter);
                level = Math.max(set.getLevel(), level);
                if (level == TemporalLevel) {
                    levelCorrect = false;
                    errors.get().addError(this.stn.getLocation(),
                            "Level error:\n" +
                                    "Temporal formula used as set.");
                }
            }
            levelCorrect = levelCorrect && opDeclLevelCheck;
            if (set != null) {
                levelParams = set.getLevelParams();
                allParams = set.getAllParams();
                levelConstraints = set.getLevelConstraints();
                argLevelConstraints = set.getArgLevelConstraints();
                argLevelParams = set.getArgLevelParams();
            }// if (set != null)
        }// if (levelChecked < iter)
        return levelCorrect;
    }

/**
 * toString, levelDataToString and walkGraph methods to implement
 * ExploreNode interface
 */

    /**
     * The body is the node's only child.
     */

    @Override
    public SemanticNode[] getChildren() {
        if (this.set == null) {
            return null;
        } else {
            return new SemanticNode[]{this.set};
        }
    }

    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        final Integer uid = myUID;
        if (semNodesTable.get(uid) != null) return;
        semNodesTable.put(uid, this);
        visitor.preVisit(this);
        if (set != null) {
            set.walkGraph(semNodesTable, visitor);
        }
        visitor.postVisit(this);
    }

    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";
        String setString = "";
        if (this.set != null) {
            setString = Strings.indent(2,
                    "\nSet:" + Strings.indent(2, this.set.toString(depth - 1)));
        }
        return "\n*NewSymbNode: " +
                "  " + super.toString(depth) +
                Strings.indent(2, "\nKind: " + this.getKind() +
                        "\nopDeclNode:" + Strings.indent(2,
                        this.opDeclNode.toString(depth - 1)) +
                        setString);
    }

    @Override
    protected Element getLevelElement(final Document doc, final SymbolContext context) {
        final Element e = doc.createElement("NewSymbNode");
        e.appendChild(getOpDeclNode().export(doc, context));
        if (getSet() != null) {
            e.appendChild(getSet().export(doc, context));
        }
        return e;
    }
}
