// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;

import java.util.Hashtable;

public class AtNode extends ExprNode {

    private final OpApplNode exceptRef;           // reference to OpApplNode for the innermost
    //   enclosing $Except operator
    private final OpApplNode exceptComponentRef;  // reference to OpApplNode for the innermost
    //   enclosing $Pair operator that represents the
    //   ExceptComponent in which this occurrence of @ is used

    // Constructor
    public AtNode(final OpApplNode er, final OpApplNode ecr) {
        super(AtNodeKind, ecr.stn);
        this.exceptRef = er;
        this.exceptComponentRef = ecr;
    }

    /**
     * Return reference to the OpApplNode for the $Except operator with
     * which this occurrence of @ is associated.  For @ on the RHS of
     * an ExceptionSpec, that is the immediately enclosing $Except; for
     * other occurences of @ it is one $Except farther up the tree.
     */
    public final OpApplNode getExceptRef() {
        return this.exceptRef;
    }

    /**
     * Return reference to the OpApplNode for the $Pair operator with
     * which this occurrence of @ is associated.  For @ on the RHS of
     * an ExceptionSpec, that is the immediately enclosing ExceptSpec;
     * for other occurences of @ it is one farther up the tree.
     */
    public final OpApplNode getExceptComponentRef() {
        return this.exceptComponentRef;
    }

    /**
     * Return the expression that is the "base" of the expression that
     *
     * @ stands for.  In the example [ [ f[3] EXCEPT !.h[4] = (@ + @) ]
     * this expression is f[3].  Both AtNodes in this example refer to
     * the SAME node, not just to copies of the same node.
     */
    public final ExprNode getAtBase() {
        return (ExprNode) this.exceptRef.getArgs()[0];
    }

    /**
     * Return the expression that must be used to modify the "base" to
     * create the actual expression that @ stands for.  In the example
     * [ [ f[3] EXCEPT !.h[4] = (@ + @) ] this expression is roughly
     * transcribable as $Seq($StringNode(h), $ExprNode(4)).  Both
     * AtNodes in this example refer to the SAME node, not just to
     * copies of the same node.
     */
    public final OpApplNode getAtModifier() {
        return (OpApplNode) this.exceptComponentRef.getArgs()[0];
    }

    /* Level check */
// These nodes are now part of all LevelNode subclasses.

    @Override
    public final boolean levelCheck(final int iter) {
        if (this.levelChecked >= iter) return true;
        this.levelChecked = iter;

        final ExprOrOpArgNode[] args = this.exceptRef.getArgs();
        args[0].levelCheck(iter);
        this.level = args[0].getLevel();
        for (int i = 1; i < args.length; i++) {
            args[i].levelCheck(iter);
            if (args[i] == this.exceptComponentRef) break;
            this.level = Math.max(this.level, args[i].getLevel());
        }

//    this.levelParams = new HashSet();
        this.levelParams.addAll(args[0].getLevelParams());
        this.allParams.addAll(args[0].getAllParams());
        for (int i = 1; i < args.length; i++) {
            if (args[i] == this.exceptComponentRef) break;
            this.levelParams.addAll(args[i].getLevelParams());
            this.allParams.addAll(args[i].getAllParams());
        }

//    this.levelConstraints = new SetOfLevelConstraints();
        this.levelConstraints.putAll(args[0].getLevelConstraints());
        for (int i = 1; i < args.length; i++) {
            if (args[i] == this.exceptComponentRef) break;
            this.levelConstraints.putAll(args[i].getLevelConstraints());
        }

//    this.argLevelConstraints = new SetOfArgLevelConstraints();
        this.argLevelConstraints.putAll(args[0].getArgLevelConstraints());
        for (int i = 1; i < args.length; i++) {
            if (args[i] == this.exceptComponentRef) break;
            this.argLevelConstraints.putAll(args[i].getArgLevelConstraints());
        }

//    this.argLevelParams = new HashSet();
        this.argLevelParams.addAll(args[0].getArgLevelParams());
        for (int i = 1; i < args.length; i++) {
            if (args[i] == this.exceptComponentRef) break;
            this.argLevelParams.addAll(args[i].getArgLevelParams());
        }
        return true;
    }

    /**
     * toString, levelDataToString, & walkGraph methods needed to
     * implement ExploreNode interface
     */

    /*
     * walkGraph finds all reachable nodes in the semantic graph
     * and inserts them in the Hashtable semNodesTable for use by the Explorer tool.
     */
    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> h, final ExplorerVisitor visitor) {
        visitor.preVisit(this);
        // Empty because there are no nodes reachable through an AtNode that are not
        // reachable by other paths through the semantic graph.
        visitor.postVisit(this);
    } // end walkGraph()


    /*
     * Displays this node as a String, implementing ExploreNode interface; depth
     * parameter is a bound on the depth of the portion of the tree that is displayed.
     */
    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";
        return "\n*AtNode: " + super.toString(depth) +
                Strings.indent(2, "\nExceptRef: " + exceptRef.getUid() +
                        "\nExceptComponent: " + exceptComponentRef.getUid());
    }

    @Override
    protected Element getLevelElement(final Document doc, final SymbolContext context) {
        final Element e = doc.createElement("AtNode");
        final SemanticNode exceptObj = exceptRef.getArgs()[0];
        final SemanticNode exceptComponents = exceptComponentRef.getArgs()[0];
        e.appendChild(exceptObj.export(doc, context));
        e.appendChild(exceptComponents.export(doc, context));
        return e;
    }
}
