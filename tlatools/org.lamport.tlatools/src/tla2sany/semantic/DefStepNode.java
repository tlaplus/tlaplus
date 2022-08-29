// Portions Copyright (c) 2007 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;
import util.UniqueString;

import java.util.Hashtable;

/***************************************************************************
 * This class represents definition step of a proof, which consists of a    *
 * sequence of operator-, function-, or module-definition steps.  (A        *
 * module definition is something like "Id == INSTANCE...".)                *
 ***************************************************************************/

public class DefStepNode extends LevelNode {

    /*************************************************************************
     * The fields.                                                            *
     *************************************************************************/
    private final UniqueString stepNumber;
    /***********************************************************************
     * The step number of the step if it has one, otherwise null if it's    *
     * not a numbered step.                                                 *
     ***********************************************************************/

    private final OpDefNode[] defs;
    /***********************************************************************
     * The sequence of definitions.                                         *
     ***********************************************************************/

    /*************************************************************************
     * The constructor.                                                       *
     *************************************************************************/
    public DefStepNode(final TreeNode stn, final UniqueString stepNum, final OpDefNode[] theDefs) {
        super(DefStepKind, stn);
        this.stepNumber = stepNum;
        this.defs = theDefs;
    }

    /*************************************************************************
     * The methods just return the field values.                              *
     *************************************************************************/
    public UniqueString getStepNumber() {
        return stepNumber;
    }

    public OpDefNode[] getDefs() {
        return defs;
    }

    @Override
    public boolean levelCheck(final int iter) {
        /***********************************************************************
         * Level check the steps and the instantiated modules coming from       *
         * module definitions.                                                  *
         ***********************************************************************/
        return this.levelCheckSubnodes(iter, defs);
    }

    @Override
    public void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        final Integer uid = myUID;
        if (semNodesTable.get(uid) != null) return;
        semNodesTable.put(uid, this);
        visitor.preVisit(this);
        for (final OpDefNode def : defs) {
            def.walkGraph(semNodesTable, visitor);
        }
        visitor.postVisit(this);
    }

    @Override
    public SemanticNode[] getChildren() {
        final SemanticNode[] res = new SemanticNode[defs.length];
        System.arraycopy(defs, 0, res, 0, defs.length);
        return res;
    }

    @Override
    public String toString(final int depth) {
        if (depth <= 0) return "";
        final StringBuilder ret = new StringBuilder("\n*DefStepNode:\n"
                + super.toString(depth)
                + Strings.indent(2, "\ndefs:"));
        for (final OpDefNode def : this.defs) {
            ret.append(Strings.indent(4, def.toString(depth - 1)));
        }
        return ret.toString();
    }

    @Override
    protected Element getLevelElement(final Document doc, final SymbolContext context) {
        final Element e = doc.createElement("DefStepNode");
        for (final OpDefNode def : defs) {
            e.appendChild(def.export(doc, context));
        }
        return e;
    }
}
