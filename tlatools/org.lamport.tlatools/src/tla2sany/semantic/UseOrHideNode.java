// Copyright (c) 2007 Microsoft Corporation.  All rights reserved.
// last modified on Fri  3 July 2009 at 12:41:45 PST by lamport
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
 * This class represents a USE or HIDE statement.  It is of kind            *
 * UseKind or HideKind.                                                     *
 ***************************************************************************/
public class UseOrHideNode extends LevelNode {

    /*************************************************************************
     * The fields.                                                            *
     *                                                                        *
     * A use or hide has the syntax USE/HIDE [facts] [DEF[S] defs].  The      *
     * following two fields are the semantic nodes for the facts and defs.    *
     *************************************************************************/
    public final LevelNode[] facts;
    /***********************************************************************
     * For each i, facts[i] will be either an ExprNode, a ModuleNode, or    *
     * an OpDefNode of type ModuleInstanceKind (with no parameters).  A     *
     * proof management tool will probably put restrictions on the class    *
     * of expressions that can be used as facts.                            *
     *                                                                      *
     * 4 Mar 2009: implemented a restriction that arbitrary expressions     *
     * can't be used as facts.  The only allowable expressions are the      *
     * names of theorems, assumptions, and steps.                           *
     ***********************************************************************/
    public final SymbolNode[] defs;
    /***********************************************************************
     * For each i, defs[i] should be a UserDefinedOpDefKind or              *
     * ModuleInstanceKind OpDefNode or a ThmOrAssumpDefNode                 *
     ***********************************************************************/

    public final boolean isOnly;
    /***********************************************************************
     * True iff this node was formed from an "ONLY" step.  This is          *
     * possible only if the node is of kind UseKind or if it was            *
     * temporarily constructed for making a LeafProofNode for a "BY ONLY"   *
     * proof.  However, the "ONLY BY" construct might be disabled.          *
     ***********************************************************************/

    /**
     * If the UseOrHideNode is a proof step, this is the step number.  It
     * is made a UniqueString for consistency; there's no need to make
     * comparison efficient.
     * Added by LL on 6 June 2010.
     */
    private UniqueString stepName = null;

    /*************************************************************************
     * The constructor.                                                       *
     *************************************************************************/
    public UseOrHideNode(final int kind, final TreeNode stn, final LevelNode[] theFacts,
                         final SymbolNode[] theDefs, final boolean only) {
        super(kind, stn);
        this.facts = theFacts;
        this.defs = theDefs;
        this.isOnly = only;
    }

    /**
     * @return the stepName
     */
    public UniqueString getStepName() {
        return stepName;
    }

    public void setStepName(final UniqueString stepName) {
        this.stepName = stepName;
    }

    /*************************************************************************
     * The following method was added 4 Mar 2009 to check the restriction     *
     * that only the names of facts (and of modules) can be used as facts in  *
     * a USE or HIDE.                                                         *
     *                                                                        *
     * It was modified on 1 Jul 2009 to allow the use of expressions as       *
     * facts in a USE.                                                        *
     *************************************************************************/
    public void factCheck() {
        if (this.facts == null || this.getKind() == UseKind) {
            return;
        }
        for (final LevelNode fact : this.facts) {
            if ((fact.getKind() == OpApplKind)
                    && (((OpApplNode) fact).operator.getKind()
                    != ThmOrAssumpDefKind)) {
                errors.get().addError(
                        fact.stn.getLocation(),
                        "The only expression allowed as a fact in a HIDE " +
                                "is \nthe name of a theorem, assumption, or step.");
            }
        } // for
    }

    @Override
    public boolean levelCheck(final int iter) {
        /***********************************************************************
         * Level checking is performed by level-checking the facts.  Since the  *
         * defs should be defined operators, they have already been level       *
         * checked.                                                             *
         ***********************************************************************/
        if (this.levelChecked >= iter) return this.levelCorrect;
        return this.levelCheckSubnodes(iter, facts);
    }

    @Override
    public void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        final Integer uid = myUID;
        if (semNodesTable.get(uid) != null) return;
        semNodesTable.put(uid, this);
        visitor.preVisit(this);
        for (final LevelNode fact : facts) {
            fact.walkGraph(semNodesTable, visitor);
        }
        /***********************************************************************
         * Note: there's no need to walk the defs array because all the nodes   *
         * on it are walked from the nodes under which they appear.             *
         ***********************************************************************/
        visitor.postVisit(this);
    }

    /*
     * The children are the facts.
     * @see tla2sany.semantic.SemanticNode#getChildren()
     */
    @Override
    public SemanticNode[] getChildren() {
        if (this.facts == null || this.facts.length == 0) {
            return null;
        }
        final SemanticNode[] res = new SemanticNode[this.facts.length];
        System.arraycopy(facts, 0, res, 0, facts.length);
        return res;
    }

    @Override
    public String toString(final int depth) {
        if (depth <= 0) return "";
        final StringBuilder ret = new StringBuilder("\n*UseOrHideNode:\n"
                + super.toString(depth)
                + Strings.indent(2, "\nisOnly: " + this.isOnly)
                + Strings.indent(2, "\nfacts:"));
        for (final LevelNode fact : this.facts) {
            ret.append(Strings.indent(4, fact.toString(1)));
        }
        ret.append(Strings.indent(2, "\ndefs:"));
        for (final SymbolNode def : this.defs) {
            ret.append(Strings.indent(4, def.toString(1)));
        }
        return ret.toString();
    }

    @Override
    protected Element getLevelElement(final Document doc, final SymbolContext context) {
        //SemanticNode.SymbolContext context = new SemanticNode.SymbolContext(context2);
        final Element e = doc.createElement("UseOrHideNode");

        final Element factse = doc.createElement("facts");
        final Element definitions = doc.createElement("defs");

        for (final LevelNode fact : facts) factse.appendChild(fact.export(doc, context));
        for (final SymbolNode def : defs) definitions.appendChild(def.export(doc, context));

        e.appendChild(factse);
        e.appendChild(definitions);
        if (isOnly) e.appendChild(doc.createElement("only"));
        if (getKind() == HideKind) e.appendChild(doc.createElement("hide"));


// at the end, we append the context of the symbols used in this node
        //e.appendChild(context.getContextElement(doc));

        return e;
    }
}
