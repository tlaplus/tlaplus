// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;

public class LetInNode extends ExprNode
        implements ExploreNode, LevelConstants {

    public final Context context;
    /**
     * This node represents a LET expression, for example
     * <p>
     * LET Foo(a) == a + x
     * Bar == Foo(a) + a
     * IN body
     */

    private final SymbolNode[] opDefs;
    /***********************************************************************
     * opDefs is an array of the OpDefNode and ThmOrAssumpDefNode objects   *
     * defined in the LET. For TLA+1, these LET definitions were never      *
     * visible outside the IN expression.  The only reason for remembering  *
     * them was for level checking and printing them out.  Since in TLA+2   *
     * the definitions can be referred to from outside the IN expression,   *
     * the Context `context' was added that captures everything in the      *
     * LET, including ModuleInstanceKind OpDef nodes, and allows            *
     * convenient name lookup of them.  However, to minimize changes and    *
     * the possibility that allows for errors, the opDefs field has been    *
     * maintained.                                                          *
     ***********************************************************************/
    private final InstanceNode[] insts;
    /***********************************************************************
     * Like opDefs, except for the OpDef nodes of kind ModuleInstanceKind.  *
     * Used only for level checking.                                        *
     ***********************************************************************/
    private final ExprNode body;
    /*************************************************************************
     * The following method is not used by the parser and was provided for    *
     * use by tools.  It is no longer needed, since tools, can obtain that    *
     * information from the (public) context field.  However, TLC uses it,    *
     * until it is changed, we must provide it.  Since opDefs was changed to  *
     * include both ThmOrAssumpDefNode objects and ModuleInstanceKind         *
     * OpDefNode objects, it must be reimplemented.                           *
     *************************************************************************/
    private OpDefNode[] gottenLets = null;

    /**
     * Return the array of LET operator definitions. In the example above,
     * getLets()[1] is the OpDefNode representing the definition of Bar.
     */
    /* Constructor */
    public LetInNode(final TreeNode treeNode,
                     final SymbolNode[] defs,
                     final InstanceNode[] insts,
                     final ExprNode bdy,
                     final Context ctext) {
        super(LetInKind, treeNode);
        this.opDefs = defs;
        this.insts = insts;
        this.body = bdy;
        this.context = ctext;
    }

    public final OpDefNode[] getLets() {
        if (gottenLets == null) {
            /*********************************************************************
             * First count how many UserDefinedOpKind OpDefNode objects are in    *
             * opDefs.                                                            *
             *********************************************************************/
            int cnt = 0;
            for (final SymbolNode def : opDefs) {
                if (def.getKind() == UserDefinedOpKind) {
                    cnt++;
                }
            }
            gottenLets = new OpDefNode[cnt];
            cnt = 0;
            for (final SymbolNode opDef : opDefs) {
                if (opDef.getKind() == UserDefinedOpKind) {
                    gottenLets[cnt] = (OpDefNode) opDef;
                    cnt++;
                }
            }

        }
        return this.gottenLets;
    }

    /* Return the body of the LET expression (the IN expression). */
    public final ExprNode getBody() {
        return this.body;
    }

    /* Level checking */
// These fields are now part of all LevelNode subclasses.

    @Override
    @SuppressWarnings("unchecked")
    public final boolean levelCheck(final int itr) {
        if (this.levelChecked >= itr) return this.levelCorrect;
        levelChecked = itr;

        // Level check all the components:
        this.levelCorrect = true;
        /***********************************************************************
         * In TLA+2, opDefs contains ModuleInstanceKind OpDefNode objects,      *
         * which should not be level checked.  (They have no body to level      *
         * check.)                                                              *
         ***********************************************************************/
        for (final SymbolNode node : this.opDefs) {
            /***********************************************************************
             * In TLA+2, opDefs contains ModuleInstanceKind OpDefNode objects,      *
             * which should not be level checked.  (They have no body to level      *
             * check.)                                                              *
             ***********************************************************************/
            if ((node.getKind() != ModuleInstanceKind)
                    && !node.levelCheck(itr)) {
                this.levelCorrect = false;
            }
        }
        if (!this.body.levelCheck(itr)) {
            this.levelCorrect = false;
        }
        for (final InstanceNode instanceNode : this.insts) {
            if (!instanceNode.levelCheck(itr)) {
                this.levelCorrect = false;
            }
        }

        // Calculate level information:
        this.level = this.body.getLevel();

        /***********************************************************************
         * 23 February 2009: Added ".clone" to the following statements.  I     *
         * don't think this is needed and that everything works fine despite    *
         * the aliasing of the levelParams and allParams fields of this node    *
         * and its body to the same HashSets, but it doesn't hurt to be safe.   *
         ***********************************************************************/
        this.levelParams = (HashSet<SymbolNode>) this.body.getLevelParams().clone();
        this.allParams = (HashSet<SymbolNode>) this.body.getAllParams().clone();

//    this.levelConstraints = new SetOfLevelConstraints();
        this.levelConstraints.putAll(this.body.getLevelConstraints());
        /*******************************************************************
         * opDefs[i] is level checked above.                                *
         *******************************************************************/
        for (final SymbolNode symbolNode : this.opDefs) {
            if (symbolNode.getKind() != ModuleInstanceKind) {
                this.levelConstraints.putAll(symbolNode.getLevelConstraints());
            }
            /*******************************************************************
             * opDefs[i] is level checked above.                                *
             *******************************************************************/
        }

//    this.argLevelConstraints = new SetOfArgLevelConstraints();
        this.argLevelConstraints.putAll(this.body.getArgLevelConstraints());
        for (final SymbolNode def : this.opDefs) {
            if (def.getKind() != ModuleInstanceKind) {
                this.argLevelConstraints.putAll(def.getArgLevelConstraints());
            }
        }

//    this.argLevelParams = new HashSet();
        this.argLevelParams.addAll(this.body.getArgLevelParams());
        /*******************************************************************
         * opDefs[i] is either an OpDefNode or a ThmOrAssumpDefNode; only   *
         * an OpDefNode can have parameters.                                *
         *******************************************************************/
        for (final SymbolNode opDef : this.opDefs) {
            if (opDef.getKind() != ModuleInstanceKind) {
                /*******************************************************************
                 * opDefs[i] is either an OpDefNode or a ThmOrAssumpDefNode; only   *
                 * an OpDefNode can have parameters.                                *
                 *******************************************************************/
                FormalParamNode[] params = new FormalParamNode[0];
                if (opDef.getKind() != ThmOrAssumpDefKind) {
                    params = ((OpDefNode) opDef).getParams();
                }
                for (final ArgLevelParam alp : opDef.getArgLevelParams()) {
                    if (!alp.occur(params)) {
                        this.argLevelParams.add(alp);
                    }
                }
            }
        }
        /*******************************************************************
         * insts[i] level checked above.                                    *
         *******************************************************************/
        for (final InstanceNode inst : this.insts) {
            this.argLevelParams.addAll(inst.getArgLevelParams());
            /*******************************************************************
             * insts[i] level checked above.                                    *
             *******************************************************************/
        }
        return this.levelCorrect;
    }

    /**
     * toString, levelDataToString, and walkGraph methods to implement
     * ExploreNode interface
     */

    @Override
    public SemanticNode[] getChildren() {
        final SemanticNode[] res =
                new SemanticNode[this.opDefs.length + this.insts.length + 1];
        res[res.length - 1] = this.body;
        int i;
        for (i = 0; i < this.opDefs.length; i++) {
            res[i] = this.opDefs[i];
        }
        System.arraycopy(this.insts, 0, res, i + 0, this.insts.length);
        return res;
    }

    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        final Integer uid = myUID;

        if (semNodesTable.get(uid) != null) return;

        semNodesTable.put(uid, this);
        visitor.preVisit(this);

        /***********************************************************************
         * Can now walk LET nodes from context, don't need to use opDefs        *
         * (which is incomplete).                                               *
         ***********************************************************************/
        if (context != null) {
            context.walkGraph(semNodesTable, visitor);
        }
        if (body != null) body.walkGraph(semNodesTable, visitor);
        visitor.postVisit(this);
    }

    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";

        final StringBuilder ret = new StringBuilder("\n*LetInNode: " + super.toString(depth));
        /***********************************************************************
         * Print context.                                                       *
         ***********************************************************************/
        final ArrayList<String> contextEntries = context.getContextEntryStringArrayList(1, false);
        /*********************************************************************
         * The depth argument 1 of getContextEntryStringArrayList causes only    *
         * the name and node uid of the entry and not the node itself to be   *
         * printed.                                                           *
         *********************************************************************/
        if (contextEntries != null) {
            for (String contextEntry : contextEntries) {
                if (contextEntry != null) {
                    ret.append(Strings.indent(2, contextEntry));
                } else {
                    ret.append("*** null ***");
                }
            }
        }

        /***********************************************************************
         * We no longer print opDefs because the information is in the context. *
         ***********************************************************************/
        ret.append(Strings.indent(2, "\nBody:" + Strings.indent(2, body.toString(depth - 1))));
        return ret.toString();
    }

    @Override
    protected Element getLevelElement(final Document doc, final SymbolContext context) {
        final Element ret = doc.createElement("LetInNode");
        ret.appendChild(appendElement(doc, "body", body.export(doc, context)));
        final Element arguments = doc.createElement("opDefs");
        for (final SymbolNode opDef : opDefs) arguments.appendChild(opDef.export(doc, context));
        ret.appendChild(arguments);

        return ret;
    }
}
