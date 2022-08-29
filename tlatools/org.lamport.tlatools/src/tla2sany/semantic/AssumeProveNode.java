// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sun  1 March 2009 at 14:09:26 PST by lamport

package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;

import java.util.Hashtable;

/***************************************************************************
 * An assume prove node represents something like                           *
 *                                                                          *
 *    ASSUME A, B                                                           *
 *    PROVE  C                                                              *
 *                                                                          *
 * The method getAssumes() returns the list A, B, each of which can be      *
 *   AssumeProveNode                                                        *
 *   ExprNode                                                               *
 *   NewSymbNode                                                            *
 *                                                                          *
 * The method getProve() returns C, which must be an ExprNode.              *
 *                                                                          *
 * Note: The level information for the Assume/Prove includes constraints    *
 * for the NEW symbols declared in the ASSUME clauses.  See comments        *
 * in LevelNode.java.                                                       *
 ****************************************************************************/

/***************************************************************************
 * 16 February 2009: LL added suffices field.                               *
 *   This field is set to true iff the AssumeProveNode object is generated  *
 *   by a step of the form.                                                 *
 *                                                                          *
 *     SUFFICES ASSUME A PROVE P                                            *
 ***************************************************************************/

/***************************************************************************
 * YET ANOTHER KLUDGE: references to subexpressions of ASSUME/PROVEs.       *
 *                                                                          *
 * If the assumptions of an ASSUME/PROVE contain declarations, then we      *
 * want to allow references to subexpressions of an ASSUME/PROVE only       *
 * within the scope of the declared symbols.  This means that a reference   *
 * ref to a subexpression exp of an ASSUME/PROVE is legal iff               *
 * the following predicate is true.                                         *
 *                                                                          *
 *    Legal(exp, ref) ==                                                    *
 *      /\ exp does not lie within the scope of a declaration in            *
 *         an inner (nested) ASSUME/PROVE                                   *
 *                                                                          *
 *      /\ \/ exp does not lie within the scope of a declaration in an      *
 *            outer ASSUME/PROVE                                            *
 *                                                                          *
 *         \/ IF the outer ASSUME/PROVE is the body of a SUFFICES theorem   *
 *              THEN ref lies outside the theorem's proof                   *
 *              ELSE ref lies within  the theorem's proof                   *
 *                                                                          *
 * To determine if a reference is legal, we add the following fields        *
 * to an AssumeProveNode object:                                            *
 *                                                                          *
 *   inScopeOfDecl[i] : True iff one of assume clauses 1 .. (i-1)           *
 *                      is a declaration.                                   *
 *                      (Hence inScopeOfDecl[0] = false.)                   *
 *                                                                          *
 *   inProof : This field is useful only during the construction            *
 *             of the semantic node, and is true iff SANY is                *
 *             currently analyzing the proof of the theorem                 *
 *             containing the ASSUME/PROVE.                                 *
 *                                                                          *
 * Using the fact that the AssumeProve node's goal field is non-null iff    *
 * the ASSUME/PROVE is an outer-level one (at least if the goal is a        *
 * named theorem or proof step), this makes it easy to check if             *
 * Legal(exp, ref) is true when ref is a positional subexpression.  In      *
 * particular, if rho is a legal reference to an ASSUME/PROVE node ap,      *
 * then                                                                     *
 *                                                                          *
 *   Legal(exp, rho!i) =                                                    *
 *     \/ ~ ap.inScopeOfDecl[i]                                             *
 *     \/ /\ ap.goal # null                                                 *
 *        /\ ap.goal.suffices = ~ ap.inProof                                *
 *                                                                          *
 * This is implemented in Generator.illegalAPPosRef.                        *
 *                                                                          *
 * To handle label references, we must first ensure that the parser does    *
 * not allow a label within the scope of a declaration from an inner        *
 * ASSUME/PROVE. (In Generator.generateAssumeProve, this is handled using   *
 * noLabelsAllowed and assumeProveDepth.)  We can then determine if         *
 * Legal(exp, ref) is true for a label reference by using the label's goal  *
 * and goalClause fields, and the suffices field of the goal's TheoremNode  *
 * (which is copied in the goal node).  More precisely, if rho is a legal   *
 * reference, then rho!lab is a legal reference iff                         *
 *                                                                          *
 *    LET ap == lab.goal                                                    *
 *    IN  \/ ap = null                                                      *
 *        \/ ~ ap.inScopeOfDecl[lab.goalClause]                             *
 *        \/ /\ ap.goal # null                                              *
 *           /\ ap.goal.suffices = ~ ap.inProof                             *
 *                                                                          *
 * The negation of this formula is computed by Generator.illegalLabelRef    *
 ***************************************************************************/

public class AssumeProveNode extends LevelNode {

    private final ThmOrAssumpDefNode goal;
    /*************************************************************************
     * The descendants.                                                       *
     *************************************************************************/
    protected LevelNode[] assumes = null;
    protected ExprNode prove = null;
    /*************************************************************************
     * Other fields: see their descriptions above.                            *
     *************************************************************************/
    protected boolean[] inScopeOfDecl;
    protected boolean inProof = true;
    /*************************************************************************
     * suffices field added 16 Feb 2009.                                      *
     * This field is used only in Generator.selectorToNode.                   *
     *************************************************************************/
    protected boolean suffices = false;
    /**
     * The following field is set true iff this is a []ASSUME/[]PROVE node.
     * This flag is not used by SANY or any current tool, but it's
     * here just in case it will ever be used by a future tool.
     */
    protected boolean isBoxAssumeProve;

    /*************************************************************************
     * The Constructor.                                                       *
     *************************************************************************/
    public AssumeProveNode(final TreeNode stn, final ThmOrAssumpDefNode gl) {
        super(AssumeProveKind, stn);
        this.goal = gl;
    }

    protected boolean isSuffices() {
        return this.suffices;
    }

    void setSuffices() {
        this.suffices = true;
    }

    public boolean getSuffices() {
        return suffices;
    }

    public boolean getIsBoxAssumeProve() {
        return isBoxAssumeProve;
    }
    /***********************************************************************
     * This is the named theorem or proof-step node whose body the          *
     * ASSUME/PROVE is.  Otherwise, it equals null.  In particular, it      *
     * equals null for an inner ASSUME/PROVE                                *
     *                                                                      *
     * This comment was wrong until LL added the code to                    *
     * Generator.generateAssumeProve to make it true on 9 Nov 2009.         *
     ***********************************************************************/

    protected void setIsBoxAssumeProve(final boolean value) {
        isBoxAssumeProve = value;
    }

    /*************************************************************************
     * The methods for finding the descendants.                               *
     *************************************************************************/
    public final SemanticNode[] getAssumes() {
        return assumes;
    }

    public final ExprNode getProve() {
        return prove;
    }

    public ThmOrAssumpDefNode getGoal() {
        return goal;
    }


    /*************************************************************************
     * Fields and methods for implementing the LevelNode interface.           *
     * The fields are all set by the levelCheck  method.                      *
     *************************************************************************/
// These fields are now part of all LevelNode subclasses.

    /*************************************************************************
     * I implemented the levelCheck  method by copying from the method of     *
     * the same name in the OpApplNode class, using the assumptions and       *
     * prove expression the same way the ranges expressions are used to       *
     * compute the level-related fields for an OpApplNode.  This seems        *
     * reasonable, but I don't know if it's really correct.  -   LL           *
     *************************************************************************/
    @Override
    public boolean levelCheck(final int iter) {
        /***********************************************************************
         * Return immediately if this this.levelCheck(i) has already been       *
         * invoked for i >= iter.                                               *
         ***********************************************************************/
        if (levelChecked >= iter) return this.levelCorrect;
        levelChecked = iter;

        this.levelCorrect = true;

        /***********************************************************************
         * Level check assumptions.                                             *
         ***********************************************************************/
        for (final LevelNode element : this.assumes) {
            if (element != null && !element.levelCheck(iter)) {
                this.levelCorrect = false;
            }
        }// end for

        /***********************************************************************
         * Level check prove expression                                         *
         ***********************************************************************/
        this.prove.levelCheck(iter);

        /***********************************************************************
         * Calculate level.                                                     *
         ***********************************************************************/
        this.level = this.prove.getLevel();
        /*******************************************************************
         * Must call levelCheck before calling getLevel.                    *
         *******************************************************************/
        for (final LevelNode item : this.assumes) {
            item.levelCheck(iter);
            /*******************************************************************
             * Must call levelCheck before calling getLevel.                    *
             *******************************************************************/
            if (item.getLevel() > level) {
                level = item.getLevel();
            }
        }

        /***********************************************************************
         * Calculate levelParams and allParams.                                 *
         ***********************************************************************/
//    this.levelParams = new HashSet();
        this.levelParams.addAll(this.prove.getLevelParams());
        this.allParams.addAll(this.prove.getAllParams());
        for (final LevelNode value : this.assumes) {
            this.levelParams.addAll(value.getLevelParams());
            this.allParams.addAll(value.getAllParams());
        }// for i

        /***********************************************************************
         * Calculate levelConstraints.                                          *
         ***********************************************************************/
//    this.levelConstraints = new SetOfLevelConstraints();
        this.levelConstraints.putAll(this.prove.getLevelConstraints());
        for (final LevelNode node : this.assumes) {
            this.levelConstraints.putAll(node.getLevelConstraints());
        }

        /***********************************************************************
         * Calculate argLevelConstraints.                                       *
         ***********************************************************************/
//    this.argLevelConstraints = new SetOfArgLevelConstraints();
        this.argLevelConstraints.putAll(this.prove.getArgLevelConstraints());
        for (final LevelNode levelNode : this.assumes) {
            this.argLevelConstraints.putAll(levelNode.getArgLevelConstraints());
        }

        /***********************************************************************
         * Calculate argLevelParamams.                                          *
         ***********************************************************************/
//    this.argLevelParams = new HashSet();
        this.argLevelParams.addAll(this.prove.getArgLevelParams());
        for (final LevelNode assume : this.assumes) {
            this.argLevelParams.addAll(assume.getArgLevelParams());
        }
        /***********************************************************************
         * The following added on 1 Mar 2009.  See                              *
         * LevelNode.addTemporalLevelConstraintToConstants.                     *
         ***********************************************************************/
        if (this.levelCorrect) {
            addTemporalLevelConstraintToConstants(this.levelParams,
                    this.levelConstraints);
        }
        return this.levelCorrect;
    } // end levelCheck


/*************************************************************************
 * End fields and methods implementing the LevelNode interface:           *
 *************************************************************************/

    /*************************************************************************
     * Fields and methods implementing the ExplorerNode  interface:           *
     *************************************************************************/


    /**
     * The children of this node are the assumes and prove expressions.
     */
    @Override
    public SemanticNode[] getChildren() {
        final SemanticNode[] res = new SemanticNode[this.assumes.length + 1];
        res[assumes.length] = this.prove;
        System.arraycopy(assumes, 0, res, 0, assumes.length);
        return res;
    }

    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> h, final ExplorerVisitor visitor) {
        final Integer uid = myUID;
        if (h.get(uid) != null) return;
        h.put(uid, this);
        visitor.preVisit(this);
        int i = 0;
        while (i < assumes.length) {
            assumes[i].walkGraph(h, visitor);
            i = i + 1;
        }
        prove.walkGraph(h, visitor);
        visitor.postVisit(this);
    } // end walkGraph()


    /*
     * Displays this node as a String, implementing ExploreNode interface; depth
     * parameter is a bound on the depth of the portion of the tree that is displayed.
     */
    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";
        final StringBuilder assumeStr = new StringBuilder();
        int i = 0;
        while (i < assumes.length) {
            assumeStr.append(Strings.indent(4, assumes[i].toString(depth - 1)));
            i = i + 1;
        }
        String goalStr = "null";
        if (goal != null) {
            goalStr = Strings.indent(4, goal.toString(1));
        }
        return "\n*AssumeProveNode: "
                + super.toString(depth)  // Seems to print stn.getLocation() where stn is the
                // corresponding syntax tree node.
                + "\n  " + (isBoxAssumeProve ? "[]" : "") + "Assumes: " + assumeStr
                + "\n  " + (isBoxAssumeProve ? "[]" : "") + "Prove: " + Strings.indent(4, prove.toString(depth - 1))
                + "\n  Goal: " + goalStr
                + ((suffices) ? "\n  SUFFICES" : "");
    }

    /*************************************************************************
     * End fields and methods implementing the ExplorerNode interface:        *
     *************************************************************************/

    @Override
    public Element getLevelElement(final Document doc, final SymbolContext context) {
        final Element e = doc.createElement("AssumeProveNode");
        final Element antecedent = doc.createElement("assumes");
        final Element succedent = doc.createElement("prove");

        final SemanticNode[] assumes = getAssumes();
        for (final SemanticNode assume : assumes) antecedent.appendChild(assume.export(doc, context));

        succedent.appendChild(getProve().export(doc, context));

        e.appendChild(antecedent);
        e.appendChild(succedent);

        if (isSuffices()) e.appendChild(doc.createElement("suffices"));
        if (isBoxAssumeProve) e.appendChild(doc.createElement("boxed"));

        return e;
    }
}



