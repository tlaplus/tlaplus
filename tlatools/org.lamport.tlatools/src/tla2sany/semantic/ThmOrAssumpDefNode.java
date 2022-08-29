// Copyright (c) 2007 Microsoft Corporation.  All rights reserved.

// last modified on Thu  2 July 2009 at 15:44:33 PST by lamport
/***************************************************************************
 * The ThmOrAssumpDefNode constructor is invoked in                         *
 * semantic/Generator.java to construct the nodes corresponding to the      *
 * definition in something like                                             *
 *                                                                          *
 *   THEOREM Foo == ...                                                     *
 *                                                                          *
 * The following are the only public methods that a tool is likely to       *
 * call.  (Search for the method to find an explanation of what it does.)   *
 *                                                                          *
 *    LevelNode getBody()                                                   *
 *    ModuleNode getOriginallyDefinedInModuleNode()                         *
 *    boolean  isTheorem()                                                  *
 *    boolean isSuffices()                                                  *
 *    ProofNode getProof()                                                  *
 *    FormalParamNode[] getParams()                                         *
 *    ModuleNode getInstantiatedFrom()                                      *
 ***************************************************************************/

package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;
import util.UniqueString;
import util.WrongInvocationException;

import java.util.*;

/***************************************************************************
 * This node represents the definition of Foo in                            *
 *                                                                          *
 *    THEOREM Foo == ...                                                    *
 *    ASSUME  Foo == ...                                                    *
 ***************************************************************************/

public class ThmOrAssumpDefNode extends SymbolNode
        implements OpDefOrLabelNode, AnyDefNode {

    public int arity = 0;
    // T.L. 2014 - the actual theorem or assumption associated with this def
    // this is required in order to simplify presentation. After all normalizations
    // we dont really need this def any more
    // this field is being set by TheoremNode or AssumeNode
    protected LevelNode thmOrAssump = null;
    /***********************************************************************
     * A theorem or assumption definition like                              *
     *                                                                      *
     *   THEOREM foo == ...                                                 *
     *                                                                      *
     * has no parameters.  However, it can acquire parameters when          *
     * the module it's in is instantiated.                                  *
     ***********************************************************************/
    ProofNode proof;
    /*************************************************************************
     * The fields used for level checking.                                    *
     *************************************************************************/
// These fields are now present in all LevelNode subclasses


    int[] maxLevels;
    int[] weights;
    /***********************************************************************
     * If this represents a theorem, then this is the value of the          *
     * TheoremNode's suffices field (which is false unless the TheoremNode  *
     * represents a SUFFICES proof step).  This is a kludge added for the   *
     * following reason.  To check if a reference to a subexpression of an  *
     * ASSUME/PROVE is legal, we need to know whether or not the            *
     * ASSUME/PROVE lies within a SUFFICES step.  However, the reference    *
     * accesses the ThmOrAssumpDefNode, while it's the TheoremNode that     *
     * contains the suffices field.  It might seem sensible to have the     *
     * ThmOrAssumpDefNode contain a pointer to the TheoremNode.  However,   *
     * that's problematic.  For one thing, instantiation creates a new      *
     * ThmOrAssumpDefNode for the imported definition, but does not create  *
     * a new TheoremNode.  So, we copy just the suffices field (which will  *
     * be false for an instantiated node because proof steps don't get      *
     * instantiated).                                                       *
     *                                                                      *
     * This field is set by setSuffices() and read by isSuffices() ;        *
     ***********************************************************************/
    int[][] minMaxLevel;
    /***********************************************************************
     * According to LevelSpec.tla, if this is the OpDefNode for the         *
     * definition of op, then op.minMaxLevel[i][k] is the minimum value of  *
     * oparg.maxLevels[k] for the i-th argument of Op.  Thus,               *
     * op.minMaxLevels[i] is a sequence whose length is the number of       *
     * arguments taken by the i-th argument of Op.  (It equals 0 if the     *
     * i-th argument of Op is not an operator argument.)                    *
     ***********************************************************************/

    boolean[] isLeibnizArg;
    boolean isLeibniz;
    private LevelNode body = null;
    private ModuleNode originallyDefinedInModule = null;
    private boolean theorem = true;
    /***********************************************************************
     * If the theorem or assumption was obtained by instantiation, then     *
     * this is the module from which it was instantiated.                   *
     ***********************************************************************/
    /***********************************************************************
     * True if a theorem, false if an assumption.                           *
     ***********************************************************************/
    private boolean suffices = false;
    /*************************************************************************
     * The following field is used to implement the OpDefOrLabel interface.   *
     * It is a hashtable of OpDefNode objects representing labels within      *
     * the body that are not within the scope of an inner label or LET        *
     * definition.                                                            *
     *************************************************************************/
    private Hashtable<UniqueString, LabelNode> labels = null;
    private FormalParamNode[] params = new FormalParamNode[0];
    /**********************************************************************
     * The proof, if there is one; else null.  Obviously, only a theorem   *
     * can have a proof.                                                   *
     **********************************************************************/

    private ModuleNode instantiatedFrom = null;
    /**
     * The source field and its methods was added by LL on 15 June 2010.
     * I don't know why it wasn't added to this class when it was added
     * to OpDefNode.  However, it's needed by the Toolbox, so it's being
     * added now by trying to duplicate what was done for OpDefNode
     */
    private ThmOrAssumpDefNode source = null;
    /***********************************************************************
     * The name of a theorem or assumption has no parameters.               *
     ***********************************************************************/

    // Modified by LL on 30 Oct 2012 to handle locally instantiated theorems
    // and assumptions.
    private boolean local = false;
    private boolean[][][] opLevelCond;

    /*************************************************************************
     * The Constructor.                                                      *
     *************************************************************************/
    public ThmOrAssumpDefNode(
            final UniqueString name,       // The thm/assump name.
            final boolean thm,        // true if a theorem, false if an assump.
            final LevelNode exp,        // The body
            final ModuleNode oModNode,   // Name of module.
            final SymbolTable st,         // The current value of
            // Generator.symbolTable
            final TreeNode stn,            // The syntax node.
            final FormalParamNode[] parms, // The parameters, or null if none.
            final ModuleNode iFrom,      // The instantiatedFrom field.
            final ThmOrAssumpDefNode src   // The source field.
    ) {
        super(ThmOrAssumpDefKind, stn, name);
        this.theorem = thm;
        this.body = exp;
        this.originallyDefinedInModule = oModNode;
        /*********************************************************************
         * Note that when this theorem or assumption is instantiated with a   *
         * parameter substitution, then the newly created ThmOrAssumpDefNode  *
         * has this field set to the instantiating module.  Thus, this field  *
         * is not useful to track down the module of origin of a theorem.     *
         *********************************************************************/
        // On 1 Nov 2012,, LL moved the following two statements to here from
        // the end of the constructor.  It's necessary for the source field to be
        // set before addSymbol is called.
        this.instantiatedFrom = iFrom;
        this.source = src;

        if (st != null) {
            st.addSymbol(name, this);
        }
        /*********************************************************************
         * By some magic, this eventually puts the name into the current      *
         * module's context.                                                  *
         *********************************************************************/
        if (parms != null) {
            this.params = parms;
            this.arity = parms.length;
        }
    }

    /*************************************************************************
     * A place-holder constructor and a method for setting the remaining      *
     * fields.  It is used in Generator.processTheorem, where the object      *
     * needs to be created before its body is generated.  This method is      *
     * not used when created a ThmOrAssumpDefNode by instantiation, so        *
     * getInstantitedFrom will be null for this object.                       *
     *************************************************************************/
    public ThmOrAssumpDefNode(final UniqueString name, final TreeNode stn) {
        super(ThmOrAssumpDefKind, stn, name);
    }

    public Hashtable<UniqueString, LabelNode> getLabelsHT() {
        /***********************************************************************
         * Return the labels field.  Used to "clone" an OpDefNode for module    *
         * instantiation.                                                       *
         ***********************************************************************/
        return labels;
    }

    @Override
    public ThmOrAssumpDefNode getSource() {
        if (source == null) {
            return this;
        }
        return source;
    }

    public void construct(
            final boolean thm,       // true if a theorem, false if an assump.
            final LevelNode exp,       // The body
            final ModuleNode oModNode,  // Name of module.
            final SymbolTable st,        // The current value of
            // Generator.symbolTable
            final FormalParamNode[] parms // The parameters, or null if none.
    ) {
        this.theorem = thm;
        this.body = exp;
        this.originallyDefinedInModule = oModNode;
        if (st != null) {
            st.addSymbol(name, this);
        }
        /*********************************************************************
         * By some magic, this eventually puts the name into the current      *
         * module's context.                                                  *
         *********************************************************************/
        if (parms != null) {
            this.params = parms;
            this.arity = parms.length;
        }
    }

    /*************************************************************************
     * The methods.                                                           *
     *************************************************************************/
    public LevelNode getBody() {
        return this.body;
    }

    /***********************************************************************
     * Note: this is a LevelNode rather than an ExprNode because it could   *
     * be either an ExprNode, AssumeProve node, or an APSubstInNode whose   *
     * body is either an ExprNode or an AssumeProve node.  To check if a    *
     * node N is an ExprNode, use the test                                  *
     *                                                                      *
     *    N instanceof ExprNode                                             *
     ***********************************************************************/

    public ModuleNode getOriginallyDefinedInModuleNode()
    /***********************************************************************
     * This is the module for which the node was created, which for a       *
     * theorem or assumption instantiated with substitution is not the      *
     * module from which the theorem or assumption came.                    *
     ***********************************************************************/
    {
        return originallyDefinedInModule;
    }
    /***********************************************************************
     * Returns true iff the body is an ExprNode (rather than an             *
     * AssumeProveNode or APSubstInNode).                                   *
     ***********************************************************************/

    public ModuleNode getInstantiatedFrom() {
        return this.instantiatedFrom;
    }

    /***********************************************************************
     * If the theorem or assumption was obtained by instantiation, then     *
     * this is the module from which it was instantiated.  Otherwise, it    *
     * is null.                                                             *
     ***********************************************************************/

    public boolean isTheorem() {
        return this.theorem;
    }

    public boolean isSuffices() {
        return this.suffices;
    }

    void setSuffices() {
        this.suffices = true;
    }

//  public final ModuleNode getModuleNode() { return this.moduleNode; }

    /*************************************************************************
     * Return the proof of the theorem, which is null unless this is a        *
     * theorem and it has a proof.                                            *
     *************************************************************************/
    public final ProofNode getProof() {
        return this.proof;
    }

    @Override
    public final FormalParamNode[] getParams() {
        return this.params;
    }

    public final boolean isExpr() {
        return this.body instanceof ExprNode;
    }

    /*************************************************************************
     * Implementations of the abstract methods of the SymbolNode superclass.  *
     *************************************************************************/
    @Override
    public final int getArity() {
        return this.arity;
    }

    @Override
    public final boolean isLocal() {
        return local;
    }

// On 24 Oct 2012 replaced the following levelCheck method with the current
// one, which was obtained by cloning the method from OpDefNode with some
// simplifications that were possible because a theorem or assumption, unlike
// and ordinary definition, cannot appear in the scope of a RECURSIVE declaration.
// He also made the ThmOrAssumpDefNode implement the AnyNode interface.
// See the comments in AnyDefNode.java for an explanation of why.

    /***********************************************************************
     * Theorem and assumption definitions are local iff imported with a     *
     * LOCAL instance.                                                      *
     ***********************************************************************/
    public final void setLocal(final boolean localness) {
        local = localness;
    }

    @Override
    public final boolean match(final OpApplNode test, final ModuleNode mn) {
        /***********************************************************************
         * True iff the current object has the same arity as the node operator  *
         * of the OpApplNode test.                                              *
         ***********************************************************************/
        final SymbolNode odn = test.getOperator();
        return odn.getArity() == 0;
    }

    /***********************************************************************
     * Sets the set of labels.                                              *
     ***********************************************************************/

    @Override
    public LabelNode getLabel(final UniqueString us) {
        /***********************************************************************
         * If the hashtable `labels' contains a LabelNode with name `us',       *
         * then that LabelNode is returned; otherwise null is returned.         *
         ***********************************************************************/
        if (labels == null) {
            return null;
        }
        return labels.get(us);
    }

    @Override
    public boolean addLabel(final LabelNode odn) {
        /***********************************************************************
         * If the hashtable `labels' contains no OpDefNode with the same name   *
         * as odn, then odn is added to the set and true is return; else the    *
         * set is unchanged and false is returned.                              *
         ***********************************************************************/
        if (labels == null) {
            labels = new Hashtable<>();
        }
        if (labels.containsKey(odn.getName())) {
            return false;
        }
        labels.put(odn.getName(), odn);
        return true;
    }

    @Override
    public LabelNode[] getLabels() {
        /***********************************************************************
         * Returns an array containing the Label objects in the hashtable       *
         * `labels'.                                                            *
         ***********************************************************************/
        if (labels == null) {
            return new LabelNode[0];
        }
        final ArrayList<LabelNode> v = new ArrayList<>();
        final Enumeration<LabelNode> e = labels.elements();
        while (e.hasMoreElements()) {
            v.add(e.nextElement());
        }
        final LabelNode[] retVal = new LabelNode[v.size()];
        for (int i = 0; i < v.size(); i++) {
            retVal[i] = v.get(i);
        }
        return retVal;
    }

    /*************************************************************************
     * The following methods implement the OpDefOrLabel interface.            *
     *                                                                        *
     * These are the same as the other classes that implement the interface.  *
     * There doesn't seem to be any easy way to write these methods only      *
     * once.                                                                  *
     *************************************************************************/
    @Override
    public void setLabels(final Hashtable<UniqueString, LabelNode> ht) {
        labels = ht;
    }

    /***********************************************************************
     * If this is the OpDefNode for the definition of op, then              *
     * isLeibnizArg[i] is true iff the i-th argument of op is Leibniz, and  *
     * isLeibniz = \A i : isLeibnizArg[i]                                   *
     ***********************************************************************/
    @Override
    public boolean[] getIsLeibnizArg() {
        return isLeibnizArg;
    }

    @Override
    public boolean getIsLeibniz() {
        return isLeibniz;
    }

    /***********************************************************************
     * According to LevelSpec.tla, if thisnode defines op,                  *
     * then op.opLevelCond[i][j][k] is true iff                             *
     * the i-th argument of op is an operator argument opArg, and the       *
     * definition of op contains an expression in which the j-th formal     *
     * parameter of the definition of op appears within the k-th argument   *
     * of opArg.                                                            *
     ***********************************************************************/
    @Override
    public final boolean levelCheck(final int itr) {
        if (this.levelChecked >= itr) {
            return this.levelCorrect;
        }
        this.levelChecked = itr;

        /***********************************************************************
         * Initialize maxLevels to the least restrictive value and weights to 0.*
         * Initialize isLeibniz and all isLeibniz[i] to true.                   *
         ***********************************************************************/
        this.maxLevels = new int[this.params.length];
        this.weights = new int[this.params.length];
        for (int i = 0; i < this.params.length; i++) {
            this.maxLevels[i] = MaxLevel;
            this.weights[i] = 0;
            this.isLeibniz = true;
            this.isLeibnizArg = new boolean[this.params.length];
            this.isLeibnizArg[i] = true;
        }


        // Level check the body:
        this.levelCorrect = this.body.levelCheck(itr);
        this.level = this.body.getLevel();

        final SetOfLevelConstraints lcSet = this.body.getLevelConstraints();
        for (int i = 0; i < this.params.length; i++) {
            final Integer plevel = lcSet.get(params[i]);
            if (plevel != null) {
                this.maxLevels[i] = plevel;
            }
        }

        for (int i = 0; i < this.params.length; i++) {
            if (this.body.getLevelParams().contains(this.params[i])) {
                this.weights[i] = this.weights[i];
            }
        }

        this.minMaxLevel = new int[this.params.length][];
        final SetOfArgLevelConstraints alcSet = this.body.getArgLevelConstraints();
        for (int i = 0; i < this.params.length; i++) {
            final int alen = this.params[i].getArity();
            this.minMaxLevel[i] = new int[alen];
            for (int j = 0; j < alen; j++) {
                final Integer alevel = alcSet.get(new ParamAndPosition(this.params[i], j));
                this.minMaxLevel[i][j] = Objects.requireNonNullElse(alevel, MinLevel);
            }
        }

        this.opLevelCond = new boolean[this.params.length][this.params.length][];
        final HashSet<ArgLevelParam> alpSet = this.body.getArgLevelParams();
        for (int i = 0; i < this.params.length; i++) {
            for (int j = 0; j < this.params.length; j++) {
                this.opLevelCond[i][j] = new boolean[this.params[i].getArity()];
                for (int k = 0; k < this.params[i].getArity(); k++) {
                    final ArgLevelParam alp = new ArgLevelParam(this.params[i], k, this.params[j]);
                    this.opLevelCond[i][j][k] = alpSet.contains(alp);
                }
            }
        }

        this.levelParams.addAll(this.body.getLevelParams());
        this.allParams.addAll(this.body.getAllParams());
        this.nonLeibnizParams.addAll(this.body.getNonLeibnizParams());
        for (int i = 0; i < this.params.length; i++) {
            this.levelParams.remove(this.params[i]);
            this.allParams.remove(this.params[i]);
            if (this.nonLeibnizParams.contains(this.params[i])) {
                /*******************************************************************
                 * The i-th argument is non-Leibniz if this.params[i] is in the     *
                 * body's nonLeibnizParams hashset (and hence now in this node's    *
                 * nonLeibnizParams hashset.                                        *
                 *******************************************************************/
                this.nonLeibnizParams.remove(this.params[i]);
                this.isLeibnizArg[i] = false;
                this.isLeibniz = false;
            }
        }

        this.levelConstraints = (SetOfLevelConstraints) lcSet.clone();
        for (final FormalParamNode formalParamNode : this.params) {
            this.levelConstraints.remove(formalParamNode);
        }

        this.argLevelConstraints = (SetOfArgLevelConstraints) alcSet.clone();
        for (final FormalParamNode param : this.params) {
            final int alen = param.getArity();
            for (int j = 0; j < alen; j++) {
                this.argLevelConstraints.remove(new ParamAndPosition(param, j));
            }
        }

        for (final ArgLevelParam alp : alpSet) {
            if (!alp.op.occur(this.params) ||
                    !alp.param.occur(this.params)) {
                this.argLevelParams.add(alp);
            }
        }

        return levelCorrect;
    }

    /***************************************************************************
     * The following Asserts can be removed after debugging.                    *
     ***************************************************************************/
    @Override
    public final int getMaxLevel(final int i) {
        if (this.levelChecked == 0) {
            throw new WrongInvocationException("getMaxLevel called before levelCheck");
        }
        final int idx = (this.getArity() == -1) ? 0 : i;
        return this.maxLevels[idx];
    }

    @Override
    public final int getWeight(final int i) {
        if (this.levelChecked == 0) {
            throw new WrongInvocationException("getWeight called before levelCheck");
        }
        final int idx = (this.getArity() == -1) ? 0 : i;
        return this.weights[idx];
    }

    @Override
    public final int getMinMaxLevel(final int i, final int j) {
        if (this.levelChecked == 0) {
            throw new WrongInvocationException("getMinMaxLevel called before levelCheck");
        }
        if (this.minMaxLevel == null) {
            return ConstantLevel;
        }
        return this.minMaxLevel[i][j];
    }

    @Override
    public final boolean getOpLevelCond(final int i, final int j, final int k) {
        if (this.levelChecked == 0) {
            throw new WrongInvocationException("getOpLevelCond called before levelCheck");
        }
        if (this.opLevelCond == null) {
            return false;
        }
        return this.opLevelCond[i][j][k];
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
        return new SemanticNode[]{this.body};
    }

    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        final Integer uid = myUID;
        if (semNodesTable.get(uid) != null) return;
        semNodesTable.put(uid, this);
        visitor.preVisit(this);
        if (this.body != null) {
            this.body.walkGraph(semNodesTable, visitor);
        }
        visitor.postVisit(this);
    }

    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";
        final StringBuilder ret =
                new StringBuilder("\n*ThmOrAssumpDefNode: " + this.getName().toString() +
                        "  " + super.toString(depth) +
                        " arity: " + this.arity +
                        " module: " + (originallyDefinedInModule != null
                        ? originallyDefinedInModule.getName().toString()
                        : "<null>"));
        if (instantiatedFrom != null) {
            ret.append(" instantiatedFrom: ").append(instantiatedFrom.getName());
        }
        if (params != null) {
            final StringBuilder tempString = new StringBuilder("\nFormal params: " + params.length);
            for (final FormalParamNode param : params) {
                tempString.append(Strings.indent(2, ((param != null)
                        ? param.toString(depth - 1)
                        : "\nnull")));
            }
            ret.append(Strings.indent(2, tempString.toString()));
        }
        if (body != null) {
            ret.append(Strings.indent(2,
                    "\nisTheorem(): " + theorem +
                            "\nBody:" +
                            Strings.indent(2, this.body.toString(depth - 1)) +
                            "\nsuffices: " + this.isSuffices()));
        } // if
        /***********************************************************************
         * The following is the same for all classes that implement the         *
         * OpDefOrLabelNode interface.                                          *
         ***********************************************************************/
        if (labels != null) {
            ret.append("\n  Labels: ");
            final Enumeration<UniqueString> list = labels.keys();
            while (list.hasMoreElements()) {
                ret.append(list.nextElement().toString()).append("  ");
            }
        } else {
            ret.append("\n  Labels: null");
        }

        return ret.toString();
    }

    /**
     *
     */
    @Override
    protected String getNodeRef() {
        if (theorem) {
            assert (thmOrAssump instanceof TheoremNode);
            return "TheoremDefRef";
        } else {
            assert (thmOrAssump instanceof AssumeNode);
            return "AssumeDefRef";
        }
    }

    @Override
    protected Element getSymbolElement(final Document doc, final tla2sany.xml.SymbolContext context) {
        assert (this.body != null); //A theorem or assumption definition without a body does not make sense.
        Element e;
        if (theorem) {
            e = doc.createElement("TheoremDefNode");
        } else {
            e = doc.createElement("AssumeDef");
        }

        e.appendChild(appendText(doc, "uniquename", getName().toString()));
        e.appendChild(body.export(doc, context));
        return e;
    }

    /* overrides LevelNode.export and exports a UID reference instad of the full version*/
    @Override
    public Element export(final Document doc, final SymbolContext context) {
        // first add symbol to context
        context.put(this, doc);
        final Element e = doc.createElement(getNodeRef());
        e.appendChild(appendText(doc, "UID", Integer.toString(myUID)));
        return e;
    }
}
