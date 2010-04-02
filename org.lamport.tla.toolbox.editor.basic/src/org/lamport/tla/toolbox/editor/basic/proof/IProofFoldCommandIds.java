package org.lamport.tla.toolbox.editor.basic.proof;

/**
 * Ids for proof folding commands.
 * 
 * @author Daniel Ricketts
 *
 */
public interface IProofFoldCommandIds
{

    public static final String FOLD_UNUSABLE = "org.lamport.tla.toolbox.editor.basic.FoldUnusableSteps";

    /**
     * Collapses all proofs.
     */
    public static final String FOLD_ALL_PROOFS = "org.lamport.tla.toolbox.editor.basic.FoldAllProofs";
    /**
     * Expands all proofs.
     */
    public static final String EXPAND_ALL_PROOFS = "org.lamport.tla.toolbox.editor.basic.ExpandAllProofs";
    /**
     * Expands the current subtree.
     */
    public static final String EXPAND_SUBTREE = "org.lamport.tla.toolbox.editor.basic.ExpandSubtree";
    /**
     * Collapses the current subtree.
     */
    public static final String COLLAPSE_SUBTREE = "org.lamport.tla.toolbox.editor.basic.CollapseSubtree";
    /**
     * Shows the proof of the step with the cursor and collapses all
     * subproofs.
     */
    public static final String SHOW_IMMEDIATE = "org.lamport.tla.toolbox.editor.basic.ShowImmediate";

}
