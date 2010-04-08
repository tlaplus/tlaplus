package org.lamport.tla.toolbox.editor.basic.proof;

/**
 * This interface represents a proof. It provides a way of giving a single
 * interface to the two types of proofs, {@link LeafProof} and {@link NonLeafProof}.
 * 
 * @author Daniel Ricketts
 * @deprecated
 */
public abstract class Proof extends ProofTreeComponent
{

    /**
     * Projection annotation for this component.
     */
    protected FoldTuple fold;

    /**
     * Returns the projection annotation for this component.
     * 
     * @return
     */
    public FoldTuple getFold()
    {
        return fold;
    }

    public Proof(int offset, int length, Provable parent)
    {
        super(offset, length, parent);
    }

    public void setFold(FoldTuple fold)
    {
        this.fold = fold;
    }
}
