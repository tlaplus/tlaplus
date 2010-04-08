package org.lamport.tla.toolbox.editor.basic.proof;



/**
 * Represents a leaf proof, i.e. a proof without any steps.
 * 
 * @author Daniel Ricketts
 * @deprecated
 */
public class LeafProof extends Proof
{
    /**
     * Constructor using initial offset and length of the leaf proof.
     * Offset is the first character of the leaf proof and length goes
     * to the end of the leaf proof.
     * 
     * @param offset
     * @param length
     * @param parent parent in the proof tree. The parent is a provable
     * for which this is a proof.
     */
    public LeafProof(int offset, int length, Provable parent)
    {
        super(offset, length, parent);
    }

}
