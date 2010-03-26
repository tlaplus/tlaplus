package org.lamport.tla.toolbox.editor.basic.proof;

import java.util.ArrayList;

/**
 * Represents a non-leaf proof, i.e. one that has steps.
 * 
 * @author Daniel Ricketts
 *
 */
public class NonLeafProof extends Proof
{

    /**
     * A list of {@link Provable}.
     */
    private ArrayList steps;

    /**
     * Constructor using initial offset and length of the leaf proof.
     * Offset is the first character of the non leaf proof and length goes
     * to the end of the last character contained within the scope of this proof.
     * 
     * @param offset
     * @param length
     * @param parent parent in the proof tree. The parent is a provable
     * for which this is a proof.
     */
    public NonLeafProof(int offset, int length, Provable parent)
    {
        super(offset, length, parent);
        steps = new ArrayList();
    }

    public void addStep(Provable proofStep)
    {
        steps.add(proofStep);
    }

}
