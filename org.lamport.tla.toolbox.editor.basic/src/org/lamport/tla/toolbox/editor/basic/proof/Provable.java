package org.lamport.tla.toolbox.editor.basic.proof;

import java.util.Vector;

/**
 * 
 * @author Daniel Ricketts
 * @deprecated
 */
public class Provable extends ProofTreeComponent
{

    private Vector childrenComponents;

    public Provable(int offset, int length, ProofTreeComponent parent)
    {
        super(offset, length, parent);
        childrenComponents = new Vector();
    }

    private Proof proof;

    public Proof getProof()
    {
        return proof;
    }

    public void setProof(Proof proof)
    {
        this.proof = proof;
    }

    public void addComponent(ProofTreeComponent component)
    {
        childrenComponents.add(component);
    }

}
