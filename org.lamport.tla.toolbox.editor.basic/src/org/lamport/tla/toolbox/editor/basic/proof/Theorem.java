package org.lamport.tla.toolbox.editor.basic.proof;

import java.util.Vector;

/**
 * 
 * @author Daniel Ricketts
 * @deprecated
 */
public class Theorem extends Provable
{

    Vector childrenComponents;

    public Theorem(int offset, int length, ProofTreeComponent parent)
    {
        super(offset, length, parent);
        childrenComponents = new Vector();
    }

    public void addComponent(ProofTreeComponent component)
    {
        childrenComponents.add(component);
    }

    public ProofTreeComponent[] getComponents()
    {
        return (ProofTreeComponent[]) childrenComponents.toArray(new ProofTreeComponent[childrenComponents.size()]);
    }

}
