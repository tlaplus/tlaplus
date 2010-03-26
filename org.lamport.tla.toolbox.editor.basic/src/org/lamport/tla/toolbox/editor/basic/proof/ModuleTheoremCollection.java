package org.lamport.tla.toolbox.editor.basic.proof;

import java.util.ArrayList;

/**
 * Contains a collection of the {@link Theorem} in
 * a module.
 * 
 * @author Daniel Ricketts
 *
 */
public class ModuleTheoremCollection
{
    
    /**
     * The theorems in the module.
     */
    private ArrayList theorems;

    /**
     * @param theorems the theorems to set, should be a list of {@link Theorem}.
     */
    public void setTheorems(ArrayList theorems)
    {
        this.theorems = theorems;
    }

    /**
     * 
     * Returns a list of the {@link Theorem} in the module.
     * 
     * @return the theorems
     */
    public Theorem[] getTheorems()
    {
        return (Theorem[]) theorems.toArray();
    }
    
    /**
     * Adds a {@link Theorem} to the collection.
     * 
     * @param theorem
     */
    public void addTheorem(Theorem theorem)
    {
        theorems.add(theorem);
    }

}
