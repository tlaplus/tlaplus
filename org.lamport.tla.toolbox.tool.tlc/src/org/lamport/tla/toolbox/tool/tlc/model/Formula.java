package org.lamport.tla.toolbox.tool.tlc.model;

/**
 * Represent a formula
 * @author Simon Zambrovski
 * @version $Id$
 */
public class Formula
{
    public String formula;

    /**
     * Constructs a formula representation
     * @param formula
     */
    public Formula(String formula)
    {
        this.formula = formula;
    }
    
    public String toString()
    {
        return formula;
    }

}
