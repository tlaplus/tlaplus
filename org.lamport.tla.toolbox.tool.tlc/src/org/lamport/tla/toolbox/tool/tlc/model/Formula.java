package org.lamport.tla.toolbox.tool.tlc.model;

/**
 * Representation of a formula.
 * @author Simon Zambrovski
 * @version $Id$
 */
public class Formula
{
    private String formula;

    /**
     * Constructs a formula representation
     * @param formula
     */
    public Formula(String formula)
    {
        this.formula = formula;
    }
    
    /**
     * Retrives formula
     * @return
     */
    public String getFormula()
    {
        return formula;
    }
    
    public String toString()
    {
        return formula;
    }

    /**
     * @param formula2
     */
    public void setFormula(String formula)
    {
        this.formula = formula;
    }

}
