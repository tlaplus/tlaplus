package org.lamport.tla.toolbox.tool.tlc.model;

/**
 * An equation consists of a label, a list of parameters and the right side
 * @author Simon Zambrovski
 * @version $Id$
 */
public class Assignment extends Formula
{
    public static final String ASSIGNMENT_SIGN = " <- ";

    private String label;
    private String[] params = new String[0];

    /**
     * @param formula
     */
    public Assignment(String label, String[] params, String right)
    {
        super(right);
        this.label = label;
        this.setParams(params);
    }

    public String getFormula()
    {
        return getLeft() + ASSIGNMENT_SIGN + getRight();
    }
    
    /**
     * Retrieves the left part (label with parameter list)
     * @return
     */
    public String getLeft()
    {
        return getParametrizedLabel(this.label);
    }

    /**
     * Appends parameters to the label
     * @param label
     * @return
     */
    public String getParametrizedLabel(String label)
    {
        return label + listParams();
    }

    /**
     * @return a string representation of parameter list
     */
    private String listParams()
    {
        if (params.length == 0)
        {
            return "";
        }
        StringBuffer buffer = new StringBuffer();
        buffer.append("(");
        for (int i = 0; i < params.length; i++)
        {
            buffer.append(params[i]);
            buffer.append( (i != params.length - 1) ? ", " : "");
        }
        buffer.append(")");
        return buffer.toString();
    }

    public void setFormula(String formula)
    {
        throw new UnsupportedOperationException("Not implemented yet");
        /*
        int i;
        if (formula == null || (i = formula.indexOf(ASSIGNMENT_SIGN)) == -1) 
        {
            throw new IllegalArgumentException("Wrong format of the formula");
        }
        
        setRight(formula.substring(0, i));
        */
    }

    /**
     * @return the label
     */
    public String getLabel()
    {
        return label;
    }

    /**
     * Retrieve the right part
     * @return
     */
    public String getRight()
    {
        return super.getFormula();
    }
    
    public String[] getParams()
    {
        return params;
    }

    public String toString()
    {
        return getFormula();
    }

    /**
     * Sets the right part
     * @param right
     */
    public void setRight(String right)
    {
        super.setFormula(right);
    }

    /**
     * Set parameters, the left part depends on
     * @param params
     */
    public void setParams(String[] params)
    {
        if (params != null)
        {
            this.params = params;
        } else {
            this.params = new String[0];
        }
    }

}
