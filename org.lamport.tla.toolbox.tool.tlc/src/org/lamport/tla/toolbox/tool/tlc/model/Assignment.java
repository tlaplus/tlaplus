package org.lamport.tla.toolbox.tool.tlc.model;

/**
 * An equation consists of a label, a list of parameters and the right side
 * @author Simon Zambrovski
 * @version $Id$
 */
public class Assignment extends Formula
{
    public static final String ASSIGNMENT_SIGN = " <- ";
    public static final String IS_MV = " [ model value ] ";

    private String label;
    private String[] params = new String[0];
    private boolean modelValue = false;

    /**
     * Constructs the assignment
     * if the right side is equals to the label, the assignment is treated as a model value assignment
     */
    public Assignment(String label, String[] params, String right)
    {

        super(right);
        this.label = label;
        this.setParams(params);
        if (this.label != null && right != null && this.label.equals(right))
        {
            // right side equals label => model value
            setModelValue(true);
        }
    }

    public String getFormula()
    {
        return getLeft() + ((this.modelValue) ? IS_MV : ASSIGNMENT_SIGN + getRight());
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
            buffer.append((i != params.length - 1) ? ", " : "");
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
     * @return the right side of the assignment, can be <code>null</code>
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
        } else
        {
            this.params = new String[0];
        }
    }

    /**
     * Returns if this assignment is to be set to the model value
     * @return
     */
    public boolean isModelValue()
    {
        return modelValue;
    }

    /**
     * Set the constant assignment to be a model value
     * @param modelValue
     */
    public void setModelValue(boolean modelValue)
    {
        if (modelValue && this.params.length != 0)
        {
            throw new IllegalArgumentException("Operators can not be instantiated with model values");
        }
        this.modelValue = modelValue;
        if (modelValue)
        {
            setRight(this.getLabel());
        }
    }

    public static String[] getArrayOfEmptyStrings(int number)
    {
        String[] array = new String[number];
        String EMPTY = new String("");
        for (int i = 0; i < number; i++)
        {
            array[i] = EMPTY;
        }
        return array;
    }
}
