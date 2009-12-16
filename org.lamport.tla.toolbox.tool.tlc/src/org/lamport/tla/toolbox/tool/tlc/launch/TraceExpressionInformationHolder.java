package org.lamport.tla.toolbox.tool.tlc.launch;

/**
 * A container class for the relevant information about a
 * trace explorer expression. This class contains the expression,
 * the identifier which is defined to be the expression, the variable
 * that is declared for this expression, and the level of the expression.
 * 
 * @author Daniel Ricketts
 *
 */
public class TraceExpressionInformationHolder
{

    /*
     * The expression that the user wants to be evaluated at every
     * state of the trace. 
     */
    private String expression;
    /*
     * The identifier that is defined to be the expression.
     */
    private String identifier;
    /*
     * The variable name that is declared for this expression.
     */
    private String variableName;
    /*
     * The level of the trace expression
     */
    private int level;

    public void setExpression(String expression)
    {
        this.expression = expression;
    }

    public void setIdentifier(String identifier)
    {
        this.identifier = identifier;
    }

    public void setVariableName(String variableName)
    {
        this.variableName = variableName;
    }

    public void setLevel(int level)
    {
        this.level = level;
    }

    public TraceExpressionInformationHolder(String expression, String identifier, String variableName)
    {
        this.expression = expression;
        this.identifier = identifier;
        this.variableName = variableName;
    }

    public String getExpression()
    {
        return expression;
    }

    public String getIdentifier()
    {
        return identifier;
    }

    public String getVariableName()
    {
        return variableName;
    }

    public int getLevel()
    {
        return level;
    }

}
