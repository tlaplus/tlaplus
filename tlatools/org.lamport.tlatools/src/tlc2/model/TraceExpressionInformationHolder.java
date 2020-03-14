package tlc2.model;

import java.util.List;

import tlc2.output.SpecWriterUtilities;
import util.TLAConstants;

/**
 * A container class for the relevant information about a
 * trace explorer expression. This class contains the expression,
 * the identifier which is defined to be the expression, the variable
 * that is declared for this expression, and the level of the expression.
 * 
 * @author Daniel Ricketts
 *
 */
public class TraceExpressionInformationHolder {
	/**
	 * @param expressions
	 * @param attributeName
	 * @return expressions.size() instances of {@code TraceExpressionInformationHolder}
	 */
	public static TraceExpressionInformationHolder[] createHolders(final List<Formula> expressions, final String attributeName) {
		final TraceExpressionInformationHolder[] holders = new TraceExpressionInformationHolder[expressions.size()];
	    int position = 0;
	    for (final Formula formula : expressions) {
			final String expression = formula.getFormula();
	
			if ((expression != null) && (expression.length() > 0)) {
	        	final String identifier
	        			= SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.TRACE_EXPR_DEF_SCHEME);
	        	if (formula.isNamed()) {
	        		final String varname = formula.getLeftHandSide();
	        		final String rightHandSide = formula.getRightHandSide();
					holders[position] = new TraceExpressionInformationHolder(rightHandSide, identifier, varname);
	        	} else  {
	        		final String varname
	        				= SpecWriterUtilities.getValidIdentifier(TLAConstants.Schemes.TRACE_EXPR_VAR_SCHEME);
	        		holders[position] = new TraceExpressionInformationHolder(expression, identifier, varname);
	        	}
	        }
	
	        position++;
	    }
	    
	    return holders;
	}

	
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
