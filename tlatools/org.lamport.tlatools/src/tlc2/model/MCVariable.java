package tlc2.model;

import tlc2.output.EC;
import tlc2.value.IValue;
import util.Assert;

public class MCVariable {
    private final String name;
    private final String valueAsString;
	private final IValue tlcValue;
    private String traceExpression;

	/**
	 * @param varName   name of the variable
	 * @param value     TLC string representation of the variable value
	 */
	public MCVariable(final String varName, final String value) {
		Assert.check(varName != null, EC.GENERAL);
		name = varName;
		Assert.check(value != null, EC.GENERAL);
		valueAsString = value;
		traceExpression = null;
		this.tlcValue = null;
	}

	/**
	 * @param varName  name of the variable
	 * @param tlcValue Original TLC representation of the value
	 */
	public MCVariable(final String varName, final IValue tlcValue) {
		Assert.check(varName != null, EC.GENERAL);
		name = varName;
		valueAsString = tlcValue != null ? tlcValue.toString() : "";
		traceExpression = null;
		this.tlcValue = tlcValue;
	}

	public String getName() {
		return name;
	}

	// `tlcValue` may be null.
	public IValue getTLCValue() {
		return tlcValue;
	}

    /**
	 * @return the name, or the trace expression if it is defined, for this variable
	 *         in a single line String; the name could be multiple lines if this
	 *         represents a trace explorer expression.
	 */
	public String getSingleLineDisplayName() {
		final String s = isTraceExplorerExpression() ? traceExpression : name;
		
		return s.replaceAll("\\n", "").replaceAll("\\r", "");
	}

	public String getValueAsString() {
		return valueAsString;
	}
	
	public String getValueAsStringReIndentedAs(final String indent) {
		final String[] split = valueAsString.split("(\\r\\n|\\r|\\n)");
		final StringBuilder sb = new StringBuilder();

		for (int i = 0; i < split.length; i++) {
			sb.append(indent).append(split[i]);
			if (i < (split.length - 1)) {
				sb.append("\n");
			}
		}
		
		return sb.toString();
	}
	
	public boolean isTraceExplorerExpression() {
		return (traceExpression != null);
	}
	
	public void setTraceExpression(final String expression) {
		traceExpression = expression;
	}
	
	public String getTraceExpression() {
		return traceExpression;
	}
}
