package tlc2.model;

public class MCVariable {
    private final String name;
    private final String valueAsString;
    private String traceExpression;

	/**
	 * @param varName   name of the variable
	 * @param value     TLC string representation of the variable value
	 */
	public MCVariable(final String varName, final String value) {
		name = varName;
		valueAsString = value;
		traceExpression = null;
	}

	public String getName() {
		return name;
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
