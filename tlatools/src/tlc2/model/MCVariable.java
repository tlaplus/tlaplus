package tlc2.model;

public class MCVariable {
    private String name;
    private String valueAsString;
    private boolean isTraceExplorerVariable;

	/**
	 * @param varName   name of the variable
	 * @param value     TLC string representation of the variable value
	 */
	public MCVariable(final String varName, final String value) {
		name = varName;
		valueAsString = value;
		isTraceExplorerVariable = false;
	}

	public String getName() {
		return name;
	}

    /**
	 * @return the name this variable in a single line String; the name could be
	 *         multiple lines if this represents a trace explorer expression.
	 */
	public String getSingleLineName() {
		return name.replaceAll("\n", "").replaceAll("\r", "");
	}

	public String getValueAsString() {
		return valueAsString;
	}
	
	public boolean isTraceExplorerExpression() {
		return isTraceExplorerVariable;
	}
}
