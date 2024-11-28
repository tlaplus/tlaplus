package tlc2.model;

/**
 * An Assignment consists of a label, a list of parameters and the right side.
 * e.G. <code>F(_, _, _,) <- foo</code>. <code>F</code> is the label, <code>foo</code> is the 
 * right side, and there are three parameters. Because of the fact, that usually the user 
 * wants to specify <code>foo</code> as a function of parameters, the parameters can be named. 
 * So <code>F(a, b, c) <- foo(a, b) + c<code> the three parameters has names <code>a, b, c</code>.  
 * <br><br>
 * The label of an assignment is immutable. The parameters and the right side can be changed. 
 * <br><br>
 * The right side of assignments with no parameters has different meanings depending on the {@link Assignment#modelValue}.
 * If the value of {@link Assignment#modelValue} is <code>false</code>, the right side is treated as an ordinary assignment.
 * <br>
 * If the value of {@link Assignment#modelValue} is <code>true</code>, the assignment is treated as a assignments of 
 * model value(s) to a constant. If the right side is equals to the label of the assignment, it is considered, that the 
 * assignment of type <code>F = F</code> is used. Otherwise, the right side is interpreted as a set of model values and the 
 * assignment of type <code>F = {f_1, f_2, f_3}</code> with <code>f_1 = f_1, f_2 = f_2, f_3 = f_3</code>.
 * <br> 
 * Especially, the right side is parsed using {@link TypedSet#parseSet(String)}. The information whether the set of model values 
 * is typed or not is not saved explicitly, but is based on the syntax of the set. The set <code>{p_1, p_2, p_3}</code> is typed 
 * (type p), the set <code>{k_1, i_2, 3}</code> is untyped.
 * <br>
 * For assignments with at least one parameter, the value of the {@link Assignment#modelValue} is ignored.
 * <br>
 * <br>
 * @author Simon Zambrovski
 * @version $Id$
 */
public class Assignment extends Formula {
    public static final String ASSIGNMENT_SIGN = " <- ";
    public static final String IS_MV = " [ model value ] ";
    public static final String SYMMETRICAL = " <symmetrical> ";

    
    private String label;
    private String[] params = new String[0];
    private boolean modelValue = false;
    private boolean symmetry = false;
    private TypedSet setOfModelValues = null;

    /**
     * Constructs the assignment
     * if the right side is equals to the label, the assignment is treated as a model value assignment
     */
	public Assignment(String label, String[] params, String right) {
        super(right);
        this.label = label;
        this.setParams(params);
		if ((this.label != null) && (right != null) && this.label.equals(right)) {
            // right side equals label => model value
            setModelValue(true);
        }
    }

    public String getFormula() {
    	return getFormula("");
    }

    public String getFormula(String tab)
    {
        StringBuffer buffer = new StringBuffer(getLeft());
        buffer.append(tab);
        buffer.append(ASSIGNMENT_SIGN);
        
        if (this.modelValue)
        {
            buffer.append(IS_MV);
            if (isSetOfModelValues()) 
            {
                if (this.isSymmetricalSet())
                {
                    buffer.append(SYMMETRICAL);
                    buffer.append(getFormattedRight());
                } else {
                    // print out the set
                    buffer.append(getFormattedRight());                    
                }
            } else 
            {
                // a single value, nothing to print
            }
        } else
        {
            buffer.append(getFormattedRight());
        }

        return buffer.toString();
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
     * @param id
     * @return
     */
    public String getParametrizedLabel(String id)
    {
        return id + listParams();
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
        final StringBuilder buffer = new StringBuilder();
        buffer.append('(');
        for (int i = 0; i < params.length; i++)
        {
            buffer.append(params[i]);
            buffer.append((i != params.length - 1) ? ", " : "");
        }
        buffer.append(')');
        return buffer.toString();
    }

    public void setFormula(String formula)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }

    /**
     * @return the label
     */
    public String getLabel()
    {
        return label;
    }

    /**
     * @return "bar" for a assignment "frob!bar"
     */
    public String getLocalLabel() {
		final int beginIndex = label.lastIndexOf("!") + 1;
		return label.substring(beginIndex);
    }
    
    /**
     * Retrieve the right part
     * @return the right side of the assignment, can be <code>null</code>
     */
    public String getRight()
    {
        return super.getFormula();
    }

    /**
     * Retrieves a formatted version of the right side 
     * @return right side ending with ... iff \n is contained in the right side
     */
    public String getFormattedRight()
    {
        String tempRight = getRight();
        if (tempRight == null) 
        {
            return null;
        }
        int i = -1;
        if ( (i = tempRight.indexOf("\n")) != -1) 
        {
            tempRight = tempRight.substring(0, i + 1) + " ..."; 
        }
        return tempRight;
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
	public synchronized void setRight(String right) {
		super.setFormula(right);
		setOfModelValues = null;
	}

    /**
     * Set parameters, the left part depends on
     * @param params
     * 
     * Modified by LL on 11 Nov 2009 to trim spaces off the ends of 
     * the parameters.
     */
    public void setParams(String[] params)
    {
        if (params != null)
        {
            this.params = params;
            for (int i = 0; i < this.params.length; i++) {
                this.params[i] = this.params[i].trim();
            }
        } else
        {
            this.params = new String[0];
        }
    }

    /**
     * @return if this assignment is to be set to the model value
     */
    public boolean isModelValue()
    {
        return modelValue;
    }
    
    /**
     * @return true iff model value but not a set of values
     */
    public boolean isSimpleModelValue() {
    	return isModelValue() && !isSetOfModelValues();
    }
    
    /**
     * @return true, iff the assignment is a set of model values
     */
	public boolean isSetOfModelValues() {
        return modelValue && !getLabel().equals(getRight());
    }
	
	/**
	 * @return the TypedSet for model values if {@link #isSetOfModelValues()} returns true, otherwise null
	 */
	public synchronized TypedSet getSetOfModelValues() {
		if (isSetOfModelValues()) {
			if (setOfModelValues == null) {
				setOfModelValues = TypedSet.parseSet(getRight());
			}
			
			return setOfModelValues;
		}
		
		return null;
	}

    /**
     * @return true, if the set of model values is symmetrical and "nosymmetry" java property is false
     */
	public boolean isSymmetricalSet() {
		return !Boolean.getBoolean("nosymmetry") && symmetry;
    }

    /**
     * Sets the symmetry property for a set of model values 
     * @param isSymmetric
     */
    public void setSymmetric(boolean isSymmetric)
    {
        if (isSymmetric && !modelValue)
        {
            throw new IllegalArgumentException("Current assignment is not a set of model values");
        }
        this.symmetry = isSymmetric;
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


    /** 
     * compares if the signature (label and the number of parameters matches)
     */
    public boolean equalSignature(Assignment obj)
    {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (label == null)
        {
            if (obj.label != null)
                return false;
        } else if (!label.equals(obj.label))
            return false;

        return (params.length == obj.params.length);
    }
    
    public String prettyPrint() {
    	return prettyPrint("");
    }
    
    public String prettyPrint(final String delim) {
    	final StringBuffer buf = new StringBuffer();
    	if (!isModelValue()) {
    		return getFormula(delim);
    	} else if (isSetOfModelValues()) {
    		buf.append(getLeft());
    		buf.append(delim);
    		buf.append(ASSIGNMENT_SIGN);
   			if (isSymmetricalSet()) {
   				buf.append("s");
   			}
   			buf.append(getFormattedRight());
  		} else {
			// Ordinary model value, just skip the value (no point showing "X <-
			// X").
   			buf.append(getLeft());
    	}
    	return buf.toString();
    }
    
}
