package org.lamport.tla.toolbox.tool.tlc.model;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

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

	// MAK 03/2019: This methods below appear redundant to the Assignment subclass
	// but I don't have time to look into it.
    
    public boolean isNamed()  {
    	return !getLeftHandSide().equals("");
    }
    
    // DOTALL to match beyond line endings.
    private static final Pattern pattern = Pattern.compile("^\\s*(\\w+)\\s*==(.*)$", Pattern.DOTALL);
    
    public String getLeftHandSide() {
		final Matcher matcher = pattern.matcher(this.formula);
		if (matcher.find()) {
			return matcher.group(1).trim();
		}
		return "";
    }
    
    public String getRightHandSide() {
		final Matcher matcher = pattern.matcher(this.formula);
		if (matcher.find()) {
			return matcher.group(2).trim();
		}
		return "";
    }
}
