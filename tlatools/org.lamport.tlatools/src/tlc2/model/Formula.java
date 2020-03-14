package tlc2.model;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Representation of a formula.
 * @author Simon Zambrovski
 */
public class Formula {
    /**
     * De-serialize formula list, to a list of formulas, that are selected (have a leading "1")
     * 
     * The first character of the formula is used to determine if the formula is enabled in the model 
     * editor or not. This allows the user to persist formulas, which are not used in the current model 
     */
	public static List<Formula> deserializeFormulaList(final List<String> serializedList) {
		final ArrayList<Formula> result = new ArrayList<>(serializedList.size());
		for (final String entry : serializedList) {
			if ("1".equals(entry.substring(0, 1))) {
				result.add(new Formula(entry.substring(1)));
			}
		}
		return result;
	}
	
    // DOTALL to match beyond line endings.
    private static final Pattern PATTERN = Pattern.compile("^\\s*(\\w+)\\s*==(.*)$", Pattern.DOTALL);
    
	
    private String formula;

    /**
     * Constructs a formula representation
     * @param formula
     */
	public Formula(String formulaString) {
		formula = formulaString;
	}

	/**
	 * Retrives formula
	 * 
	 * @return
	 */
	public String getFormula() {
		return formula;
	}

	@Override
	public String toString() {
		return formula;
	}

	/**
	 * @param formulaString
	 */
	public void setFormula(String formulaString) {
		formula = formulaString;
	}

	// MAK 03/2019: This methods below appear redundant to the Assignment subclass
	// but I don't have time to look into it.
    
    public boolean isNamed()  {
    	return !getLeftHandSide().equals(getFormula());
    }
    
    public String getLeftHandSide() {
		final Matcher matcher = PATTERN.matcher(this.formula);
		if (matcher.find()) {
			return matcher.group(1).trim();
		}
		return getFormula();
    }
    
    public String getRightHandSide() {
		final Matcher matcher = PATTERN.matcher(this.formula);
		if (matcher.find()) {
			return matcher.group(2).trim();
		}
		return getFormula();
    }
}
