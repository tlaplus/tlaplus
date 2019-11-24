package tlc2.model;

import static org.junit.Assert.*;

import org.junit.Test;

import tlc2.model.Formula;

public class FormulaTest {

	@Test
	public void testUnnamed() {
		Formula formula = new Formula("TRUE");
		assertFalse(formula.isNamed());
		assertEquals("TRUE", formula.getRightHandSide());

		formula = new Formula("LET clock[i \\in 1..(__trace_var_state)] ==\n" + 
				"   IF i = 1\n" + 
				"   THEN [ p \\in DOMAIN pc |-> 0 ]\n" + 
				"   ELSE clock[i - 1]\n" + 
				"IN clock[__trace_var_state]");
		assertFalse(formula.isNamed());
		assertEquals("LET clock[i \\in 1..(__trace_var_state)] ==\n" + 
				"   IF i = 1\n" + 
				"   THEN [ p \\in DOMAIN pc |-> 0 ]\n" + 
				"   ELSE clock[i - 1]\n" + 
				"IN clock[__trace_var_state]", formula.getRightHandSide());
	}

	@Test
	public void testNamed() {
		Formula formula = new Formula("foo == TRUE");
		assertEquals("foo", formula.getLeftHandSide());
		assertEquals("TRUE", formula.getRightHandSide());
		
		formula = new Formula("foo == LET bar == TRUE IN bar");
		assertEquals("foo", formula.getLeftHandSide());
		assertEquals("LET bar == TRUE IN bar", formula.getRightHandSide());
		
		formula = new Formula("bar == LET clock[i \\in 1..(__trace_var_state)] ==\n" + 
				"   IF i = 1\n" + 
				"   THEN [ p \\in DOMAIN pc |-> 0 ]\n" + 
				"   ELSE clock[i - 1]\n" + 
				"IN clock[__trace_var_state]");
		assertEquals("bar", formula.getLeftHandSide());
		assertEquals("LET clock[i \\in 1..(__trace_var_state)] ==\n" + 
				"   IF i = 1\n" + 
				"   THEN [ p \\in DOMAIN pc |-> 0 ]\n" + 
				"   ELSE clock[i - 1]\n" + 
				"IN clock[__trace_var_state]", formula.getRightHandSide());
	}
}
