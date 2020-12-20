package tlc2.model;

import static org.junit.Assert.assertEquals;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;

public class MCErrorTest {
	
	@Test
	public void testGetErrorMessage()
	{
		final String expected = "this is an error message";
		MCError actual = new MCError(expected);
		assertEquals(expected, actual.getMessage());
	}
	
	@Test
	public void testUpdateStatesForTraceExpressions()
	{
		MCError error = new MCError();
		MCState[] states = new MCState[] {
				Utils.buildState(1, "init", "", "x = 1"),
				Utils.buildState(2, "next", "", "x = 2"),
				Utils.buildState(3, "next", "", "x = 3"),
				Utils.buildState(5, "next", "", "x = 4"),
				Utils.buildState(6, "next", "", "x = 5")
		};
		
		for (MCState state : states)
		{
			error.addState(state);
		}
		
		Map<String, String> map = new HashMap<String, String>();
		map.put("x", "y");
		error.updateStatesForTraceExpression(map);
		
		List<MCState> actualStates = error.getStates();
		assertEquals(states.length, actualStates.size());
		for (MCState actualState : actualStates)
		{
			MCVariable[] actualVariables = actualState.getVariables();
			assertEquals(1, actualVariables.length);
			for (MCVariable actualVariable : actualVariables)
			{
				assertEquals("x", actualVariable.getName());
				assertEquals("y", actualVariable.getSingleLineDisplayName());
			}
		}
	}
}
