package tlc2.model;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.util.List;

import org.junit.Test;

import util.TLAConstants;

public class MCStateTest {
	
	@Test
	public void testParseRoundTrips()
	{
		testParseRoundTrip(1, "Initial predicate", "", "x = 8", "y = 7");
		testParseRoundTrip(2, "YIncr", "line 8, col 10 to line 10, col 26 of module Bla", "x = 8", "y = 15");
		testParseRoundTrip(1, "Initial predicate", "", "x = 1", "y = FALSE");
		testParseRoundTrip(2, "Next", "line 7, col 9 to line 11, col 23 of module Alias", "x = 2", "y = TRUE");
		testParseRoundTrip(3, "Next", "line 7, col 9 to line 11, col 23 of module Alias", "x = 3", "y = FALSE");
		testParseRoundTrip(4, "Next", "line 7, col 9 to line 11, col 23 of module Alias", "x = 4", "y = TRUE");
	}
	
	@Test
	public void testSimpleRecordPrinter()
	{
		final MCState input = Utils.buildState(1, "Initial predicate", "", "x = 8", "y = 7");
		final String actual = input.asSimpleRecord();
		final String[] expectedTokens = new String[] {
				TLAConstants.L_SQUARE_BRACKET,
				"x", TLAConstants.RECORD_ARROW.trim(), "8",
				TLAConstants.COMMA,
				"y", TLAConstants.RECORD_ARROW.trim(), "7",
				TLAConstants.R_SQUARE_BRACKET
		};

		String remaining = actual.trim();
		for (String expectedToken : expectedTokens)
		{
			if (remaining.startsWith(expectedToken))
			{
				remaining = remaining.substring(expectedToken.length()).trim();
			}
			else
			{
				fail(String.format("Required token [%s]; received [%s]", expectedToken, remaining));
			}
		}
	}
	
	private static void testParseRoundTrip(
			int ordinal,
			String name,
			String location,
			String ...assignments)
	{
		final MCState expected = Utils.buildState(ordinal, name, location, assignments);
		final List<String> inputLines = Utils.toTlcOutputFormat(expected);
		final String input = String.join(TLAConstants.CR, inputLines);
		final MCState actual = MCState.parseState(input);
		MCStateTest.compareStates(expected, actual);
	}
	
	private static void compareStates(final MCState expected, final MCState actual)
	{
		assertEquals(expected.getName(), actual.getName());
		// The label is not trimmed in parsing; we are maintaining backward compatibility
		assertEquals(" " + expected.getLabel(), actual.getLabel());
		assertEquals(expected.isStuttering(), actual.isStuttering());
		assertEquals(expected.isBackToState(), actual.isBackToState());
		assertEquals(expected.getStateNumber(), actual.getStateNumber());
		
		MCVariable[] expectedVars = expected.getVariables();
		MCVariable[] actualVars = actual.getVariables();
		assertEquals(expectedVars.length, actualVars.length);
		for (int i = 0; i < expectedVars.length; i++)
		{
			assertEquals(expectedVars[i].getName(), actualVars[i].getName());
			assertEquals(expectedVars[i].getValueAsString(), actualVars[i].getValueAsString());
		}
	}
}
