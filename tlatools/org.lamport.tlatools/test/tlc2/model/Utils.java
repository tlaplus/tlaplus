package tlc2.model;

import java.util.ArrayList;
import java.util.List;

import tla2sany.st.Location;

/**
 * Some helper functions for dealing with various TLC model class types.
 */
public class Utils {

	public static MCState buildState(
			final int ordinal,
			final String name,
			final String location,
			final String ...assignments)
	{
		MCVariable[] variables = new MCVariable[assignments.length];
		for (int i = 0; i < assignments.length; i++)
		{
			String assignment = assignments[i];
			String[] split = assignment.split("=");
			variables[i] = new MCVariable(split[0].trim(), split[1].trim());
		}
		
		return new MCState(
				variables,
				name,
				Utils.toLabelFormat(name, location),
				Location.parseLocation(location),
				false,
				false,
				ordinal);
	}
	
	public static String toLabelFormat(String name, String location)
	{
		String label = String.format("%s %s", name, location).trim();
		return String.format("<%s>", label);
	}
	
	public static List<String> toTlcOutputFormat(final MCState state)
	{
		List<String> inputLines = new ArrayList<String>();
		inputLines.add(String.format("%d: %s", state.getStateNumber(), state.getLabel()));
		for (MCVariable variable : state.getVariables())
		{
			inputLines.add(String.format("/\\ %s = %s", variable.getName(), variable.getValueAsString()));
		}

		return inputLines;
	}
}
