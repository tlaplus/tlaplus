package tlc2.model;

import tla2sany.st.Location;

import java.util.ArrayList;
import java.util.List;

/**
 * Some helper functions for dealing with various TLC model class types.
 */
public class Utils {

    public static MCState buildState(
            final int ordinal,
            final String name,
            final String location,
            final String... assignments) {
        final MCVariable[] variables = new MCVariable[assignments.length];
        for (int i = 0; i < assignments.length; i++) {
            final String assignment = assignments[i];
            final String[] split = assignment.split("=");
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

    public static String toLabelFormat(final String name, final String location) {
        final String label = String.format("%s %s", name, location).trim();
        return String.format("<%s>", label);
    }

    public static List<String> toTlcOutputFormat(final MCState state) {
        final List<String> inputLines = new ArrayList<>();
        inputLines.add(String.format("%d: %s", state.getStateNumber(), state.getLabel()));
        for (final MCVariable variable : state.getVariables()) {
            inputLines.add(String.format("/\\ %s = %s", variable.getName(), variable.getValueAsString()));
        }

        return inputLines;
    }
}
