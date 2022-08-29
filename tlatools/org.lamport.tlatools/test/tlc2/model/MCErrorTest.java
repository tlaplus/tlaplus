package tlc2.model;

import org.junit.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;

public class MCErrorTest {

    @Test
    public void testGetErrorMessage() {
        final String expected = "this is an error message";
        final MCError actual = new MCError(expected);
        assertEquals(expected, actual.getMessage());
    }

    @Test
    public void testUpdateStatesForTraceExpressions() {
        final MCError error = new MCError();
        final MCState[] states = new MCState[]{
                Utils.buildState(1, "init", "", "x = 1"),
                Utils.buildState(2, "next", "", "x = 2"),
                Utils.buildState(3, "next", "", "x = 3"),
                Utils.buildState(5, "next", "", "x = 4"),
                Utils.buildState(6, "next", "", "x = 5")
        };

        for (final MCState state : states) {
            error.addState(state);
        }

        final Map<String, String> map = new HashMap<>();
        map.put("x", "y");
        error.updateStatesForTraceExpression(map);

        final List<MCState> actualStates = error.getStates();
        assertEquals(states.length, actualStates.size());
        for (final MCState actualState : actualStates) {
            final MCVariable[] actualVariables = actualState.getVariables();
            assertEquals(1, actualVariables.length);
            for (final MCVariable actualVariable : actualVariables) {
                assertEquals("x", actualVariable.getName());
                assertEquals("y", actualVariable.getSingleLineDisplayName());
            }
        }
    }
}
