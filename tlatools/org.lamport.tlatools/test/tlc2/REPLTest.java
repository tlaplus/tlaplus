package tlc2;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

// useful for debugging purposes or more complicated test scenarios
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.Value;

public class REPLTest {

    @Test
    public void testProcessInput() throws IOException {
        Path tempDir = Files.createTempDirectory("repltest");
        final REPL repl = new REPL(tempDir);
        String res;

        // Numeric expressions.
        res = repl.processInput("2+2");
        assertEquals("4", res);

        Value val = repl.processInputToValue("2+2");
        assertEquals("4", val.toString());
        assert(val instanceof IntValue);

        res = repl.processInput("4-2");
        assertEquals("2", res);
        res = repl.processInput("10 \\div 2");
        assertEquals("5", res);

        // Set expressions.
        val = repl.processInputToValue("1 \\in {1,2,3,4}");
        assertEquals("TRUE", val.toString());
        assert(val instanceof BoolValue);

        Value valNum = repl.processInputToValue("1");
        Value valSet = repl.processInputToValue("{2,3,4}");
        assert(valNum instanceof IntValue);
        assert(valSet instanceof SetEnumValue);
        assert(!((SetEnumValue)valSet).member(valNum));

        res = repl.processInput("{1,2} \\X {3,4}");
        assertEquals("{<<1, 3>>, <<1, 4>>, <<2, 3>>, <<2, 4>>}", res);
        res = repl.processInput("{1,2} \\cup {3,4}");
        assertEquals("{1, 2, 3, 4}", res);
        res = repl.processInput("{1,2} \\cap {2,3}");
        assertEquals("{2}", res);

        // Tuple expressions.
        res = repl.processInput("Append(<<1,2>>, 3)");
        assertEquals("<<1, 2, 3>>", res);
        res = repl.processInput("Append(3, <<1,2>>)"); // error.
        assertEquals("", res);
        res = repl.processInput("Tail(<<1,2,3>>)");
        assertEquals("<<2, 3>>", res);
        res = repl.processInput("Head(<<1,2,3>>)");
        assertEquals("1", res);
        res = repl.processInput("<<1,2>> \\o <<3>>");
        assertEquals("<<1, 2, 3>>", res);

        // Other invalid expressions.
        res = repl.processInput("invalid");
        assertEquals("", res);
        res = repl.processInput("123abc");
        assertEquals("", res);
    }

    @Test(expected = tlc2.tool.EvalException.class)
    public void testEvalExceptionThrow() throws IOException {
        Path tempDir = Files.createTempDirectory("repltest2");
        final REPL repl = new REPL(tempDir);

        Value val = repl.processInputToValue("Append(3, <<1,2>>)"); // error.
        assertEquals("", val.toString());
    }

}
