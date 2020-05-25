package tlc2;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

public class REPLTest {

    @Test
    public void testProcessInput() throws IOException {
        Path tempDir = Files.createTempDirectory("repltest");
        final REPL repl = new REPL(tempDir);
        String res;

        // Numeric expressions.
        res = repl.processInput("2+2");
        assertEquals("4", res);
        res = repl.processInput("4-2");
        assertEquals("2", res);
        res = repl.processInput("10 \\div 2");
        assertEquals("5", res);

        // Set expressions.
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

}
