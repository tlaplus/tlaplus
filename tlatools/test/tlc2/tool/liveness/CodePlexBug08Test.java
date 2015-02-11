package tlc2.tool.liveness;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.junit.Assert;

import junit.framework.TestCase;
import tlc2.TLC;
import tlc2.TLCGlobals;
import util.ToolIO;


/**
 * see http://tlaplus.codeplex.com/workitem/8
 */
public class CodePlexBug08Test extends TestCase {

	private static final String TEST_MODEL = "test-model/CodePlexBug08";

	public void testSpec() {
		try {
			// TEST_MODEL is where TLC should look for user defined .tla files
			ToolIO.setUserDir(TEST_MODEL);
			
			// Make output "easily" parsable.
			TLCGlobals.tool = true;

			// Intercept the ModelChecker's stdout and stderr output.
			final ByteArrayOutputStream stream = new ByteArrayOutputStream();
			ToolIO.out = new PrintStream(stream);
			ToolIO.err = ToolIO.out;
			
			final TLC tlc = new TLC();
			// * We want *no* deadlock checking to find the violation of the
			// temporal formula
			// * We use a single worker to simplify debugging by taking out
			// threading
			// * MC is the name of the TLA+ specification to be checked (the file
			// is placed in TEST_MODEL
			final String[] args = { "-deadlock", "-workers", "1", "MC" };
			tlc.handleParameters(args);
			
			// Run the ModelChecker
			tlc.process();
			
			// Retrieve what has been written to stdout/stderror
			ToolIO.out.flush(); // flush just in case
			final String output = stream.toString();
			
			// No output can't mean anything good
			Assert.assertTrue("No TLC output", output.length() > 0);
			
			// Assert that TLC found a temporal violation
			Assert.assertTrue("Failed to find temporal violation", 
					output.contains("@!@!@STARTMSG 2116:1 @!@!@\n" +
									"Temporal properties were violated.\n" + 
									"\n" + "@!@!@ENDMSG 2116 @!@!@\n"));

			// Assert that TLC did not find an invalid counter example. (This
			// check is obviously very brittle. If a single char changes, the invalid
			// counterexample won't be detected.)
			Assert.assertFalse("Found invalid counter example", 
					output.contains("@!@!@STARTMSG 2264:1 @!@!@\n" +
									"The following behavior constitutes a counter-example:\n" +
									"\n" +
									"@!@!@ENDMSG 2264 @!@!@\n" +
									"@!@!@STARTMSG 2217:4 @!@!@\n" +
									"1: <Initial predicate>\n" +
									"/\\ b = FALSE\n" +
									"/\\ x = 3\n" +
									"\n" +
									"@!@!@ENDMSG 2217 @!@!@\n" +
									"@!@!@STARTMSG 2217:4 @!@!@\n" +
									"2: <Action line 11, col 6 to line 13, col 18 of module CodeplexBug8>\n" +
									"/\\ b = TRUE\n" +
									"/\\ x = 4\n" +
									"\n" +
									"@!@!@ENDMSG 2217 @!@!@\n" +
									"@!@!@STARTMSG 2217:4 @!@!@\n" +
									"3: <Action line 6, col 6 to line 9, col 19 of module CodeplexBug8>\n" +
									"/\\ b = FALSE\n" +
									"/\\ x = 4\n" +
									"\n" +
									"@!@!@ENDMSG 2217 @!@!@\n" +
									"@!@!@STARTMSG 2217:4 @!@!@\n" +
									"4: <Action line 11, col 6 to line 13, col 18 of module CodeplexBug8>\n" +
									"/\\ b = TRUE\n" +
									"/\\ x = 5\n" +
									"\n" +
									"@!@!@ENDMSG 2217 @!@!@\n" +
									"@!@!@STARTMSG 2218:4 @!@!@\n" +
									"5: Stuttering\n" +
									"@!@!@ENDMSG 2218 @!@!@"));
			
			System.out.println(output);
		} catch (Exception e) {
			fail();
		}
	}
}
