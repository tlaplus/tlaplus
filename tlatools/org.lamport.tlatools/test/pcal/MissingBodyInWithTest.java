package pcal;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.tool.CommonTestCase;
import util.ToolIO;

public class MissingBodyInWithTest extends PCalTest {
	
	@Test
	public void test() {
		assertEquals(trans.STATUS_EXIT_WITH_ERRORS,
				trans.runMe(new String[] { "-nocfg", CommonTestCase.BASE_PATH + "MissingBodyInWith.tla" }));
		
		final String[] messages = ToolIO.getAllMessages();
		assertTrue(messages.length == 1);
		
		final String msg = messages[0];
		assertEquals("Unrecoverable error:\n" + 
				" -- Missing body of with statement\n" + 
				"    at line 5, column 5.", msg.trim());
	}
}
