package pcal;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.tool.CommonTestCase;
import util.ToolIO;

public class MissingBodyInWhileTest extends PCalTest {
	
	@Test
	public void test() {
		assertEquals(trans.STATUS_EXIT_WITH_ERRORS,
				trans.runMe(new String[] {"-nocfg", CommonTestCase.BASE_PATH + "MissingBodyInWhile.tla"}));
		
		final String[] messages = ToolIO.getAllMessages();
		assertTrue(messages.length == 1);
		
		final String msg = messages[0];
		assertEquals("Unrecoverable error:\n" + 
				" -- Missing body of while statement at\n" + 
				"    line 6, column 14.", msg.trim());
	}
}
