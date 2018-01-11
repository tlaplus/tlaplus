package pcal;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.tool.CommonTestCase;
import util.ToolIO;

public class MissingBodyInWithTest {
	
	@Test
	public void test() {
		// Make tool capture the output written to ToolIO.out. Otherwise,
		// ToolIO#getAllMessages returns an empty array.
		ToolIO.setMode(ToolIO.TOOL);

		assertNull(trans.runMe(new String[] {"-nocfg", CommonTestCase.BASE_PATH + "MissingBodyInWith.tla"}));
		
		final String[] messages = ToolIO.getAllMessages();
		assertTrue(messages.length == 1);
		
		final String msg = messages[0];
		assertEquals("Unrecoverable error:\n" + 
				" -- Missing body of with statement\n" + 
				"    at line 5, column 5.", msg.trim());
	}
}
