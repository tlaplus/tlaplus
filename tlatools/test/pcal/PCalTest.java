package pcal;

import org.junit.Before;

import util.ToolIO;

public abstract class PCalTest {
	
	@Before
	public void setup() {
		// Make tool capture the output written to ToolIO.out. Otherwise,
		// ToolIO#getAllMessages returns an empty array.
		ToolIO.setMode(ToolIO.TOOL);
		
		// Reset ToolIO for each test case. Otherwise, a test case sees the output of
		// the previous tests.
		ToolIO.reset();
	}
}
