package pcal;

import java.util.ArrayList;
import java.io.File;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.tool.CommonTestCase;
import util.ToolIO;

public class ConflictingFairnessOptions extends PCalTest {

	@Test
	public void test() {
		assertEquals(trans.STATUS_EXIT_WITHOUT_ERROR,
				trans.runMe(new String[] {"-nocfg",
					CommonTestCase.BASE_PATH + File.separator + "pcal" + File.separator
					+ "ConflictingFairnessOptions.tla"}));

		final String[] messages = ToolIO.getAllMessages();

		ArrayList<String> warnings = new ArrayList<String>();
		for (int i = 0; i < messages.length; i++) {
			if (messages[i].startsWith(PcalDebug.WARNING)) {
				warnings.add(messages[i]);
			}
		}
		assertEquals(1, warnings.size());

		final String msg = warnings.get(0);
		assertEquals("Warning: Option `nof' specified for --fair algorithm.", msg.trim());
	}
}
