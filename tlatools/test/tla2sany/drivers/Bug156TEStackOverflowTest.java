package tla2sany.drivers;

import junit.framework.TestCase;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import util.SimpleFilenameToStream;
import util.ToolIO;

/**
 * @see http://bugzilla.tlaplus.net/show_bug.cgi?id=156
 */
public class Bug156TEStackOverflowTest extends TestCase {

	private SpecObj moduleSpec;

	/**
	 * @throws java.lang.Exception
	 */
	public void setUp() throws Exception {
		// create a model and initialize
		moduleSpec = new SpecObj("test-model/Bug156/TE.tla", new SimpleFilenameToStream());
		SANY.frontEndInitialize(moduleSpec, ToolIO.out);
	}

	/**
	 * Test method for {@link tla2sany.drivers.SANY#frontEndParse(tla2sany.modanalyzer.SpecObj, java.io.PrintStream)}.
	 * @throws ParseException 
	 */
	public void testFrontEndParse() throws ParseException {
		fail("Fix me please!");
//        try {
//			SANY.frontEndParse(moduleSpec, ToolIO.out);
//		} catch (StackOverflowError e) {
//			fail("StackOverflow must not happen");
//		}
	}
}
