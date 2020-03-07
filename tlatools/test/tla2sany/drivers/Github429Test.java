package tla2sany.drivers;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import tla2sany.modanalyzer.SpecObj;
import tlc2.tool.CommonTestCase;
import util.SimpleFilenameToStream;
import util.ToolIO;

public class Github429Test {

	private SpecObj moduleSpec;

	@Before
	public void setUp() throws Exception {
		// create a model and initialize
		moduleSpec = new SpecObj(CommonTestCase.BASE_PATH + "Github429.tla", new SimpleFilenameToStream());
		SANY.frontEndInitialize(moduleSpec, ToolIO.out);
	}

	@Test
	public void testForFailedParse() {
        try {
			SANY.frontEndParse(moduleSpec, ToolIO.out);
			SANY.frontEndSemanticAnalysis(moduleSpec, ToolIO.out, false);
		} catch (final Exception e) {
			Assert.fail("No exception should occur during parse. Instead encountered [" + e.getClass()
								+ "] with message: " + e.getMessage());
		}
	}
}
