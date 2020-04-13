package tlc2.model;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TLAConstants;

/**
 * These are test cases related to the investigation of problems involving parameterized instantiation, undertaken starting
 * 	in April, 2020.
 */
public class ParameterizedInstantiation extends ModelCheckerTestCase {
	private static final String TEST_MODEL_FOLDER_NAME = "ParameterizedInstantiation";
	private static final String SPEC_A_CONFIG = "SPECIFICATION\nSpecA\n";
	private static final String SPEC_B_CONFIG = "SPECIFICATION\nSpecB\n";
	private static final String INIT_NEXT_CONFIG = "INIT\nInit\nNEXT\nNext\n";
	private static final String PARENT_DIR = BASE_PATH + File.separator + TEST_MODEL_FOLDER_NAME;
	private static final File CONFIG_FILE = new File(PARENT_DIR, TLAConstants.Files.MODEL_CHECK_CONFIG_FILE);
	
	
	private int testNumber;
	public ParameterizedInstantiation() {
		super(TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, TEST_MODEL_FOLDER_NAME);
		
		testNumber = 0;
	}

	@Override
	protected void beforeSetUp() {
		try {
			switch(testNumber) {
				case 0:
					writeConfigFile(SPEC_A_CONFIG);
					break;
				case 1:
					writeConfigFile(SPEC_B_CONFIG);
					break;
				case 2:
					writeConfigFile(INIT_NEXT_CONFIG);
					break;
			}

			// we need to wait at least a second or else we risk having TLC fail because the states directory already exists
			Thread.sleep(1100);
			
			testNumber++;
		} catch (final Exception e) {
			fail("Exception caught writing config file: " + e.getMessage());
		}
		
		super.beforeSetUp();
	}

	@Override
	protected void beforeTearDown() {
		CONFIG_FILE.delete();
		
		super.beforeTearDown();
	}
	
	@Test
	public void testSpecA() throws Exception {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
	}
	
	@Test
	public void testSpecB() throws Exception {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
	}
	
	@Test
	public void testInitNext() throws Exception {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
	}
	
	private void writeConfigFile(final String configContent) throws IOException {
		try (final BufferedWriter bw = new BufferedWriter(new FileWriter(CONFIG_FILE))) {
			bw.write(configContent);
		}
	}
}
