package tlc2.model;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.concurrent.atomic.AtomicInteger;

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
	private static final String SPEC_C_CONFIG = "SPECIFICATION\nSpecC\n";
	private static final String INIT_NEXT_CONFIG = "INIT\nInit\nNEXT\nNext\n";
	private static final String PARENT_DIR = BASE_PATH + File.separator + TEST_MODEL_FOLDER_NAME;
	private static final File CONFIG_FILE = new File(PARENT_DIR, TLAConstants.Files.MODEL_CHECK_CONFIG_FILE);
	private static final AtomicInteger TEST_NUMBER = new AtomicInteger(0);
	
	
	public ParameterizedInstantiation() {
		super(TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, TEST_MODEL_FOLDER_NAME);
	}

	@Override
	protected void beforeSetUp() {
		synchronized (TEST_NUMBER) {
			try {
				switch (TEST_NUMBER.getAndIncrement()) {
					case 0:
						writeConfigFile(SPEC_A_CONFIG);
						break;
					case 1:
						writeConfigFile(SPEC_B_CONFIG);
						break;
					case 2:
						writeConfigFile(SPEC_C_CONFIG);
						break;
					case 3:
						writeConfigFile(INIT_NEXT_CONFIG);
						break;
				}
			} catch (final Exception e) {
				fail("Exception caught writing config file: " + e.getMessage());
			}
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
	public void testSpecC() throws Exception {
		assertTrue(recorder.recorded(EC.TLC_CONFIG_SPEC_IS_TRIVIAL));
		setExitStatus(151);
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
