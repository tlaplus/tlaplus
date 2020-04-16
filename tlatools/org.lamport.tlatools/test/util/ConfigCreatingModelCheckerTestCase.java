package util;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * This class provides a setup and tear-down affectation of the MC config file whose contents are described
 * 	on class construction.
 * 
 * TODO ModelCheckerTestCase and its super class should be moved into this package (util) as well.
 */
public abstract class ConfigCreatingModelCheckerTestCase extends ModelCheckerTestCase {
	private final String mcConfigContent;
	private final File mcConfigFile;
	
	public ConfigCreatingModelCheckerTestCase(final String testFileFolderName, final String configText) {
		super(TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, testFileFolderName);
		mcConfigContent = configText;
		
		final String parentDir = BASE_PATH + File.separator + testFileFolderName;
		mcConfigFile= new File(parentDir, TLAConstants.Files.MODEL_CHECK_CONFIG_FILE);
	}

	@Override
	protected void beforeSetUp() {
		try {
			writeConfigFile();
		} catch (final Exception e) {
			fail("Exception caught writing config file: " + e.getMessage());
		}
		
		super.beforeSetUp();
	}

	@Override
	protected void beforeTearDown() {
		if (!mcConfigFile.delete()) {
			mcConfigFile.deleteOnExit();
		}

		super.beforeTearDown();
	}
	
	private void writeConfigFile() throws IOException {
		try (final BufferedWriter bw = new BufferedWriter(new FileWriter(mcConfigFile))) {
			bw.write(mcConfigContent);
		}
	}
}
