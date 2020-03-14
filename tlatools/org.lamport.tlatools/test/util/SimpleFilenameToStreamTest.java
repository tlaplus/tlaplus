package util;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

public class SimpleFilenameToStreamTest {

	/**
	 * Try to load a standard module
	 */
	@Test
	public void testResolveStandardModule() {
		final SimpleFilenameToStream sfts = new SimpleFilenameToStream();
		final File file = sfts.resolve("TLC.tla", true);
		
		assertNotNull(file);
		assertTrue(file.getAbsolutePath() + " does not exist!", file.exists());
	}
	
	/**
	 * Test whether the fix for #424 still works
	 */
	@Test
	public void testWindowsTLAFileCreation() {
		if (System.getProperty("os.name").toLowerCase().indexOf("win") > -1) {
			final String driveLetter = "X:";
			final String parentDirectory = driveLetter + "\\Develop\\myspecs\\DecentSpec\\";
			final String child = parentDirectory + "Fromage.tla";
			final FilenameToStream.TLAFile file = new FilenameToStream.TLAFile(parentDirectory, child, null);
			final int driveLetterCount = file.getAbsolutePath().split(driveLetter).length - 1;
			
			assertTrue("There should be 1 drive letter in the child's absolute path, but there are " + driveLetterCount,
					   (1 == driveLetterCount));
		}
	}
	
}
