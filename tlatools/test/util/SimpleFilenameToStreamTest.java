package util;

import java.io.File;

import junit.framework.TestCase;

public class SimpleFilenameToStreamTest extends TestCase {

	/**
	 * Try to load a standard module
	 */
	public void testResolveStandardModule() {
		final SimpleFilenameToStream sfts = new SimpleFilenameToStream();
		final File file = sfts.resolve("TLC.tla", true);
		
		assertNotNull(file);
		assertTrue(file.getAbsolutePath() + " does not exist!", file.exists());
		
		final String path = file.getAbsolutePath();
		assertTrue("Test only really makes sense if whitespaces in standardmodules path", path.contains(" "));
	}
}
