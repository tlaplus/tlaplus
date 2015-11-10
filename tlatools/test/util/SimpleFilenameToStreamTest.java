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
}
