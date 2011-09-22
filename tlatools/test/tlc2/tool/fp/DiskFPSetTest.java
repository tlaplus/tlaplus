package tlc2.tool.fp;

import java.io.File;
import java.io.IOException;

import junit.framework.TestCase;

public class DiskFPSetTest extends TestCase {

	private static final String tmpdir = System.getProperty("java.io.tmpdir") + File.separator + "DiskFPSetTest"
			+ System.currentTimeMillis();
	private static final String filename = "DiskFPSetTest";
	
	private File dir;

	/*
	 * (non-Javadoc)
	 * 
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();

		// create temp folder
		dir = new File(tmpdir);
		dir.mkdirs();
	}
	
	/* (non-Javadoc)
	 * @see junit.framework.TestCase#tearDown()
	 */
	public void tearDown() {
		// delete all nested files
		final File[] listFiles = dir.listFiles();
		for (int i = 0; i < listFiles.length; i++) {
			final File aFile = listFiles[i];
			aFile.delete();
		}
		dir.delete();
	}

	public void testMaxDiskFPSetSize() throws IOException {

		//
		final DiskFPSet diskFPSet = new DiskFPSet(10000000);
		diskFPSet.init(1, tmpdir, filename);

		// fill with max int + 1
		final long l = Integer.MAX_VALUE + 2L;
		for (long i = 0; i < l; i++) {
			diskFPSet.put(i);
			assertEquals((i + 1), diskFPSet.size());
		}

		// try creating a check point
		diskFPSet.beginChkpt();
		diskFPSet.commitChkpt();
		
		//
		assertEquals(l, diskFPSet.size());
	}
}
