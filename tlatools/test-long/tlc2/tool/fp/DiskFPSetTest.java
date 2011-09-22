package tlc2.tool.fp;

import java.io.File;
import java.io.IOException;

import tlc2.TLC;

import junit.framework.TestCase;

public class DiskFPSetTest extends TestCase {

	private static final String tmpdir = System.getProperty("java.io.tmpdir") + File.separator + "DiskFPSetTest"
			+ System.currentTimeMillis();
	private static final String filename = "DiskFPSetTest";
	
	private File dir;

	/* (non-Javadoc)
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

	/**
	 * Test filling a DiskFPSet with max int + 1 
	 * @throws IOException
	 */
	public void testMaxDiskFPSetSize() throws IOException {

		//
		final DiskFPSet diskFPSet = new DiskFPSet(getFreeMemory());
		diskFPSet.init(1, tmpdir, filename);

		// fill with max int + 1
		final long l = Integer.MAX_VALUE + 2L;
		for (long i = 1; i < l; i++) {
			if (i % 2 != 0) {
				assertFalse(diskFPSet.put(l - i));
			} else {
				assertFalse(diskFPSet.put(i));
			}
			
			assertEquals(i, diskFPSet.size());
		}

		// try creating a check point
		diskFPSet.beginChkpt();
		diskFPSet.commitChkpt();
		
		//
		assertEquals(l, diskFPSet.size());
	}
	
	/**
	 * Implementation based on {@link TLC#handleParameters(String[])}
	 * @return
	 */
	private int getFreeMemory() {
		final Runtime runtime = Runtime.getRuntime();
		final long MinFpMemSize = 20 * (1 << 19);
		
		long fpMemSize = 0;

		if (fpMemSize == -1) {
			fpMemSize = runtime.maxMemory() >> 2;
		}
		if (fpMemSize < MinFpMemSize) {
			fpMemSize = MinFpMemSize;
		}
		if (fpMemSize >= runtime.maxMemory()) {
			fpMemSize = runtime.maxMemory() - (runtime.maxMemory() >> 2);
		}

		return (int) fpMemSize / 20;
	}
}
