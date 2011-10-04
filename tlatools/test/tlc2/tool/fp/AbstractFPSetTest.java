// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.File;
import java.io.IOException;

import junit.framework.TestCase;
import tlc2.TLC;

public abstract class AbstractFPSetTest extends TestCase {

	protected static final String tmpdir = System.getProperty("java.io.tmpdir") + File.separator + "FPSetTest"
					+ System.currentTimeMillis();
	protected static final String filename = "FPSetTestTest";
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
	 * @param freeMemory
	 * @return A new {@link FPSet} instance
	 * @throws IOException
	 */
	protected abstract FPSet getFPSet(int freeMemory) throws IOException;

	/**
	 * Implementation based on {@link TLC#handleParameters(String[])}
	 * @return
	 */
	protected int getFreeMemory() {
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
