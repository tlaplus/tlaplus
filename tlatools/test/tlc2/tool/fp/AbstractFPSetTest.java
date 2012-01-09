// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.File;
import java.io.IOException;

import junit.framework.TestCase;
import tlc2.TLC;
import util.TLCRuntime;

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
	protected abstract FPSet getFPSet(long freeMemoryInBytes) throws IOException;

	/**
	 * Implementation based on {@link TLC#handleParameters(String[])}
	 * @return
	 */
	protected long getFreeMemoryInBytes() {
		return TLCRuntime.getInstance().getFPMemSize(.9d);
	}
}
