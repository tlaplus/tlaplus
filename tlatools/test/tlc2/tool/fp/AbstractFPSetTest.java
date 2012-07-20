// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.File;
import java.io.IOException;
import java.text.DecimalFormat;
import java.util.Date;

import junit.framework.TestCase;
import tlc2.TLC;
import util.TLCRuntime;

public abstract class AbstractFPSetTest extends TestCase {

	protected static final String tmpdir = System.getProperty("java.io.tmpdir") + File.separator + "FPSetTest"
					+ System.currentTimeMillis();
	protected static final String filename = "FPSetTestTest";
	protected final DecimalFormat df = new DecimalFormat("###,###.###");

	protected long previousTimestamp;
	protected long previousSize;

	private File dir;
	

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();
	
		// create temp folder
		dir = new File(tmpdir);
		dir.mkdirs();
		
		previousTimestamp = System.currentTimeMillis();
		previousSize = 0L;
		
		System.out.println("Test started at " + new Date());
	}

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#tearDown()
	 */
	public void tearDown() {
		System.out.println("Test finished at " + new Date());
		
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

	protected FPSet getFPSetInitialized() throws IOException {
		long freeMemory = getFreeMemoryInBytes();
		final FPSet fpSet = getFPSet(freeMemory);
		fpSet.init(1, tmpdir, filename);

		if (fpSet instanceof FPSetStatistic) {
			FPSetStatistic fpSetStats = (FPSetStatistic) fpSet;
			System.out.println("Maximum FPSet bucket count is: " + df.format(fpSetStats.getMaxTblCnt()));
		}

		System.out.println("Testing " + fpSet.getClass().getCanonicalName());
		return fpSet;
	}

	/**
	 * Implementation based on {@link TLC#handleParameters(String[])}
	 * @return
	 */
	protected long getFreeMemoryInBytes() {
		// Leave room for system GC to work which approximately requires 20% of
		// memory to do its job.
		return TLCRuntime.getInstance().getFPMemSize(.75d);
	}
	
	// insertion speed
	protected void printInsertionSpeed(final long currentSize) {
		final long currentTimestamp = System.currentTimeMillis();
		// print every minute
		final double factor = (currentTimestamp - previousTimestamp) / 60000d;
		if (factor >= 1d) {
			long insertions = (long) ((currentSize - previousSize) * factor);
			System.out.println(df.format(insertions) + " insertions/min");
			previousTimestamp = currentTimestamp;
			previousSize = currentSize;
		}
	}
}
