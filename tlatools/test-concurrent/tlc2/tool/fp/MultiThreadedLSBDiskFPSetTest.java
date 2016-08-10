// Copyright (c) 2016 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;

public class MultiThreadedLSBDiskFPSetTest extends MultiThreadedFPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(long)
	 */
	@Override
	protected FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws IOException {
		fpSetConfig.setRatio(1.0d); // Tests can consume all of the available VM memory
		return new LSBDiskFPSet(fpSetConfig);
	}
}
