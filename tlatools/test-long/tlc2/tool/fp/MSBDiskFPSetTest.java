// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;

public class MSBDiskFPSetTest extends FPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(long)
	 */
	@Override
	protected FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws IOException {
		return new MSBDiskFPSet(fpSetConfig);
	}

}
