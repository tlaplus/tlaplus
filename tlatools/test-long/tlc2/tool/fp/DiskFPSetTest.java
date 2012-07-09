package tlc2.tool.fp;

import java.io.IOException;

public class DiskFPSetTest extends FPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(int)
	 */
	@Override
	protected FPSet getFPSet(long freeMemory) throws IOException {
		final DiskFPSet fpSet = new DiskFPSet(freeMemory / (long) DiskFPSet.LongSize);
		System.out.println("DiskFPSet approx. consumes MiB: "
				+ ((fpSet.getMaxTblCnt() * (long) DiskFPSet.LongSize) >> 20));
        return fpSet;
	}
}
