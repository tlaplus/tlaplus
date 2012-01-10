package tlc2.tool.fp;

import java.io.IOException;

public class DiskFPSetTest extends FPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(int)
	 */
	@Override
	protected FPSet getFPSet(long freeMemory) throws IOException {
		return new DiskFPSet(freeMemory);
	}
}
