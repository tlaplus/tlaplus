package tlc2.tool.fp;

import java.io.IOException;

public class DiskFPSetLongTest extends FPSetLongTest {

    /* (non-Javadoc)
     * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(int)
     */
    @Override
    protected FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws IOException {
        final DiskFPSet fpSet = new LSBDiskFPSet(fpSetConfig);
        System.out.println("DiskFPSet approx. consumes MiB: "
                + ((fpSet.getMaxTblCnt() * FPSet.LongSize) >> 20));
        return fpSet;
    }
}
