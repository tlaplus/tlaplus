// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;
import java.lang.reflect.InvocationTargetException;

import org.junit.Assert;

import tlc2.tool.fp.generator.PartitionedFingerPrintGenerator;

public class MultiThreadedOffHeapDiskFPSetTest extends MultiThreadedFPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(long)
	 */
	@Override
	protected FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws IOException {
		return new OffHeapDiskFPSet(new FPSetConfiguration(1.0d, OffHeapDiskFPSet.class.getName()));
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.MultiThreadedFPSetTest#testMaxFPSetSizePartitioned()
	 */
	@Override
	public void testMaxFPSetSizePartitioned()
			throws IOException, InterruptedException, NoSuchMethodException, SecurityException, InstantiationException,
			IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		final OffHeapDiskFPSet fpSet = (OffHeapDiskFPSet) doTest(PartitionedFingerPrintGenerator.class);
		Assert.assertEquals(0, fpSet.getBucketCapacity()); // bucket capacity is actually reprobe which expected to be zero.
	}
}
