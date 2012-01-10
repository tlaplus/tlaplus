package tlc2.tool.fp;

import java.io.IOException;
import java.util.Random;

public abstract class FPSetTest extends AbstractFPSetTest {

	/**
	 * Test filling a {@link FPSet} with max int + 1 random
	 * @throws IOException
	 */
	public void testMaxFPSetSizeRnd() throws IOException {
		Random rnd = new Random(System.currentTimeMillis());
		
		// amount to ~514 (mb) with 4gb system mem
		long freeMemory = getFreeMemoryInBytes();
		final FPSet fpSet = getFPSet(freeMemory);
		fpSet.init(1, tmpdir, filename);
	
		// fill with max int + 1
		final long l = Integer.MAX_VALUE + 2L;
		for (long i = 1; i < l; i++) {
			
			long nextLong = rnd.nextLong();
			assertFalse(fpSet.put(nextLong));
			assertEquals(i, fpSet.size());
		}
	
		// try creating a check point
		fpSet.beginChkpt();
		fpSet.commitChkpt();
		
		//
		assertEquals(l, fpSet.size());
	}

	/**
	 * Test filling a {@link FPSet} with max int + 1 
	 * @throws IOException
	 */
	public void testMaxFPSetSize() throws IOException {
	
		//
		final FPSet fpSet = getFPSet(getFreeMemoryInBytes());
		fpSet.init(1, tmpdir, filename);
	
		long counter = 0;
		// fill with max int + 1
		final long l = Integer.MAX_VALUE + 2L;
		// choose value in the interval [-l/2, l/2] 
		for (long i = (l/2) * -1; i < l; i++) {
			
			long value = -1;
			if (i % 2 != 0) {
				value = l - i;
			} else {
				value = i;
			}
			
			assertFalse(fpSet.put(value));
			assertEquals(++counter, fpSet.size());
		}
	
		// try creating a check point
		fpSet.beginChkpt();
		fpSet.commitChkpt();
		
		//
		assertEquals(l, fpSet.size());
	}
}
