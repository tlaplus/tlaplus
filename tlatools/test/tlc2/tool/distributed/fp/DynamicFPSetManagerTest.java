// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.fp;

import java.io.IOException;
import java.rmi.RemoteException;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import junit.framework.TestCase;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MemFPSet;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

public class DynamicFPSetManagerTest extends TestCase {

	/**
	 * Test that the ctor rejects invalid values.
	 */
	public void testCtorInvalidZero() throws RemoteException {
		try {
			new DynamicFPSetManager(0);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail("Exception expected");
	}
	
	/**
	 * Test that the ctor rejects invalid values.
	 */
	public void testCtorInvalidMin1() throws RemoteException {
		try {
			new DynamicFPSetManager(-1);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail("Exception expected");
	}
	
	/**
	 * Test that the ctor correctly calculates its mask used to index fpset
	 * servers for valid values.
	 */
	public void testCtor1() throws RemoteException {
		DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(1);
		long mask = dynamicFPSetManager.getMask();
		assertEquals(1L, mask);
	}
	
	/**
	 * Test that the ctor correctly calculates its mask used to index fpset
	 * servers for valid values.
	 */
	public void testCtor10() throws RemoteException {
		DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(10);
		long mask = dynamicFPSetManager.getMask();
		assertEquals(15L, mask);
	}
	
	/**
	 * Test that the ctor correctly calculates its mask used to index fpset
	 * servers for valid values.
	 */
	public void testCtor31() throws RemoteException {
		DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(31);
		long mask = dynamicFPSetManager.getMask();
		assertEquals(31L, mask);
	}
	
	/**
	 * Test that the ctor correctly calculates its mask used to index fpset
	 * servers for valid values.
	 */
	public void testCtor32() throws RemoteException {
		DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(32);
		long mask = dynamicFPSetManager.getMask();
		assertEquals(63L, mask);
	}
	
	/**
	 * Test that the ctor correctly calculates its mask used to index fpset
	 * servers for valid values.
	 */
	public void testCtor33() throws RemoteException {
		DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(33);
		long mask = dynamicFPSetManager.getMask();
		assertEquals(63L, mask);
	}

	/**
	 * Test that the ctor correctly calculates its mask used to index fpset
	 * servers for valid values.
	 */
	public void testCtorMax() throws RemoteException {
		DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(Integer.MAX_VALUE);
		long mask = dynamicFPSetManager.getMask();
		assertEquals((Integer.MAX_VALUE), mask);
	}

	/**
	 * Test that the {@link DynamicFPSetManager} correctly indexes into the
	 * table of FPSet servers.
	 */
	public void testGetIndexSingleFPSet() throws RemoteException {
		// Simple case with a single FPSet server
		final Map<Long, Integer> pairs = new HashMap<Long, Integer>();
		pairs.put(Long.MAX_VALUE, 0);
		pairs.put(Long.MIN_VALUE, 0);
		pairs.put(0L, 0);
		pairs.put(1L, 0);
		
		doTestGetIndex(1, pairs);
	}

	/**
	 * Test that the {@link DynamicFPSetManager} correctly indexes into the
	 * table of FPSet servers.
	 */
	public void testGetIndex10FPSet() throws RemoteException {
		final Map<Long, Integer> pairs = new HashMap<Long, Integer>();
		
		pairs.put(Long.MAX_VALUE, 5);
		pairs.put(Long.MIN_VALUE, 0);

		// Test all fpsets get addressed
		pairs.put(0L, 0);
		pairs.put(1L, 1);
		pairs.put(2L, 2);
		pairs.put(3L, 3);
		pairs.put(4L, 4);
		pairs.put(5L, 5);
		pairs.put(6L, 6);
		pairs.put(7L, 7);
		pairs.put(8L, 8);
		pairs.put(9L, 9);

		// Test to correctly wrap over
		pairs.put(10L, 0);
		pairs.put(11L, 1);
		pairs.put(12L, 2);
		
		pairs.put(48L, 0);
		pairs.put(49L, 1);
		pairs.put(50L, 2);
		pairs.put(51L, 3);
		
		doTestGetIndex(10, pairs);
	}
	
	// Create the given amount of FPSetManagers and check if the return the integer for the given fingerprint (long)
	private void doTestGetIndex(final int expectedNumOfServers, final Map<Long, Integer> pairs) throws RemoteException {
		final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers);
		for (int i = 0; i < expectedNumOfServers; i++) {
			dfm.register(new MemFPSet(), "localhost" + i);
		}
		
		for (Entry<Long, Integer> pair : pairs.entrySet()) {
			long fp = pair.getKey();
			int index = dfm.getIndex(fp);
			int expected = pair.getValue();
			assertEquals(expected, index);
		}
	}
	
	/**
	 * Tests that reassign doesn't accept invalid values
	 */
	public void testReassingInvalidMin1() throws RemoteException {
		int expectedNumOfServers = 1;
		final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers);
		for (int i = 0; i < expectedNumOfServers; i++) {
			dfm.register(new MemFPSet(), "localhost" + i);
		}

		// invalid input
		try {
			dfm.reassign(-1);
		} catch (IllegalArgumentException e){
			// expected
			return;
		}
		fail();
	}
	
	/**
	 * Tests that reassign doesn't accept invalid values
	 */
	public void testReassingInvalid2() throws RemoteException {
		int expectedNumOfServers = 1;
		final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers);
		for (int i = 0; i < expectedNumOfServers; i++) {
			dfm.register(new MemFPSet(), "localhost" + i);
		}

		// invalid input
		try {
			dfm.reassign(expectedNumOfServers);
		} catch (IllegalArgumentException e){
			// expected
			return;
		}
		fail();
	}
	
	/**
	 * Tests that reassign correctly terminates with -1 when reassignment to
	 * next FPSet impossible (no FPSets left)
	 */
	public void testReassingTerminate() throws RemoteException {
		int expectedNumOfServers = 1;
		final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers);
		for (int i = 0; i < expectedNumOfServers; i++) {
			dfm.register(new MemFPSet(), "localhost" + i);
		}

		int reassign = dfm.reassign(0);
		assertEquals(-1, reassign);
	}
	
	/**
	 * Tests that reassign correctly assigns to the next FPSet
	 */
	public void testReassing() throws RemoteException {
		int expectedNumOfServers = 10;
		final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers);
		for (int i = 0; i < expectedNumOfServers; i++) {
			dfm.register(new MemFPSet(), "localhost" + i);
		}

		// subsequently replace all FPSets until we 
		// hit the end of the list (-1)
		int reassign = dfm.reassign(1);
		assertEquals(2, reassign);
		
		reassign = dfm.reassign(2);
		assertEquals(3, reassign);

		reassign = dfm.reassign(3);
		assertEquals(4, reassign);
		
		reassign = dfm.reassign(4);
		assertEquals(5, reassign);
		
		reassign = dfm.reassign(5);
		assertEquals(6, reassign);
		
		reassign = dfm.reassign(6);
		assertEquals(7, reassign);
		
		reassign = dfm.reassign(7);
		assertEquals(8, reassign);
		
		reassign = dfm.reassign(8);
		assertEquals(9, reassign);
		
		reassign = dfm.reassign(9);
		assertEquals(0, reassign);
		
		reassign = dfm.reassign(0);
		assertEquals(-1, reassign);
	}
	
	/**
	 * Tests if the {@link FPSetManager} correctly fails over to the replacement {@link FPSet}
	 */
	public void testFailoverPut() throws RemoteException {
		int expectedNumOfServers = 2;
		final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers);
		dfm.register(new FaultyFPSet(), "TestFPSet");
		dfm.register(new MemFPSet(), "RegularFPSet");
		
		final long fp = 2L;
		
		assertEquals("Assert fingerprint corresponds to TestFPSet", 0, dfm.getIndex(fp));
		
		// Test DFM correctly behaves first time when TestFPSet works as expected
		assertFalse(dfm.put(fp));
		assertTrue(dfm.contains(fp));
		
		// Test DFM correctly fails over to successor of TestFPSet
		// (Here one can observe the behavior that a fingerprint is thought to
		// be new when a FPSet crashes).
		assertFalse(dfm.put(fp));
		assertTrue(dfm.contains(fp));
	}

	/**
	 * Tests if the {@link FPSetManager} correctly fails over to the replacement {@link FPSet}
	 */
	public void testFailoverPutBlock() throws RemoteException {
		int expectedNumOfServers = 2;
		final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers);
		dfm.register(new FaultyFPSet(), "TestFPSet");
		dfm.register(new MemFPSet(), "RegularFPSet");
		
		final int numOfServers = dfm.numOfServers();

		// LongVec has to have same size of IFPSetManager#numServers (putBlock
		// method contract)
		final LongVec[] fps = new LongVec[numOfServers]; 
		fps[0] = new LongVec();
		fps[0].addElement(0L);
		assertEquals("Assert fingerprint corresponds to TestFPSet", 0, dfm.getIndex(0L));
		fps[1] = new LongVec();
		fps[1].addElement(1L);
		assertEquals("Assert fingerprint corresponds to TestFPSet", 1, dfm.getIndex(1L));
		
		/* Test DFM correctly behaves first time when TestFPSet works as expected */

		BitVector[] bvs = dfm.putBlock(fps);
		assertEquals(1, bvs[0].trueCnt());
		assertEquals(1, bvs[1].trueCnt());

		bvs = dfm.containsBlock(fps);
		// all (the same) fingerprints are now known (meaning corresponding
		// bit in bvs[x] is zero).
		assertEquals(0, bvs[0].trueCnt());
		assertEquals(0, bvs[1].trueCnt());
		
		/*
		 * Test DFM correctly fails over to successor of TestFPSet (Here one can
		 * observe the behavior that a fingerprint is thought to be new when a
		 * FPSet crashes).
		 */

		bvs = dfm.putBlock(fps);
		assertEquals(1, bvs[0].trueCnt()); // fingerprint is unknown after fpset crash
		assertEquals(0, bvs[1].trueCnt());

		// The previous putBlock call has caused the FPSetManager to detect the
		// failure state of the first FPSets and reassigned the replacement FPSet.
		// Thus, it reports two alive servers
		assertEquals(1, dfm.numOfAliveServers());

		bvs = dfm.containsBlock(fps);
		assertEquals(0, bvs[0].trueCnt()); // fingerprint is known again
		assertEquals(0, bvs[1].trueCnt());
	}

	/**
	 * Tests if the {@link FPSetManager} correctly terminates if all nested FPSets fail
	 */
	public void testFailoverTerminationPutBlock() throws RemoteException {
		int expectedNumOfServers = 2;
		final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers);
		dfm.register(new FaultyFPSet(), "TestFPSet1");
		dfm.register(new FaultyFPSet(), "TestFPSet2");
		
		final int numOfServers = dfm.numOfServers();

		// LongVec has to have same size of IFPSetManager#numServers (putBlock
		// method contract)
		final LongVec[] fps = new LongVec[numOfServers]; 
		fps[0] = new LongVec();
		fps[0].addElement(0L);
		assertEquals("Assert fingerprint corresponds to TestFPSet", 0, dfm.getIndex(0L));
		fps[1] = new LongVec();
		fps[1].addElement(1L);
		assertEquals("Assert fingerprint corresponds to TestFPSet", 1, dfm.getIndex(1L));
		
		/* Test DFM correctly behaves first time when TestFPSet works as expected */

		BitVector[] bvs = dfm.putBlock(fps);
		assertEquals(1, bvs[0].trueCnt());
		assertEquals(1, bvs[1].trueCnt());

		bvs = dfm.containsBlock(fps);
		// all (the same) fingerprints are now known (meaning corresponding
		// bit in bvs[x] is zero).
		assertEquals(0, bvs[0].trueCnt());
		assertEquals(0, bvs[1].trueCnt());
		
		/*
		 * Test DFM correctly fails over to successor of TestFPSet (Here one can
		 * observe the behavior that a fingerprint is thought to be new when a
		 * FPSet crashes).
		 */

		bvs = dfm.putBlock(fps);
		assertEquals(2, bvs[0].trueCnt()); // fingerprint is unknown after fpset crash
		assertEquals(2, bvs[1].trueCnt());
		
		// The previous putBlock call has caused the FPSetManager to detect the
		// failure state of both FPSets
		assertEquals(0, dfm.numOfAliveServers());
		
		bvs = dfm.containsBlock(fps);
		assertEquals(2, bvs[0].trueCnt()); // fingerprint is known again
		assertEquals(2, bvs[1].trueCnt());
	}
	
	/**
	 * Tests if the {@link FPSetManager} correctly terminates if all nested FPSets fail
	 */
	public void testFailoverTerminationPutBlockConcurrent() throws RemoteException {
		int expectedNumOfServers = 2;
		final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers);
		dfm.register(new FaultyFPSet(), "TestFPSet1");
		dfm.register(new FaultyFPSet(), "TestFPSet2");
		
		final int numOfServers = dfm.numOfServers();
		

		// LongVec has to have same size of IFPSetManager#numServers (putBlock
		// method contract)
		final LongVec[] fps = new LongVec[numOfServers]; 
		fps[0] = new LongVec();
		fps[0].addElement(0L);
		assertEquals("Assert fingerprint corresponds to TestFPSet", 0, dfm.getIndex(0L));
		fps[1] = new LongVec();
		fps[1].addElement(1L);
		assertEquals("Assert fingerprint corresponds to TestFPSet", 1, dfm.getIndex(1L));
		
		/* Test DFM correctly behaves first time when TestFPSet works as expected */
		final ExecutorService es = Executors.newCachedThreadPool();
		try {
			BitVector[] bvs = dfm.putBlock(fps, es);
			assertEquals(1, bvs[0].trueCnt());
			assertEquals(1, bvs[1].trueCnt());
			
			bvs = dfm.containsBlock(fps, es);
			// all (the same) fingerprints are now known (meaning corresponding
			// bit in bvs[x] is zero).
			assertEquals(0, bvs[0].trueCnt());
			assertEquals(0, bvs[1].trueCnt());
			
			/*
			 * Test DFM correctly fails over to successor of TestFPSet (Here one can
			 * observe the behavior that a fingerprint is thought to be new when a
			 * FPSet crashes).
			 */
			
			bvs = dfm.putBlock(fps, es);
			assertEquals(2, bvs[0].trueCnt()); // fingerprint is unknown after fpset crash
			assertEquals(2, bvs[1].trueCnt());
			
			// The previous putBlock call has caused the FPSetManager to detect the
			// failure state of both FPSets
			assertEquals(0, dfm.numOfAliveServers());
			
			bvs = dfm.containsBlock(fps, es);
			assertEquals(2, bvs[0].trueCnt()); // fingerprint is known again
			assertEquals(2, bvs[1].trueCnt());
		} finally {
			es.shutdown();
		}
	}
	
	/**
	 * Tests if the {@link FPSetManager} returns the BitVector[] with correct
	 * order.
	 * <p>
	 * Due to the nature of concurrency, this test can pass by chance (inversely
	 * proportional probability to expectedNumOfServers). However, repeatedly
	 * test execution is expected to fail most of the time if
	 * {@link DynamicFPSetManager} is indeed faulty (pay attention to
	 * intermittent test failures).
	 */
	public void testPutBlockConcurrentOrder() throws IOException {
		int expectedNumOfServers = 20;
		final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers);
		
		// expectedNumOfServers - 1 empty fpsets
		for (int i = 0; i < expectedNumOfServers - 1; i++) {
			dfm.register(new MemFPSet(), "TestFPSet" + i);
		}

		final long fp = 1L;
		
		// add a single non-empty fpset at the last position
		FPSet nonEmptyFPSet = new MemFPSet();
		nonEmptyFPSet.put(fp);
		dfm.register(nonEmptyFPSet, "localhost");
		
		
		final LongVec[] fps = new LongVec[expectedNumOfServers]; 
		for (int i = 0; i < expectedNumOfServers; i++) {
			fps[i] = new LongVec();
			fps[i].addElement(fp);
		}
		
		// Check if the last element in the resulting bitvector has the bit for the fp set
		final ExecutorService es = Executors.newCachedThreadPool();
		try {
			final BitVector[] bvs = dfm.containsBlock(fps, es);
			// The first expectedNumOfServers - 1 must not contain the fp
			for (int i = 0; i < expectedNumOfServers - 1; i++) {
				assertEquals(1, bvs[i].trueCnt());
			}

			// The last element is expected to contain the fingerprint
			assertEquals(0, bvs[expectedNumOfServers - 1].trueCnt());
		} finally {
			es.shutdown();
		}
	}
}
