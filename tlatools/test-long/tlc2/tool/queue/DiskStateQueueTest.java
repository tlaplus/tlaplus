package tlc2.tool.queue;

import java.io.File;

import tlc2.tool.TLCState;

public class DiskStateQueueTest extends StateQueueTest {

	private File file;

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.StateQueueTest#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();

		// create a temp folder in java.io.tmpdir and have it deleted on VM exit
		final String diskdir = System.getProperty("java.io.tmpdir") + File.separator + "MultiDiskStateQueueTest_"
				+ System.currentTimeMillis();
		file = new File(diskdir);
		file.mkdirs();
		file.deleteOnExit();
		
		sQueue = new DiskStateQueue(diskdir);
	}
	
	/* (non-Javadoc)
	 * @see junit.framework.TestCase#tearDown()
	 */
	public void tearDown() {
		// delete all nested files
		final File[] listFiles = file.listFiles();
		for (int i = 0; i < listFiles.length; i++) {
			final File aFile = listFiles[i];
			aFile.delete();
		}
		file.delete();
	}
	
	// add Integer.MAX_VALUE states and check growth of MultiStateQueue. 
	// Reuse the same state to speed up instantiation and space requirements
	public void testGrowBeyondIntMaxValue() {
		final TLCState state = new DummyTLCState();

		final long j = Integer.MAX_VALUE + 1L;
		for (long i = 0; i < j; i++) {
			sQueue.sEnqueue(state);
		}
		assertTrue(sQueue.size() == j);
	}
}
