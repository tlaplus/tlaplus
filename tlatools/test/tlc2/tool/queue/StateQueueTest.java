package tlc2.tool.queue;

import tlc2.tool.TLCState;
import junit.framework.TestCase;

public class StateQueueTest extends TestCase {

	protected StateQueue sQueue;

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();
		sQueue = new MemStateQueue("");
	}

	// add and remove a single state
	public void testEnqueue() {
		final TLCState expected = new DummyTLCState();
		sQueue.enqueue(expected);
		TLCState actual = sQueue.sDequeue();
		assertEquals("", expected, actual);
	}

	// dequeue from empty 
	public void testsDequeueEmpty() {
		TLCState state = sQueue.sDequeue();
		assertNull(state);
	}
	
	// dequeue from empty 
	public void testDequeueEmpty() {
		TLCState state = sQueue.dequeue();
		assertNull(state);
	}
	
	// dequeue from not empty 
	public void testsDequeueNotEmpty() {
		DummyTLCState expected = new DummyTLCState();
		sQueue.sEnqueue(expected);
		assertTrue(sQueue.size() == 1);
		TLCState actual = sQueue.sDequeue();
		assertTrue(sQueue.size() == 0);
		assertEquals(expected, actual);
	}
	
	// dequeue from not empty 
	public void testDequeueNotEmpty() {
		DummyTLCState expected = new DummyTLCState();
		sQueue.enqueue(expected);
		assertTrue(sQueue.size() == 1);
		TLCState actual = sQueue.dequeue();
		assertTrue(sQueue.size() == 0);
		assertEquals(expected, actual);
	}

	// add 10 states and check size
	public void testEnqueueAddNotSame() {
		final int j = 10;
		for (int i = 0; i < j; i++) {
			sQueue.sEnqueue(new DummyTLCState());
		}
		assertTrue(sQueue.size() == j);
	}
	
	// add same states 10 times and check size
	public void testEnqueueAddSame() {
		final DummyTLCState state = new DummyTLCState();
		final int j = 10;
		for (int i = 0; i < j; i++) {
			sQueue.sEnqueue(state);
		}
		assertTrue(sQueue.size() == j);
	}

	// uncommon input with empty queue sDequeue
	public void testsDequeueAbuseEmpty() {
		expectRuntimeException(sQueue, 0);
		expectRuntimeException(sQueue, -1);
		expectRuntimeException(sQueue, Integer.MIN_VALUE);
		assertNull(sQueue.sDequeue(Integer.MAX_VALUE));
	}
	
	// uncommon input with non-empty queue
	// unfortunately sDequeue behaves differently depending what's its internal state
	public void testsDequeueAbuseNonEmpty() {
		sQueue.sEnqueue(new DummyTLCState()); // make sure isAvail = true

		expectRuntimeException(sQueue, 0);
		expectRuntimeException(sQueue, -1);
		expectRuntimeException(sQueue, Integer.MIN_VALUE);

		assertTrue(sQueue.sDequeue(Integer.MAX_VALUE).length == 1);
	}
	
	private void expectRuntimeException(StateQueue aQueue, int size)  {
		try {
			aQueue.sDequeue(size);
		} catch(RuntimeException e) {
			return;
		}
		fail("expected to throw RuntimeException with <= input");
	}
}
