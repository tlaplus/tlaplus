package tlc2.tool.queue;

import org.easymock.EasyMock;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import tla2sany.semantic.OpDeclNode;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;

import static org.junit.Assert.*;

public class StateQueueTest {

    protected IStateQueue sQueue;

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    @Before
    public void setUp() {
        var tool = EasyMock.createNiceMock(ITool.class);
        sQueue = new MemStateQueue("", tool);
    }

    @After
    public void tearDown() throws Exception {
        sQueue.close();
    }

    // add and remove a single state
    @Test
    public void testEnqueue() {
        final TLCState expected = new DummyTLCState(new OpDeclNode[]{});
        sQueue.enqueue(expected);
        final TLCState actual = sQueue.sDequeue();
        assertEquals("", expected, actual);
    }

    // dequeue from empty
    @Test
    public void testsDequeueEmpty() {
        final TLCState state = sQueue.sDequeue();
        assertNull(state);
    }

    // dequeue from empty
    @Test
    public void testDequeueEmpty() {
        final TLCState state = sQueue.dequeue();
        assertNull(state);
    }

    // dequeue from not empty
    @Test
    public void testsDequeueNotEmpty() {
        final DummyTLCState expected = new DummyTLCState(new OpDeclNode[]{});
        sQueue.sEnqueue(expected);
        assertEquals(1, sQueue.size());
        final TLCState actual = sQueue.sDequeue();
        assertEquals(0, sQueue.size());
        assertEquals(expected, actual);
    }

    // dequeue from not empty
    @Test
    public void testDequeueNotEmpty() {
        final DummyTLCState expected = new DummyTLCState(new OpDeclNode[]{});
        sQueue.enqueue(expected);
        assertEquals(1, sQueue.size());
        final TLCState actual = sQueue.dequeue();
        assertEquals(0, sQueue.size());
        assertEquals(expected, actual);
    }

    // add 10 states and check size
    @Test
    public void testEnqueueAddNotSame() {
        final int j = 10;
        for (int i = 0; i < j; i++) {
            sQueue.sEnqueue(new DummyTLCState(new OpDeclNode[]{}));
        }
        assertEquals(j, sQueue.size());
    }

    // add same states 10 times and check size
    @Test
    public void testEnqueueAddSame() {
        final DummyTLCState state = new DummyTLCState(new OpDeclNode[]{});
        final int j = 10;
        for (int i = 0; i < j; i++) {
            sQueue.sEnqueue(state);
        }
        assertEquals(j, sQueue.size());
    }

    // uncommon input with empty queue sDequeue
    @Test
    public void testsDequeueAbuseEmpty() {
        expectRuntimeException(sQueue, 0);
        expectRuntimeException(sQueue, -1);
        expectRuntimeException(sQueue, Integer.MIN_VALUE);
        assertNull(sQueue.sDequeue(Integer.MAX_VALUE));
    }

    // uncommon input with non-empty queue
    // unfortunately sDequeue behaves differently depending what's its internal state
    @Test
    public void testsDequeueAbuseNonEmpty() {
        sQueue.sEnqueue(new DummyTLCState(new OpDeclNode[]{})); // make sure isAvail = true

        expectRuntimeException(sQueue, 0);
        expectRuntimeException(sQueue, -1);
        expectRuntimeException(sQueue, Integer.MIN_VALUE);

        assertEquals(1, sQueue.sDequeue(Integer.MAX_VALUE).length);
    }

    private void expectRuntimeException(final IStateQueue aQueue, final int size) {
        try {
            aQueue.sDequeue(size);
        } catch (final RuntimeException | AssertionError e) {
            return;
        }
        fail("expected to throw RuntimeException with <= input");
    }
}
