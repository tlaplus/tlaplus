package tlc2.tool.distributed;

import org.junit.Test;
import tlc2.tool.TLCState;
import tlc2.tool.distributed.selector.DummyTLCWorker;
import tlc2.tool.queue.DummyTLCState;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class TLCWorkerSmartProxyTest {

    private static final int ZERO = 0;
    private static final int ONE = 1;
    private static final int MAX_ARRAY_SIZE = 0;

    @Test
    public void testGetNetworkOverheadMaxStateOne() throws Exception {
        final long calculationDuration = Long.MAX_VALUE;
        assertTrue(doTest(calculationDuration, new DummyTLCState[ONE]) > 0);
    }

    @Test
    public void testGetNetworkOverheadMinStateOne() throws Exception {
        final long calculationDuration = Long.MIN_VALUE;
        assertTrue(doTest(calculationDuration, new DummyTLCState[ONE]) > 0);
    }

    @Test
    public void testGetNetworkOverheadZeroStateOne() throws Exception {
        final long calculationDuration = ZERO;
        assertTrue(doTest(calculationDuration, new DummyTLCState[ONE]) > 0);
    }

    @Test
    public void testGetNetworkOverheadMaxStateZero() throws Exception {
        final long calculationDuration = Long.MAX_VALUE;
        assertTrue(doTest(calculationDuration, new DummyTLCState[ZERO]) > 0);
    }

    @Test
    public void testGetNetworkOverheadMinStateZero() throws Exception {
        final long calculationDuration = Long.MIN_VALUE;
        assertTrue(doTest(calculationDuration, new DummyTLCState[ZERO]) > 0);
    }

    @Test
    public void testGetNetworkOverheadZeroStateZero() throws Exception {
        final long calculationDuration = ZERO;
        assertTrue(doTest(calculationDuration, new DummyTLCState[ZERO]) > 0);
    }

    @Test
    public void testGetNetworkOverheadMinStateMax() throws Exception {
        final long calculationDuration = Long.MIN_VALUE;
        assertTrue(doTest(calculationDuration, new DummyTLCState[MAX_ARRAY_SIZE]) > 0);
    }

    @Test
    public void testGetNetworkOverheadMaxStateMa() throws Exception {
        final long calculationDuration = Long.MAX_VALUE;
        assertTrue(doTest(calculationDuration, new DummyTLCState[MAX_ARRAY_SIZE]) > 0);
    }

    @Test
    public void testGetNetworkOverheadZeroStateMax() throws Exception {
        final long calculationDuration = ZERO;
        assertTrue(doTest(calculationDuration, new DummyTLCState[MAX_ARRAY_SIZE]) > 0);
    }

    private double doTest(final long calculationDuration, final TLCState[] states) throws Exception {
        final DummyTLCWorker aWorker = new DummyTLCWorker(calculationDuration);

        try (final TLCWorkerSmartProxy proxy = new TLCWorkerSmartProxy(aWorker)) {
            // let proxy calculate current network overhead
            final NextStateResult nsr = proxy.getNextStates(states);
            assertNotNull(nsr);

            final double networkOverhead = proxy.getNetworkOverhead();
            return networkOverhead;
        }
    }
}
