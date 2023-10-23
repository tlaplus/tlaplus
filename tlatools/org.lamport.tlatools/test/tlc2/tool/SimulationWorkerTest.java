package tlc2.tool;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.tool.queue.DummyTLCState;

public class SimulationWorkerTest {

	@Test
	public void testGetTraceTLCState0() {
		SimulationWorker sw = new SimulationWorker(0, null, null, 0, 0, 0, null, false, null, null, null, null, null);

		final StateVec trace = sw.getTrace(null);
		assertEquals(0, trace.size());
	}

	@Test
	public void testGetTraceTLCState1() {
		SimulationWorker sw = new SimulationWorker(0, null, null, 0, 0, 0, null, false, null, null, null, null, null);

		TLCState a = new EqualityDummyTLCState(0, 0);

		final StateVec trace = sw.getTrace(a);
		assertEquals(1, trace.size());

		assertTrue(trace.elementAt(0).isInitial());
		assertNull(trace.elementAt(0).getPredecessor());
		assertEquals(0, trace.elementAt(0).fingerPrint());
	}

	@Test
	public void testGetTraceTLCState2() {
		SimulationWorker sw = new SimulationWorker(0, null, null, 0, 0, 0, null, false, null, null, null, null, null);

		TLCState a = new EqualityDummyTLCState(0, 0);
		TLCState b = new EqualityDummyTLCState(0, 0, a);

		final StateVec trace = sw.getTrace(b);
		assertEquals(1, trace.size());

		assertTrue(trace.elementAt(0).isInitial());
		assertNull(trace.elementAt(0).getPredecessor());
		assertEquals(0, trace.elementAt(0).fingerPrint());
	}

	@Test
	public void testGetTraceTLCState3() {
		SimulationWorker sw = new SimulationWorker(0, null, null, 0, 0, 0, null, false, null, null, null, null, null);

		TLCState a = new EqualityDummyTLCState(0, 0);
		TLCState b = new EqualityDummyTLCState(0, 0, a);
		TLCState c = new EqualityDummyTLCState(0, 0, b);

		final StateVec trace = sw.getTrace(c);
		assertEquals(1, trace.size());

		assertTrue(trace.elementAt(0).isInitial());
		assertNull(trace.elementAt(0).getPredecessor());
		assertEquals(0, trace.elementAt(0).fingerPrint());
	}

	@Test
	public void testGetTraceTLCState4() {
		SimulationWorker sw = new SimulationWorker(0, null, null, 0, 0, 0, null, false, null, null, null, null, null);

		TLCState a = new EqualityDummyTLCState(0, 0);
		TLCState b = new EqualityDummyTLCState(0, 0, a);
		TLCState c = new EqualityDummyTLCState(0, 0, b);
		TLCState d = new EqualityDummyTLCState(1, 1, c);

		final StateVec trace = sw.getTrace(d);
		assertEquals(2, trace.size());

		assertTrue(trace.elementAt(0).isInitial());
		assertEquals(0, trace.elementAt(0).fingerPrint());
		assertNull(trace.elementAt(0).getPredecessor());
		assertFalse(trace.elementAt(1).isInitial());
		assertEquals(1, trace.elementAt(1).fingerPrint());
		assertSame(a, trace.elementAt(1).getPredecessor());
	}

	@Test
	public void testGetTraceTLCState5() {
		SimulationWorker sw = new SimulationWorker(0, null, null, 0, 0, 0, null, false, null, null, null, null, null);

		TLCState a = new EqualityDummyTLCState(0, 0);
		TLCState b = new EqualityDummyTLCState(0, 0, a);
		TLCState c = new EqualityDummyTLCState(0, 0, b);
		TLCState d = new EqualityDummyTLCState(1, 1, c);
		TLCState e = new EqualityDummyTLCState(2, 2, d);

		final StateVec trace = sw.getTrace(e);
		assertEquals(3, trace.size());

		assertTrue(trace.elementAt(0).isInitial());
		assertEquals(0, trace.elementAt(0).fingerPrint());
		assertNull(trace.elementAt(0).getPredecessor());
		assertFalse(trace.elementAt(1).isInitial());
		assertEquals(1, trace.elementAt(1).fingerPrint());
		assertSame(a, trace.elementAt(1).getPredecessor());
		assertFalse(trace.elementAt(2).isInitial());
		assertEquals(2, trace.elementAt(2).fingerPrint());
		assertSame(d, trace.elementAt(2).getPredecessor());
	}

	@Test
	public void testGetTraceTLCState6() {
		SimulationWorker sw = new SimulationWorker(0, null, null, 0, 0, 0, null, false, null, null, null, null, null);

		TLCState a = new EqualityDummyTLCState(0, 0);
		TLCState b = new EqualityDummyTLCState(0, 0, a);
		TLCState c = new EqualityDummyTLCState(0, 0, b);
		TLCState d = new EqualityDummyTLCState(1, 1, c);
		TLCState e = new EqualityDummyTLCState(1, 1, d);

		final StateVec trace = sw.getTrace(e);
		assertEquals(2, trace.size());
		assertTrue(trace.elementAt(0).isInitial());
		assertNull(trace.elementAt(0).getPredecessor());
		assertEquals(0, trace.elementAt(0).fingerPrint());
		assertFalse(trace.elementAt(1).isInitial());
		assertEquals(1, trace.elementAt(1).fingerPrint());
		assertSame(a, trace.elementAt(1).getPredecessor());
	}

	@SuppressWarnings("serial")
	private static class EqualityDummyTLCState extends DummyTLCState {

		private final int id;
		private TLCState predecessor;

		public EqualityDummyTLCState(final int fp, final int id) {
			super(fp);
			this.id = id;
			this.predecessor = null;
		}

		public EqualityDummyTLCState(final int fp, final int id, final TLCState predecessor) {
			super(fp);
			this.id = id;
			this.predecessor = predecessor;
			setPredecessor(predecessor);
		}

		public TLCState getPredecessor() {
			return predecessor;
		}

		public TLCState setPredecessor(final TLCState predecessor) {
			this.predecessor = predecessor;
			return super.setPredecessor(predecessor);
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see java.lang.Object#hashCode()
		 */
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + id;
			result = (int) (prime * result + fingerPrint());
			return result;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see java.lang.Object#equals(java.lang.Object)
		 */
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			EqualityDummyTLCState other = (EqualityDummyTLCState) obj;
			if (fingerPrint() != other.fingerPrint())
				return false;
			if (id != other.id)
				return false;
			return true;
		}
	}
}
