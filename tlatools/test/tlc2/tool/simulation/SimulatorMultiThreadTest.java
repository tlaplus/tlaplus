package tlc2.tool.simulation;

/**
 * Correctness tests of a multi-threaded Simulator.
 * 
 * This test intends to verify that, from a correctness perspective, running the
 * Simulator with multiple threads is equivalent to running it with a single
 * thread i.e. it should pass all of the same tests.
 */
public class SimulatorMultiThreadTest extends SimulatorTest {

	public int numWorkers() {
		// A somewhat arbitrary value, but 4 threads seems like a reasonable amount of
		// parallelism.
		return 4;
	}

}
