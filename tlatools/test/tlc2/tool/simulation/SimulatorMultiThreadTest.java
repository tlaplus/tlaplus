package tlc2.tool.simulation;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;

import org.junit.Test;
import org.junit.Before;
import org.junit.After;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.CommonTestCase;
import tlc2.tool.Simulator;
import tlc2.util.RandomGenerator;
import util.FileUtil;
import util.SimpleFilenameToStream;
import util.ToolIO;

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
