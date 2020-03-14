package tlc2.tool.simulation;

import java.io.File;
import java.io.IOException;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.BenchmarkMode;
import org.openjdk.jmh.annotations.Level;
import org.openjdk.jmh.annotations.Mode;
import org.openjdk.jmh.annotations.Param;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;

import tla2sany.modanalyzer.SpecObj;
import tlc2.tool.Simulator;
import tlc2.util.RandomGenerator;
import util.SimpleFilenameToStream;
import util.ToolIO;

/**
 * A benchmark to measure multi-threaded simulation performance.
 */
@State(Scope.Benchmark)
public class SimulatorBenchmark {
	
    @Param({ "1", "2", "3", "4", "5", "6"})
    public int nWorkers;
    
	Simulator simulator;
	SpecObj specObj;
	RandomGenerator rng = new RandomGenerator(0);
	long seed = 0;

    @Setup
    public void up() throws IOException {
		ToolIO.setUserDir("test-model" + File.separator + "simulation" + File.separator + "BenchmarkSpec");
    }  
    
    @Setup(Level.Iteration)
    public void reseedIter() {
    	// For each iteration of a benchmark, we set the seed to a known value, so that each 
    	// benchmark fork starts a particular iteration with the same seed. 
		seed += 1;
		rng.setSeed(seed);
    }
    
    @Setup(Level.Trial)
    public void reseed() {
    	// We reset the random number generator to a fixed seed before benchmarking a specific worker count.
    	// This should help to make these benchmarks more deterministic for a fixed set of benchmark parameters. The initial
    	// seed of this random number generator should effectively determine what traces are explored in what order by the simulation
    	// workers, so a particular seed should correspond to a fixed exploration order of the behavior space.
		rng.setSeed(0);
		seed = 0;
    }
    
    public void simulatorBenchmark(int nWorkers) {
		try {
			int maxTraceDepth = 20;
			Simulator simulator = new Simulator("BenchmarkSpec", "MCInv", null, false, maxTraceDepth, Long.MAX_VALUE, rng, 0,
					new SimpleFilenameToStream(), nWorkers);
			simulator.simulate();
		} catch (Exception e) {
			System.out.println(e.getMessage());
		}    
    }
	
	@Benchmark
	@BenchmarkMode(Mode.AverageTime)
	public void SimulatorWorkers() {
		simulatorBenchmark(nWorkers);  
	}
}
