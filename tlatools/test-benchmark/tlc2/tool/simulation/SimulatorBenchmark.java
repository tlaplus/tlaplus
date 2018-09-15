package tlc2.tool.simulation;

import java.io.File;
import java.io.IOException;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.BenchmarkMode;
import org.openjdk.jmh.annotations.Mode;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;

import tlc2.tool.Simulator;
import tlc2.util.RandomGenerator;
import util.SimpleFilenameToStream;
import util.ToolIO;

/**
 * A benchmark to measure multi-threaded simulation performance.
 */
@State(Scope.Benchmark)
public class SimulatorBenchmark {

    @Setup
    public void up() throws IOException {
		ToolIO.setUserDir("test-model" + File.separator + "simulation" + File.separator + "BenchmarkSpec");
    }    
    
    public void simulatorBenchmark(int nWorkers) {
		try {
			RandomGenerator rng = new RandomGenerator(System.nanoTime());
			Simulator simulator = new Simulator("BenchmarkSpec", "MCInv", null, false, 35, Long.MAX_VALUE, rng, 0, true, new SimpleFilenameToStream(), null, nWorkers);
			simulator.simulate();
		} catch (Exception e) {
			System.out.println(e.getMessage());
		}    
    }
	
	@Benchmark
	@BenchmarkMode(Mode.AverageTime)
	public void Simulator1Workers() {
		simulatorBenchmark(1);  
	}

	@Benchmark
	@BenchmarkMode(Mode.AverageTime)
	public void Simulator2Workers() {
		simulatorBenchmark(2);
	}
	
	@Benchmark
	@BenchmarkMode(Mode.AverageTime)
	public void Simulator4Workers() {
		simulatorBenchmark(4);
	}
	
	@Benchmark
	@BenchmarkMode(Mode.AverageTime)
	public void Simulator8Workers() {
		simulatorBenchmark(8);
	}
	
	@Benchmark
	@BenchmarkMode(Mode.AverageTime)
	public void Simulator12Workers() {
		simulatorBenchmark(12);
	}
}
