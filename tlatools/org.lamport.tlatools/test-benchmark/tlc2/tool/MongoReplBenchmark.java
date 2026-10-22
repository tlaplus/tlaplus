/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.Level;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;
import org.openjdk.jmh.infra.ThreadParams;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import tlc2.tool.impl.FastTool;
import tlc2.util.FP64;
import util.SimpleFilenameToStream;
import util.ToolIO;

/**
 * Measures what a worker does for a state of MongoRepl
 * (general/performance/MongoRepl), the only spec of the performance runs that
 * checks with SYMMETRY: evaluate the next-state relation, and for each
 * successor check the constraint, fingerprint it under symmetry, and check the
 * invariant NeverRollbackCommitted. Unlike a run of TLC, this leaves out the
 * fingerprint set and the state queue, whose cost does not depend on how TLC
 * evaluates and normalizes values.
 * <p>
 * All threads share one tool, as workers do. Run from
 * tlatools/org.lamport.tlatools with, e.g.:
 * 
 * <pre>
 * ant -f customBuild.xml compile compile-test benchmark
 * java -cp "target/benchmarks.jar:lib/*:lib/gson/*:lib/javax.mail/*" org.openjdk.jmh.Main MongoReplBenchmark -t 2
 * </pre>
 * 
 * benchmarks.jar lacks the libraries that FastTool loads, hence lib on the
 * classpath. Add -jvm /path/to/java to run the benchmark on another JDK than
 * the one that runs JMH.
 */
@State(Scope.Benchmark)
public class MongoReplBenchmark {

	static {
		FP64.Init();
	}

	/** The directory of MongoReplBenchmark.tla. */
	private static final String SPEC_DIR = System.getProperty(MongoReplBenchmark.class.getName() + ".spec",
			"test-model" + File.separator + "MongoReplBenchmark");

	/** The directory of RaftMongo.tla, which MongoReplBenchmark.tla extends. */
	private static final String LIB_DIR = System.getProperty(MongoReplBenchmark.class.getName() + ".lib",
			".." + File.separator + ".." + File.separator + "general" + File.separator + "performance"
					+ File.separator + "MongoRepl");

	/** The number of states that the benchmarks take turns on. */
	private static final int STATES = 4096;

	/**
	 * The length of a random walk. The performance runs get to a depth of about
	 * 30 in 10 minutes, so the states spread over the depths that TLC explores.
	 */
	private static final int DEPTH = 30;

	private ITool tool;

	private TLCState[] states;

	/**
	 * Collects the states of random walks from the initial states. The walks are
	 * seeded, so all runs measure the same states.
	 */
	@Setup(Level.Trial)
	public void setup() {
		ToolIO.setUserDir(SPEC_DIR);
		tool = new FastTool("", "MongoReplBenchmark", "MongoReplBenchmark", new SimpleFilenameToStream(LIB_DIR));

		final Random rnd = new Random(15041980L);
		final StateVec inits = tool.getInitStates();
		final List<TLCState> res = new ArrayList<>(STATES);
		while (res.size() < STATES) {
			TLCState s = inits.elementAt(rnd.nextInt(inits.size()));
			s.fingerPrint(tool);
			for (int d = 0; d < DEPTH && res.size() < STATES; d++) {
				final Successors succs = new Successors(tool);
				tool.getNextStates(succs, s);
				if (succs.states.isEmpty()) {
					break;
				}
				s = succs.states.get(rnd.nextInt(succs.states.size()));
				// TLC fingerprints a state before it enqueues it.
				s.fingerPrint(tool);
				res.add(s);
			}
		}
		states = res.toArray(TLCState[]::new);
	}

	/** The state that a thread takes next. */
	@State(Scope.Thread)
	public static class Cursor {
		private int i;

		/** Threads start at different states, as workers do. */
		@Setup(Level.Trial)
		public void setup(final ThreadParams params) {
			i = params.getThreadIndex() * (STATES / Math.max(1, params.getThreadCount()));
		}

		TLCState next(final TLCState[] states) {
			i = (i + 1) % states.length;
			return states[i];
		}
	}

	/** What a worker does for a state, up to the fingerprint set. */
	@Benchmark
	public long step(final Cursor c) {
		final Step step = new Step(tool);
		tool.getNextStates(step, c.next(states));
		return step.fps;
	}

	/** Only the evaluation of the next-state relation. */
	@Benchmark
	public long nextStates(final Cursor c) {
		final Count count = new Count();
		tool.getNextStates(count, c.next(states));
		return count.n;
	}

	/** Only the check of the invariant NeverRollbackCommitted. */
	@Benchmark
	public boolean invariant(final Cursor c) {
		return tool.isValid(tool.getInvariants()[0], c.next(states));
	}

	/**
	 * Mirrors Worker#addElement. Every successor counts as new, so its invariant
	 * is checked; TLC checks it only for the new ones.
	 */
	private static final class Step implements INextStateFunctor {
		private final ITool tool;
		private long fps;

		Step(final ITool tool) {
			this.tool = tool;
		}

		@Override
		public Object addElement(final TLCState s, final Action a, final TLCState t) {
			if (!tool.isGoodState(t)) {
				throw new IllegalStateException("Successor state is not completely specified.");
			}
			if (tool.isInModel(t.setPredecessor(s).setAction(a)) && tool.isInActions(s, t)) {
				fps += t.fingerPrint(tool);
				for (final Action inv : tool.getInvariants()) {
					if (!tool.isValid(inv, t)) {
						throw new IllegalStateException("Invariant violated.");
					}
				}
			}
			return this;
		}
	}

	private static final class Count implements INextStateFunctor {
		private long n;

		@Override
		public Object addElement(final TLCState s, final Action a, final TLCState t) {
			n++;
			return this;
		}
	}

	/** Collects the successors that satisfy the constraint. */
	private static final class Successors implements INextStateFunctor {
		private final ITool tool;
		private final List<TLCState> states = new ArrayList<>();

		Successors(final ITool tool) {
			this.tool = tool;
		}

		@Override
		public Object addElement(final TLCState s, final Action a, final TLCState t) {
			if (tool.isInModel(t.setPredecessor(s).setAction(a)) && tool.isInActions(s, t)) {
				states.add(t);
			}
			return this;
		}
	}

	public static void main(String[] args) throws RunnerException {
		final Options opt = new OptionsBuilder().include(MongoReplBenchmark.class.getSimpleName()).build();
		new Runner(opt).run();
	}
}
