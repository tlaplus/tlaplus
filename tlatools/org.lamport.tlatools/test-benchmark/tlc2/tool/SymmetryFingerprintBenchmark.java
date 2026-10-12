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

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.Level;
import org.openjdk.jmh.annotations.Param;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.MVPerms;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueExcept;
import util.UniqueString;

/**
 * Measures how much TLC's lazy normalization saves under symmetry reduction.
 * To fingerprint a state, TLC picks the smallest state in its symmetry class:
 * it permutes the state with every permutation and compares the result with the
 * smallest state so far, variable by variable, up to the first difference. Most
 * of the permuted values therefore never take part in a comparison, and TLC
 * never sorts them. Normalizing eagerly, as soon as a value is created, would
 * sort every one of them.
 * <p>
 * The state is one of PaxosCommit (general/performance/PaxosCommit) with
 * SYMMETRY Permutations(Acceptor) \cup Permutations(RM). Both modes run TLC's
 * own fingerprinting; the eager mode additionally sorts every value that
 * permute creates.
 */
@State(Scope.Benchmark)
public class SymmetryFingerprintBenchmark {

	static {
		FP64.Init();
	}

	/** The values of rmState[rm], aState[rm][ac].val and m.val. */
	private static final String[] VALS = { "prepared", "aborted", "none" };

	/** The field names of the records in aState and msgs. */
	private static final UniqueString TYPE = UniqueString.of("type");
	private static final UniqueString INS = UniqueString.of("ins");
	private static final UniqueString MBAL = UniqueString.of("mbal");
	private static final UniqueString BAL = UniqueString.of("bal");
	private static final UniqueString VAL = UniqueString.of("val");
	private static final UniqueString ACC = UniqueString.of("acc");

	/**
	 * The number of messages in msgs. msgs is the largest variable and the last
	 * one, so a comparison reaches it only if rmState and aState tie. Its size
	 * therefore scales the sorting that only eager normalization does.
	 */
	@Param({ "8", "32", "128" })
	public int msgs;

	/**
	 * lazy: values are sorted when a comparison or fingerprint needs them, as in
	 * TLC. eager: values are sorted as soon as they are created.
	 */
	@Param({ "lazy", "eager" })
	public String normalization;

	/** The state <<rmState, aState, msgs>> that fingerPrint() fingerprints. */
	private TLCState state;
	/** The variable aState of state, which permuteAState() permutes. */
	private Value aState;
	/**
	 * The symmetry group without the identity, because the state itself is the
	 * first candidate for the smallest state.
	 */
	private IMVPerm[] perms;

	/**
	 * Builds a state of PaxosCommit with 2 resource managers and 3 acceptors. The
	 * state is random, so it is not a hand-picked one, and seeded, so all runs
	 * measure the same state.
	 */
	@Setup(Level.Trial)
	public void setup() throws ReflectiveOperationException {
		final Random rnd = new Random(15041980L);

		// CONSTANTS RM and Acceptor, and the group that MVPerms generates from
		// Permutations(Acceptor) \cup Permutations(RM), as for SYMMETRY.
		final Value[] rms = { ModelValue.make("rm1"), ModelValue.make("rm2") };
		final Value[] accs = { ModelValue.make("a1"), ModelValue.make("a2"), ModelValue.make("a3") };
		ModelValue.setValues();

		perms = MVPerms.permutationSubgroup(new SetEnumValue(concat(permutations(accs), permutations(rms)), false));

		// rmState \in [RM -> {"prepared", "aborted"}]
		final Value[] rmState = new Value[rms.length];
		for (int i = 0; i < rms.length; i++) {
			rmState[i] = new StringValue(VALS[rnd.nextInt(2)]);
		}

		// aState \in [RM -> [Acceptor -> [mbal : Ballot, bal : Ballot \cup {-1}, val : ...]]],
		// a function whose range is functions over the symmetry set Acceptor.
		final Value[] aStates = new Value[rms.length];
		for (int i = 0; i < rms.length; i++) {
			final Value[] acc = new Value[accs.length];
			for (int j = 0; j < accs.length; j++) {
				acc[j] = new RecordValue(new UniqueString[] { MBAL, BAL, VAL },
						new Value[] { IntValue.gen(rnd.nextInt(3)), IntValue.gen(rnd.nextInt(4) - 1),
								new StringValue(VALS[rnd.nextInt(3)]) },
						false);
			}
			aStates[i] = new FcnRcdValue(accs.clone(), acc, false);
		}
		aState = new FcnRcdValue(rms.clone(), aStates, false);

		// msgs \subseteq Message, a set of phase1b, phase2a and phase2b messages,
		// i.e. records whose fields ins and acc are elements of the symmetry sets.
		final Value[] messages = new Value[msgs];
		for (int i = 0; i < msgs; i++) {
			final Value rm = rms[rnd.nextInt(rms.length)];
			final Value acc = accs[rnd.nextInt(accs.length)];
			final Value bal = IntValue.gen(rnd.nextInt(3));
			switch (rnd.nextInt(3)) {
			case 0:
				messages[i] = new RecordValue(new UniqueString[] { TYPE, INS, MBAL, BAL, VAL, ACC },
						new Value[] { new StringValue("phase1b"), rm, bal, IntValue.gen(rnd.nextInt(4) - 1),
								new StringValue(VALS[rnd.nextInt(3)]), acc },
						false);
				break;
			case 1:
				messages[i] = new RecordValue(new UniqueString[] { TYPE, INS, BAL, VAL },
						new Value[] { new StringValue("phase2a"), rm, bal, new StringValue(VALS[rnd.nextInt(2)]) },
						false);
				break;
			default:
				messages[i] = new RecordValue(new UniqueString[] { TYPE, ACC, INS, BAL, VAL },
						new Value[] { new StringValue("phase2b"), acc, rm, bal, new StringValue(VALS[rnd.nextInt(2)]) },
						false);
			}
		}

		// TLC fingerprints only normalized states, so the only unnormalized values
		// are the ones that permute creates.
		final Value[] vars = { new FcnRcdValue(rms.clone(), rmState, false), aState,
				new SetEnumValue(messages, false) };
		for (final Value v : vars) {
			v.deepNormalize();
		}

		// VARIABLES rmState, aState, msgs, in the order PaxosCommit declares them,
		// because that order decides how far a comparison gets. Both modes wrap the
		// variables, so the wrapper costs the same in both.
		final boolean eager = "eager".equals(normalization);
		state = TLCStates.createDummyState(3);
		for (int i = 0; i < vars.length; i++) {
			state.bind(UniqueString.of("v" + i), new Variable(vars[i], eager));
		}

		// TLCStateMut gets the symmetry group only through setTool(ITool).
		final Field f = TLCStateMut.class.getDeclaredField("perms");
		f.setAccessible(true);
		f.set(null, perms);
	}

	/**
	 * What TLC does for every new state: find the smallest state in the
	 * symmetry class of state, and fingerprint it.
	 */
	@Benchmark
	public long fingerPrint() {
		return state.fingerPrint();
	}

	/**
	 * The cost for a single nested function, without the other variables.
	 * Permuting aState creates new inner functions over Acceptor. With lazy
	 * normalization, comparing the result with aState sorts only the inner
	 * functions that it reaches.
	 */
	@Benchmark
	public int permuteAState() {
		final boolean eager = "eager".equals(normalization);
		int cmp = 0;
		for (final IMVPerm perm : perms) {
			final Value p = (Value) aState.permute(perm);
			if (eager) {
				normalizeEagerly(p, aState);
			}
			cmp += p.compareTo(aState);
		}
		return cmp;
	}

	/**
	 * Normalizes eagerly: sorts exactly the values that permute created,
	 * innermost first, and skips the unchanged ones. permute returns an
	 * unchanged value itself, and it keeps the i-th element at index i, so
	 * identity tells which values are new. This covers only the kinds of value in
	 * a PaxosCommit state.
	 */
	static void normalizeEagerly(final Value permuted, final Value original) {
		if (permuted == original) {
			return;
		}
		if (permuted instanceof SetEnumValue) {
			final SetEnumValue p = (SetEnumValue) permuted, o = (SetEnumValue) original;
			for (int i = 0; i < p.elems.size(); i++) {
				normalizeEagerly(p.elems.elementAt(i), o.elems.elementAt(i));
			}
		} else if (permuted instanceof FcnRcdValue) {
			final FcnRcdValue p = (FcnRcdValue) permuted, o = (FcnRcdValue) original;
			for (int i = 0; i < p.values.length; i++) {
				normalizeEagerly(p.values[i], o.values[i]);
			}
		} else if (permuted instanceof RecordValue) {
			final RecordValue p = (RecordValue) permuted, o = (RecordValue) original;
			for (int i = 0; i < p.values.length; i++) {
				normalizeEagerly(p.values[i], o.values[i]);
			}
		}
		permuted.normalize();
	}

	/**
	 * Wraps the value of a state variable to add eager normalization to TLC's own
	 * fingerprinting, without copying it. Fingerprinting calls only permute,
	 * compareTo, fingerPrint and deepNormalize on a variable. The other methods
	 * exist because Value declares them.
	 */
	static final class Variable extends Value {
		private final Value value;
		private final boolean eager;

		Variable(final Value value, final boolean eager) {
			this.value = value;
			this.eager = eager;
		}

		@Override
		public IValue permute(final IMVPerm perm) {
			final Value p = (Value) value.permute(perm);
			if (p == value) {
				return this;
			}
			if (eager) {
				normalizeEagerly(p, value);
			}
			return new Variable(p, eager);
		}

		@Override
		public int compareTo(final Object obj) {
			return value.compareTo(((Variable) obj).value);
		}

		@Override
		public long fingerPrint(final long fp) {
			return value.fingerPrint(fp);
		}

		@Override
		public void deepNormalize() {
			value.deepNormalize();
		}

		@Override
		public byte getKind() {
			return value.getKind();
		}

		@Override
		public boolean member(final Value elem) {
			return value.member(elem);
		}

		@Override
		public Value takeExcept(final ValueExcept ex) {
			return value.takeExcept(ex);
		}

		@Override
		public Value takeExcept(final ValueExcept[] exs) {
			return value.takeExcept(exs);
		}

		@Override
		public Value normalize() {
			value.normalize();
			return this;
		}

		@Override
		public boolean isNormalized() {
			return value.isNormalized();
		}

		@Override
		public boolean isFinite() {
			return value.isFinite();
		}

		@Override
		public int size() {
			return value.size();
		}

		@Override
		public boolean isDefined() {
			return value.isDefined();
		}

		@Override
		public IValue deepCopy() {
			return new Variable((Value) value.deepCopy(), eager);
		}

		@Override
		public StringBuffer toString(final StringBuffer sb, final int offset, final boolean swallow) {
			return value.toString(sb, offset, swallow);
		}
	}

	/** Permutations(mvs), i.e. every bijection from mvs to mvs. */
	private static Value[] permutations(final Value[] mvs) {
		final List<Value> res = new ArrayList<>();
		permute(mvs, mvs.clone(), 0, res);
		return res.toArray(Value[]::new);
	}

	/**
	 * Adds to res the function from domain to each ordering of a that keeps
	 * a[0..k-1] fixed.
	 */
	private static void permute(final Value[] domain, final Value[] a, final int k, final List<Value> res) {
		if (k == a.length) {
			res.add(new FcnRcdValue(domain.clone(), a.clone(), false));
			return;
		}
		for (int i = k; i < a.length; i++) {
			swap(a, k, i);
			permute(domain, a, k + 1, res);
			swap(a, k, i);
		}
	}

	private static void swap(final Value[] a, final int i, final int j) {
		final Value t = a[i];
		a[i] = a[j];
		a[j] = t;
	}

	private static Value[] concat(final Value[] a, final Value[] b) {
		final Value[] res = new Value[a.length + b.length];
		System.arraycopy(a, 0, res, 0, a.length);
		System.arraycopy(b, 0, res, a.length, b.length);
		return res;
	}

	public static void main(String[] args) throws RunnerException {
		final Options opt = new OptionsBuilder().include(SymmetryFingerprintBenchmark.class.getSimpleName())
				.build();
		new Runner(opt).run();
	}
}
