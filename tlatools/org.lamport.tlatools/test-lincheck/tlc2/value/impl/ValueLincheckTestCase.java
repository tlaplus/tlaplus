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
package tlc2.value.impl;

import static net.bytebuddy.matcher.ElementMatchers.named;
import static net.bytebuddy.matcher.ElementMatchers.takesArguments;
import static tlc2.value.impl.ValueFixtures.ints;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import org.jetbrains.kotlinx.lincheck.Actor;
import org.jetbrains.kotlinx.lincheck.execution.ExecutionScenario;
import org.jetbrains.lincheck.datastructures.ModelCheckingOptions;
import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.BeforeClass;
import org.junit.Test;

import kotlin.jvm.internal.Intrinsics;
import net.bytebuddy.ByteBuddy;
import net.bytebuddy.agent.ByteBuddyAgent;
import net.bytebuddy.asm.Advice;
import net.bytebuddy.dynamic.loading.ClassReloadingStrategy;
import tlc2.util.FP64;
import util.UniqueString;

/**
 * Workers that concurrently call the operations of a subclass on the same
 * values, which the subclass creates, must get results that some sequential
 * order of the same calls also gets. Every subclass can fingerprint its
 * {@link #value()}, which normalizes it. Lincheck creates the subclass anew for
 * every interleaving with its public constructor, which takes no arguments. {@link #modelChecking()} checks interleavings of a random
 * scenario, and subclasses check the interleavings of specific scenarios with
 * {@link #modelCheckingParallel(String...)}.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public abstract class ValueLincheckTestCase {

	static {
		FP64.Init();
	}

	// A record sorts its fields in the order in which their names were interned,
	// which is f1, f2, f3.
	protected static final UniqueString F1 = UniqueString.of("f1");
	protected static final UniqueString F2 = UniqueString.of("f2");
	protected static final UniqueString F3 = UniqueString.of("f3");

	/**
	 * The function (3 :> 30 @@ 1 :> 10 @@ 2 :> 20), whose domain is not
	 * normalized.
	 */
	protected static FcnRcdValue unsortedFcn() {
		return new FcnRcdValue(ints(3, 1, 2), ints(30, 10, 20), false);
	}

	/**
	 * The function (1 :> 10 @@ 2 :> 20 @@ m :> 30), whose domain is not
	 * normalized, for the untyped model value m, which precedes every integer.
	 */
	protected static FcnRcdValue unsortedMixedFcn() {
		return new FcnRcdValue(new Value[] { IntValue.gen(1), IntValue.gen(2), ModelValue.make("m") },
				ints(10, 20, 30), false);
	}

	/**
	 * The set {3, 1, 2}, whose elements are not normalized.
	 */
	protected static SetEnumValue unsortedSet() {
		return new SetEnumValue(ints(3, 1, 2), false);
	}

	/**
	 * The record [f3 |-> 30, f1 |-> 10, f2 |-> 20], whose fields are not
	 * normalized.
	 */
	protected static RecordValue unsortedRcd() {
		return new RecordValue(new UniqueString[] { F3, F1, F2 }, ints(30, 10, 20), false);
	}

	/**
	 * Sorts the given function, whose values are integers, and applies it to arg.
	 */
	protected static int sortAndSelect(final FcnRcdValue fcn, final Value arg) {
		fcn.normalize();
		return ((IntValue) fcn.select(arg)).val;
	}

	/**
	 * The elements that the enumeration returns, each followed by a space.
	 */
	protected static String enumerate(final ValueEnumeration elements) {
		final StringBuilder sb = new StringBuilder();
		Value elem;
		while ((elem = elements.nextElement()) != null) {
			sb.append(elem).append(' ');
		}
		return sb.toString();
	}

	protected interface Evaluation<V> {
		Object of(V value) throws IOException;
	}

	/**
	 * Evaluates op of a value that the supplier creates, and of one that it
	 * creates and this normalizes. Json and TLC#ToString intern their results in
	 * UniqueString's table, which outlives an interleaving. Interning a string for
	 * the first time takes more steps than finding it, so Lincheck's replay of a
	 * failing interleaving would diverge and report non-determinism instead of
	 * the failure.
	 */
	protected static <V extends Value> void internResults(final Supplier<V> value, final Evaluation<V> op) {
		try {
			op.of(value.get());
			final V sorted = value.get();
			sorted.normalize();
			op.of(sorted);
		} catch (IOException e) {
			throw new UncheckedIOException(e);
		}
	}

	/**
	 * The value that {@link #fingerPrint()} fingerprints, which the subclass
	 * shares between the workers.
	 */
	protected abstract Value value();

	@Operation
	public long fingerPrint() {
		return value().fingerPrint(FP64.New());
	}

	/**
	 * In model checking mode, Lincheck compares the receiver of every method call
	 * with the standard streams, and Kotlin compiles the comparison to
	 * Intrinsics#areEqual, which calls the receiver's equals. The equals of a TLC
	 * value fails for a non-value, and the equals of a lazy set populates the
	 * set's cache outside Lincheck's analysis. The streams don't override equals,
	 * so comparing them by identity is what equals would do.
	 * 
	 * @see https://github.com/JetBrains/lincheck/issues/1048
	 */
	@BeforeClass
	public static void compareStandardStreamsByIdentity() {
		ByteBuddyAgent.install();
		new ByteBuddy().redefine(Intrinsics.class)
			.visit(Advice.to(AreEqual.class).on(named("areEqual").and(takesArguments(Object.class, Object.class))))
			.make()
			.load(Intrinsics.class.getClassLoader(), ClassReloadingStrategy.fromInstalledAgent());
	}

	static class AreEqual {
		@Advice.OnMethodEnter(skipOn = Advice.OnNonDefaultValue.class)
		static boolean enter(@Advice.Argument(1) final Object second) {
			return second == System.in || second == System.out || second == System.err;
		}

		@Advice.OnMethodExit
		static void exit(@Advice.Enter final boolean skipped, @Advice.Argument(0) final Object first,
				@Advice.Argument(1) final Object second, @Advice.Return(readOnly = false) boolean equal) {
			if (skipped) {
				equal = first == second;
			}
		}
	}

	@Test
	public void modelChecking() {
		new ModelCheckingOptions()
			// A sequential call before the workers start would normalize the value.
			.actorsBefore(0)
			.iterations(1)
			.check(getClass());
	}

	/**
	 * Checks interleavings of one scenario, in which each worker calls one of the
	 * given operations, instead of a random scenario. Lincheck stops after 10,000
	 * interleavings, its default, which suffices for two workers.
	 */
	protected final void modelCheckingParallel(final String... operations) {
		modelCheckingParallel(10_000, operations);
	}

	/**
	 * Like {@link #modelCheckingParallel(String...)}, but stops after the given
	 * number of interleavings, which an interleaving that switches between three
	 * workers several times may need.
	 */
	protected final void modelCheckingParallel(final int interleavings, final String... operations) {
		final List<List<Actor>> threads = new ArrayList<>();
		for (final String operation : operations) {
			try {
				threads.add(List.of(new Actor(getClass().getMethod(operation), List.of())));
			} catch (NoSuchMethodException e) {
				throw new IllegalArgumentException(e);
			}
		}
		new ModelCheckingOptions()
			.addCustomScenario(new ExecutionScenario(List.of(), threads, List.of(), null))
			.iterations(0)
			.invocationsPerIteration(interleavings)
			.check(getClass());
	}
}
