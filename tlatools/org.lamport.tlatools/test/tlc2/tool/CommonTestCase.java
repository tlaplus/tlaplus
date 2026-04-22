/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
 * Copyright (c) 2023, 2024, Oracle and/or its affiliates.
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.runner.RunWith;

import tla2sany.output.SilentSanyOutput;
import tla2sany.parser.TLAplusParser;
import tla2sany.parser.ParseException;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParserConstants;
import tla2sany.st.SyntaxTreeConstants;
import tlc2.TLCGlobals;
import tlc2.TestMPRecorder;
import tlc2.TestMPRecorder.Coverage;
import tlc2.output.EC;
import tlc2.tool.liveness.GraphNode;
import tlc2.util.BitVector;
import tlc2.util.BufferedRandomAccessFile;
import util.IsolatedTestCaseRunner;

@RunWith(IsolatedTestCaseRunner.class)
public abstract class CommonTestCase {

	public static final String BASE_DIR = System.getProperty("basedir", System.getProperty("user.dir", "."));
	protected static final String TEST_MODEL = "test-model" + File.separator;
	public static final String BASE_PATH = System.getProperty("basepath", BASE_DIR + File.separator + TEST_MODEL);

	protected final TestMPRecorder recorder;

	public CommonTestCase() {
		this(new TestMPRecorder());
	}
	
	public CommonTestCase(final TestMPRecorder testMPRecorder) {
		recorder = testMPRecorder;
	}

	protected boolean isExtendedTLCState() {
		return TLCState.Empty instanceof TLCStateMutExt;
	}
	
	protected void assertState(final List<Object> actual, final int ordinal, final String expectedState, final String expectedAction) {
		assertTrue(actual.size() >= ordinal);
		final Object[] objs = (Object[]) actual.get(ordinal - 1);

		assertEquals(ordinal, objs[1]);

		final TLCStateInfo stateInfo = (TLCStateInfo) objs[0];
		assertEquals(expectedState, stateInfo.toString().trim()); // trimmed to remove any newlines or whitespace

		final String info = (String) stateInfo.info;
		assertEquals(expectedAction, info);
	}

	/**
	 * Asserts that the actual trace and the expected error trace are equal
	 * under permutation. This check should still succeed even if the order of
	 * variables in the state conjunction changes.
	 * 
	 * @param actual
	 *            The actual trace as recorded by {@link MPRecorder}.
	 * @param expectedTrace
	 *            The expected trace.
	 */
	protected void assertTraceWith(final List<Object> actual, final List<String> expectedTrace) {
		assertEquals(expectedTrace.size(), actual.size());
		int[] permutation = null;
		for (int i = 0; i < expectedTrace.size(); i++) {
			final Object[] objs = (Object[]) actual.get(i);
			final TLCStateInfo stateInfo = (TLCStateInfo) objs[0];
			final String info = (String) stateInfo.info;
			if (i == 0 && !isExtendedTLCState()) {
				// The first state has to be an initial state.
				assertEquals("<Initial predicate>", info);
			} else {
				// ... all others are reachable via an action.
				//TODO: Assert actual action names.
				assertNotEquals("<Initial predicate>", info);
				assertFalse(info.startsWith("<Action"));
			}
			permutation = assertStateEqualUnderPermutation(permutation, expectedTrace.get(i), stateInfo.toString().trim());
			assertEquals(i+1, objs[1]);
		}
	}
	
	/**
	 * Given serialized representations of states like:
	 *   /\ x = 1
	 *   /\ y = 2
	 * this function checks the states for equality by matching conjuncts
	 * regardless of order; thus the above state will be equal to:
	 *   /\ y = 2
	 *   /\ x = 1
	 * If this function is called with the permutation argument set to null,
	 * the function attempts to derive a permutation for which comparison is
	 * true, then returns that permutation; the permutation should be given as
	 * a parameter to subsequent calls to this function for the same trace.
	 *
	 * Only re-ordering of top-level conjuncts is supported. Future work could
	 * possibly expand to analyzing the abstract syntax tree itself, or even
	 * rehydrating the state in TLC to compare it that way and avoid all tricky
	 * string mismatch issues. While from this point forward TLC should print
	 * out states with variables in a stable order, this permutation function
	 * was written to avoid the very tedious task of converting all existing
	 * unit test traces to use the new stable ordering.
	 */
	private static int[] assertStateEqualUnderPermutation(
	    int[] permutation,
	    final String expected,
	    final String actual
	) {
	  final List<String> expectedVariables = splitStateOnVariables(expected);
	  final List<String> actualVariables = splitStateOnVariables(actual);
	  assertEquals(expectedVariables.size(), actualVariables.size());
	  final int n = expectedVariables.size();
	  if (null == permutation) {
	    permutation = new int[n];
	    for (int i = 0; i < n; i++) {
	      permutation[i] = -1;
	      for (int j = 0; j < n; j++) {
	        if (expectedVariables.get(i).trim().equals(actualVariables.get(j).trim())) {
	          permutation[i] = j;
	          break;
	        }
	      }
	      assertNotEquals(
	          String.format(
	              "Conjunct %d of the expected state could not be matched to any conjunct in the actual state; expected:\n%s\nactual:\n%s",
	              i,
	              expectedVariables.get(i),
	              actualVariables.toString()
	           ), -1, permutation[i]);
	    }
	  }

	  assertEquals(n, permutation.length);
	  for (int i = 0; i < n; i++) {
	    assertEquals(expectedVariables.get(i).trim(), actualVariables.get(permutation[i]).trim());
	  }

	  return permutation;
	}
	
	/**
	 * Given a serialized representation of a state like:
	 *  /\ x = 1
	 *  /\ y = 2
	 *
	 * This function parses the state as a conjunction list then returns each
	 * conjunct as a separate string.
	 */
	private static List<String> splitStateOnVariables(String state) {
    final List<String> variables = new ArrayList<>();
	  final TLAplusParser parser = new TLAplusParser(new SilentSanyOutput(), state.getBytes(StandardCharsets.UTF_8));
    parser.token_source.SwitchTo(TLAplusParserConstants.SPEC);
    try {
      final SyntaxTreeNode expr = parser.Expression();
      if (expr.isKind(SyntaxTreeConstants.N_ConjList)) {
        for (final SyntaxTreeNode conjunct : expr.getHeirs()) {
          variables.add(conjunct.getLocation().getSourceCodeExcerpt(state));
        }
      } else {
        // If state is not a conjunction list, there is only one variable.
        variables.add(state);
      }
    } catch (ParseException e) {
      fail(e.toString());
    }

    return variables;
	}
	
	/**
	 * @see assertTraceWith above except that this method also asserts matching names for the initial predicate and the sub-actions of the next-state relation.
	 */
	protected void assertTraceWith(final List<Object> actual, final List<String> expectedTrace, final List<String> expectedActions) {
		assertEquals(expectedTrace.size(), actual.size());
		int[] permutation = null;
		for (int i = 0; i < expectedTrace.size(); i++) {
			final Object[] objs = (Object[]) actual.get(i);
			final TLCStateInfo stateInfo = (TLCStateInfo) objs[0];
			final String info = (String) stateInfo.info;
			assertEquals(expectedActions.get(i), info);
			permutation = assertStateEqualUnderPermutation(permutation, expectedTrace.get(i), stateInfo.toString().trim());
			assertEquals(i + 1, objs[1]);
		}
	}

	/**
	 * Asserts that the error trace ends in stuttering at the given number.
	 * 
	 * @param stateNum
	 *            The number of the stuttering state
	 */
	protected void assertStuttering(int stateNum) {
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT3));
		List<Object> stutter = recorder.getRecords(EC.TLC_STATE_PRINT3);
		assertTrue(stutter.size() > 0);
		Object[] object = (Object[]) stutter.get(0);
		assertEquals(stateNum, object[1]);
	}

	/**
	 * Asserts that the error trace loops back to some predecessor state.
	 */
	protected void assertBackToState() {
		assertTrue(recorder.recorded(EC.TLC_BACK_TO_STATE));
		final List<Object> loop = recorder.getRecords(EC.TLC_BACK_TO_STATE);
		assertTrue(loop.size() > 0);
	}

	/**
	 * Asserts that the error trace loops back to the state with the given
	 * number.
	 * 
	 * @param i The loop back state number.
	 */
	protected void assertBackToState(int stateNum) {
		assertTrue(recorder.recorded(EC.TLC_BACK_TO_STATE));
		List<Object> loop = recorder.getRecords(EC.TLC_BACK_TO_STATE);
		assertTrue(loop.size() > 0);
		Object[] object = (Object[]) loop.get(0);
		assertEquals(Integer.toString(stateNum), object[0]);
	}

	/**
	 * Asserts that the error trace loops back to the state with the given
	 * number.
	 * 
	 * @param i The loop back state number.
	 * @param action The action label associated with the loop back marker
	 */
	protected void assertBackToState(int stateNum, final String action) {
		assertTrue(recorder.recorded(EC.TLC_BACK_TO_STATE));
		List<Object> loop = recorder.getRecords(EC.TLC_BACK_TO_STATE);
		assertTrue(loop.size() > 0);
		Object[] object = (Object[]) loop.get(0);
		assertTrue(object.length > 1);
		assertEquals(Integer.toString(stateNum), object[0]);
		assertEquals(action, object[1]);
	}

	/**
	 * Check the file size of the AbstractDiskGraph files to assert that the
	 * expected amount of ptrs and nodes (outgoing arcs) have been written to
	 * disk.
	 * <p>
	 * CAUTION: The order in which the transitions are inserted into the
	 * {@link GraphNode} determines the size of the {@link BitVector}. I.e. if
	 * the truth values of the first N nodes inserted are true, and the
	 * remainder is false, the BitVector's size will correspond to N. However,
	 * if the first N truth values are false, followed by M trues, the
	 * BitVector's size is N + M.
	 * <p>
	 * See {@link GraphNode}'s constructor: it initializes {@link BitVector}
	 * with capacity zero and subsequently grows BV when bits are set to true.
	 * <p>
	 * 
	 * @see BitVector#read(BufferedRandomAccessFile)
	 * @see BitVector#write(BufferedRandomAccessFile)
	 * @see GraphNode#read(BufferedRandomAccessFile)
	 * @see GraphNode#write(BufferedRandomAccessFile)
	 * 
	 * @param nodesSize
	 * @param ptrsSize
	 */
	protected void assertNodeAndPtrSizes(final long nodesSize, final long ptrsSize) {
		// Make sure the liveness checker has flushed all its data to disk to ensure that
		// the nodes_0 and ptrs_0 files really include everything written so far.
		try {
			TLCGlobals.mainChecker.liveCheck.flushWritesToDiskFiles();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}

		final String metadir = TLCGlobals.mainChecker.metadir;
		assertNotNull(metadir);
		
		final File nodes = new File(metadir + File.separator + "nodes_0");
		assertTrue(nodes.exists());
		assertEquals(nodesSize, nodes.length());
	
		final File ptrs =  new File(metadir + File.separator + "ptrs_0");
		assertTrue(ptrs.exists());
		assertEquals(ptrsSize, ptrs.length());
	}

	// Checks if all uncovered (zero) lines are found and no more (don't care if the invocation and costs match).
	protected void assertUncovered(final String expectedUncovered) {
		final List<Coverage> expected = Arrays.asList(expectedUncovered.trim().split("\n")).stream()
				.map(o -> new Coverage(o.split(":"))).collect(Collectors.toList());

		final Set<Coverage> expectedZero = expected.stream().filter(Coverage::isZero).collect(Collectors.toSet());
		final Set<Coverage> actualZeroCoverage = recorder.getZeroCoverage().stream().collect(Collectors.toSet());
		assertEquals(expectedZero, actualZeroCoverage);
	}
	
	protected void assertZeroUncovered() {
		assertTrue(recorder.getZeroCoverage().isEmpty());
	}

	// Assert that no TE spec was generated.
	protected void assertNoTESpec() {
		assertFalse("A TE spec was generated, but it shouldn't", 
			recorder.recorded(EC.TLC_TE_SPEC_GENERATION_COMPLETE));
	}
	
	protected void assertCoverage(final String expectedCoverage) {
		// Lines can be reported multiple times if invoked from different actions!!!
		
		final List<Coverage> expected = Arrays.asList(expectedCoverage.split("\n")).stream()
				.map(o -> new Coverage(o.split(":"))).collect(Collectors.toList());
		
		// Step A:
		// Validation of coverage results is split into two steps. Step A checks if all
		// uncovered (zero) lines are found, step B checks if non-zero lines exist.		
		final Set<Coverage> expectedZero = expected.stream().filter(Coverage::isZero)
				.filter(Coverage::isCoverage).collect(Collectors.toSet());
		final Set<Coverage> actualZeroCoverage = recorder.getZeroCoverage().stream().collect(Collectors.toSet());
		assertEquals(expectedZero, actualZeroCoverage);
		
		// Step B1 (coverage):
		final List<Coverage> actualNonZeroCoverage = recorder.getNonZeroCoverage();
		final List<Coverage> expectedNonZeroCoverage = expected.stream().filter(Coverage::isCoverage).
				filter(c -> !c.isCost()).collect(Collectors.toList());
		expectedNonZeroCoverage.removeAll(actualZeroCoverage);
		for (int i = 0; i < actualNonZeroCoverage.size(); i++) {
			final Coverage a = actualNonZeroCoverage.get(i);
			final Coverage e = expectedNonZeroCoverage.get(i);
			assertEquals(e, a);
		}
		assertTrue(expectedNonZeroCoverage.size() == actualNonZeroCoverage.size());
		
		// Step B2 (coverage with cost):
		final List<Coverage> actualCostCoverage = recorder.getCostCoverage();
		final List<Coverage> expectedCostCoverage = expected.stream().filter(Coverage::isCoverage)
				.filter(Coverage::isCost).collect(Collectors.toList());
		for (int i = 0; i < actualCostCoverage.size(); i++) {
			final Coverage a = actualCostCoverage.get(i);
			final Coverage e = expectedCostCoverage.get(i);
			assertEquals(e, a);
		}
		assertTrue(expectedCostCoverage.size() == actualCostCoverage.size());
		
		// Step C (actions):
		final List<Coverage> actualActions = recorder.getActionCoverage();
		final List<Coverage> expectedActions = expected.stream().filter(Coverage::isAction).collect(Collectors.toList());
		for (int i = 0; i < actualActions.size(); i++) {
			final Coverage a = actualActions.get(i);
			final Coverage e = expectedActions.get(i);
			assertEquals(e, a);
		}
		assertTrue(expectedActions.size() == actualActions.size());
	}
}
