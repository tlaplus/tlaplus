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
import java.io.BufferedReader;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.UniqueString;

/**
 * Makes the JPF queue listeners' prefix trees available to TLC for trace
 * validation.
 * Each row in {@code nodes.tsv} adds one event (a thread and an action) to its
 * parent's history. Node zero is the empty history; subsequent node numbers are
 * the data rows' positions. Shared prefixes need not be expanded into separate
 * trace files.
 *
 * <p>
 * TLC calls these methods in place of the operators in {@code QueueJpfData.tla}.
 * The replay advances to a child only when the queue specification matches that
 * child's event. Its postcondition requires every node to have been reached by
 * at least one replay. This checks every recorded execution prefix, including
 * those ending at internal nodes, without a separate list of prefixes.
 *
 * <p>
 * A recorded prefix may end when JPF matches an already explored state, before
 * the Java execution terminates. Replay checks the recorded prefixes, not
 * executions JPF did not explore. This class supplies input only; it does not
 * implement queue transitions or decide whether replay succeeds.
 */
public final class QueueJpfData {

	private static final List<RecordValue> EVENTS = new ArrayList<>();
	private static final List<SetEnumValue> CHILDREN = new ArrayList<>();

	static {
		// Node zero denotes the empty execution prefix.
		EVENTS.add(null);
		List<List<Value>> children = new ArrayList<>();
		children.add(new ArrayList<>());
		try (BufferedReader input = Files.newBufferedReader(Path.of("nodes.tsv"))) {
			input.readLine(); // parent, thread, action
			for (String line; (line = input.readLine()) != null;) {
				String[] row = line.split("\t");
				int parent = Integer.parseInt(row[0]);
				children.get(parent).add(IntValue.gen(EVENTS.size()));
				EVENTS.add(new RecordValue(
						new UniqueString[] { UniqueString.of("thread"), UniqueString.of("action") },
						new Value[] { new StringValue(row[1]), new StringValue(row[2]) }, false));
				children.add(new ArrayList<>());
			}
		} catch (IOException e) {
			throw new UncheckedIOException(e);
		}
		children.forEach(c -> CHILDREN.add(new SetEnumValue(c.toArray(new Value[0]), false)));
	}

	public static Value JpfNodeCount() {
		return IntValue.gen(EVENTS.size() - 1);
	}

	public static Value JpfChildren(Value node) {
		return CHILDREN.get(((IntValue) node).val);
	}

	public static Value JpfEvent(Value node) {
		return EVENTS.get(((IntValue) node).val);
	}
}
