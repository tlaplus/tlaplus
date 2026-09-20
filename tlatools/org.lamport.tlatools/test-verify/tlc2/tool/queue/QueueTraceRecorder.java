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
 ******************************************************************************/
package tlc2.tool.queue;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import gov.nasa.jpf.ListenerAdapter;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.vm.ThreadInfo;

/**
 * Shares execution prefixes outside JPF's state and restores the current prefix
 * on backtracking. Publishes the tree only after exhaustive depth-first search.
 * Subclasses determine which implementation events are observed.
 */
public abstract class QueueTraceRecorder extends ListenerAdapter {

	private final Map<String, Integer> edges = new HashMap<>();
	private final List<String> nodes = new ArrayList<>(List.of("parent\tthread\taction"));
	private final List<Integer> prefixesByDepth = new ArrayList<>(List.of(0));
	private int current;
	private boolean limited;

	protected final void record(ThreadInfo thread, String action) {
		String edge = current + "\t" + thread.getName() + "\t" + action;
		Integer child = edges.get(edge);
		if (child == null) {
			child = nodes.size();
			nodes.add(edge);
			edges.put(edge, child);
		}
		current = child;
	}

	@Override
	public void stateAdvanced(Search search) {
		prefixesByDepth.add(current);
	}

	@Override
	public void stateBacktracked(Search search) {
		int depth = search.getDepth();
		prefixesByDepth.subList(depth + 1, prefixesByDepth.size()).clear();
		current = prefixesByDepth.get(depth);
	}

	@Override
	public void stateRestored(Search search) {
		throw new IllegalStateException("Use depth-first search for queue trace collection");
	}

	@Override
	public void searchConstraintHit(Search search) {
		limited = true;
	}

	@Override
	public void searchFinished(Search search) {
		if (limited || search.isDone() || search.getDepth() != 0 || !search.getErrors().isEmpty()) {
			throw new IllegalStateException("JPF search did not finish successfully");
		}
		try {
			Files.write(Path.of("nodes.tsv"), nodes);
			System.out.println("Recorded " + (nodes.size() - 1) + " queue execution prefixes.");
		} catch (IOException e) {
			throw new UncheckedIOException(e);
		}
	}
}
