import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import jdk.jfr.consumer.RecordedEvent;
import jdk.jfr.consumer.RecordingFile;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.UniqueString;

/**
 * Makes a JFR recording of the Java queue available to TLC so it can be replayed
 * against the TLA+ queue specification. Each recorded event names the thread and
 * the queue action it performed; no intermediate text trace needs to be written.
 *
 * <p>
 * This class reads the recording and groups events with the same timestamp so
 * the replay can try their possible orders while preserving each thread's own
 * order. See the comment above {@code RecordedStep} in
 * {@code DiskStateQueueTrace.tla} for how TLA+ nondeterminism handles these ties.
 * The queue's buffer size is supplied separately.
 *
 * <p>
 * TLC calls the methods below in place of the operators in
 * {@code QueueTraceData.tla}. They supply the recorded events and the information
 * needed to replay them. {@code DiskStateQueueTrace.tla} checks whether the queue
 * specification can follow those events, and {@code _POSSIBLE TraceComplete}
 * requires a replay that consumes the entire recording. This class supplies
 * input only: it neither implements the queue's behavior nor decides whether a
 * trace matches the spec.
 */
public final class QueueTraceData {

	private static final StringValue EMPTY = new StringValue("");
	private static final Data DATA = read();

	private static final class Event {

		final String thread, action;
		final long time;
		final int seq;

		Event(String thread, String action, long time, int seq) {
			this.thread = thread;
			this.action = action;
			this.time = time;
			this.seq = seq;
		}
	}

	private static final class Data {

		RecordValue[] events;
		StringValue[] actions;
		int[] ends, previous;
		Map<String, int[]> byThread = new TreeMap<>();
		SetEnumValue threads, workers;
		int capacity;
	}

	private static RecordValue record(String[] names, Value... values) {
		UniqueString[] keys = Arrays.stream(names).map(UniqueString::uniqueStringOf).toArray(UniqueString[]::new);
		return new RecordValue(keys, values, false);
	}

	private static String required(String key) {
		String value = System.getProperty(key);
		if (value == null || value.isEmpty()) {
			throw new IllegalArgumentException("Missing -D" + key);
		}
		return value;
	}

	/**
	 * Reads queue events from JFR, sorts them by raw timestamp, thread, and sequence
	 * number, and stores them as TLC records in 1-based arrays.
	 * Records timestamp-group boundaries and each event's same-thread predecessor
	 * within its group so replay can explore tied events in valid orders. Builds
	 * per-thread event indexes for looking ahead to a thread's next action.
	 */
	private static Data read() {
		try {
			// Read the queue capacity supplied by the test configuration.
			Data data = new Data();
			data.capacity = Integer.parseInt(required("queue.capacity"));
			if (data.capacity < 1) {
				throw new IllegalArgumentException("Capacity must be positive");
			}

			// Extract queue actions, thread names, timestamps, and sequence numbers from JFR.
			List<Event> events = new ArrayList<>();
			try (RecordingFile input = new RecordingFile(Path.of(required("queue.trace")))) {
				while (input.hasMoreEvents()) {
					RecordedEvent raw = input.readEvent();
					if (!raw.getEventType().getName().equals("tlc2.DiskStateQueue")) {
						continue;
					}
					String name = raw.getThread().getJavaName();
					int seq = Math.toIntExact(raw.getLong("seq"));
					// Use raw ticks: getStartTime()'s wall-clock conversion can jump backward
					// at recording-chunk boundaries.
					// See OpenJDK's chunk timestamp sampling:
					// https://github.com/openjdk/jdk11u/blob/master/src/hotspot/share/jfr/recorder/repository/jfrChunkState.cpp
					// and timestamp conversion:
					// https://github.com/openjdk/jdk11u/blob/master/src/jdk.jfr/share/classes/jdk/jfr/consumer/TimeConverter.java
					long time = raw.getLong("startTime");
					String action = raw.getString("action");
					events.add(new Event(name, action, time, seq));
				}
			}
			if (events.isEmpty()) {
				throw new IllegalArgumentException("Empty trace");
			}

			// Sort by time, preserving same-thread order within timestamp ties.
			// Thread-name tie-breaking is only for storage; replay explores the interleavings.
			events.sort(Comparator.comparingLong((Event e) -> e.time).thenComparing(e -> e.thread)
					.thenComparingInt(e -> e.seq));

			// Allocate 1-based replay arrays; index zero is unused.
			int n = events.size();
			data.events = new RecordValue[n + 1];
			data.actions = new StringValue[n + 1];
			data.ends = new int[n + 1];
			data.previous = new int[n + 1];
			Map<String, Integer> last = new HashMap<>();
			Map<String, List<Integer>> byThread = new TreeMap<>();

			// Build TLC records and ordering information one timestamp group at a time.
			for (int start = 1; start <= n;) {
				// Find the last event with the same timestamp as the group's first event.
				int end = start;
				while (end < n && events.get(end).time == events.get(start - 1).time) {
					end++;
				}

				// Convert events and link each to its same-thread predecessor in this group.
				last.clear();
				for (int i = start; i <= end; i++) {
					Event e = events.get(i - 1);
					byThread.computeIfAbsent(e.thread, k -> new ArrayList<>()).add(i);
					data.actions[i] = new StringValue(e.action);
					data.events[i] = record(new String[] { "action", "thread" }, data.actions[i],
							new StringValue(e.thread));
					data.ends[i] = end;
					data.previous[i] = last.getOrDefault(e.thread, 0);
					last.put(e.thread, i);
				}
				start = end + 1;
			}

			// Finalize per-thread lookahead indexes and the thread/worker sets used by TLC.
			byThread.forEach((thread, indices) -> data.byThread.put(thread,
					indices.stream().mapToInt(Integer::intValue).toArray()));
			data.threads = new SetEnumValue(
					data.byThread.keySet().stream().map(StringValue::new).toArray(Value[]::new), false);
			data.workers = new SetEnumValue(data.byThread.keySet().stream().filter(s -> s.startsWith("TLCWorkerThread-"))
					.map(StringValue::new).toArray(Value[]::new), false);

			return data;
		} catch (Exception e) {
			throw new ExceptionInInitializerError(e);
		}
	}

	public static Value TraceLength() {
		return IntValue.gen(DATA.events.length - 1);
	}

	public static Value TraceThreads() {
		return DATA.threads;
	}

	public static Value TraceWorkers() {
		return DATA.workers;
	}

	public static Value BufferCapacity() {
		return IntValue.gen(DATA.capacity);
	}

	public static Value EventAt(Value index) {
		return DATA.events[((IntValue) index).val];
	}

	public static Value GroupEnd(Value index) {
		return IntValue.gen(DATA.ends[((IntValue) index).val]);
	}

	public static Value PreviousInGroup(Value index) {
		return IntValue.gen(DATA.previous[((IntValue) index).val]);
	}

	public static Value NextAction(Value thread, Value index, Value used) {
		int[] indices = DATA.byThread.get(((StringValue) thread).val.toString());
		if (indices == null) {
			return EMPTY;
		}
		int offset = Arrays.binarySearch(indices, ((IntValue) index).val);
		if (offset < 0) {
			offset = -offset - 1;
		}
		while (offset < indices.length && used.member(IntValue.gen(indices[offset]))) {
			offset++;
		}
		return offset < indices.length ? DATA.actions[indices[offset]] : EMPTY;
	}
}
