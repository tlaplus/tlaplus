// Copyright (c) 2024, Oracle and/or its affiliates.

package tlc2.util;

import org.junit.Assert;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.Random;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Fuzz testing for {@link BufferedRandomAccessFile}.
 *
 * <p>This fuzzer generates many random lists of file operations ({@link FileOperation}) and validates that executing
 * those operations has the same outcome whether applied to a {@link RandomAccessFile} or a
 * {@link BufferedRandomAccessFile}.
 *
 * <p>Not all lists of operations result in well-defined behavior.  For instance, some writes fill the file with
 * arbitrary bytes, and reads at those positions are not well-defined.  When randomly generating operations, this test
 * simulates the operations on a lightweight in-memory representation of the file ({@link AbstractFileState}) which has
 * helpers to indicate if an operation would result in undefined output.  Those undefined operations are omitted from
 * the generated list.
 */
public class BufferedRandomAccessFileFuzzTest {

    /** The number of threads to use for fuzzing, to explore more traces in less time. */
    private static final int THREAD_COUNT = Runtime.getRuntime().availableProcessors();

    /** How much fuzzing to do before declaring success. */
    private static final int TRACES_TO_EXPLORE_PER_THREAD = 10_000;

    /**
     * A bound on various operation parameters, like how far to seek or how many bytes to read.  As a sort of grey-box
     * testing technique, the bound is larger than {@link BufferedRandomAccessFile#BuffSz}.
     */
    private static final int BOUND = BufferedRandomAccessFile.BuffSz * 2;

    /**
     * Fuzz test {@link BufferedRandomAccessFile}.
     *
     * @throws IOException if an I/O error occurs
     * @throws RuntimeException if an erroneous trace is discovered; the trace will be minimized and written to stdout
     */
    @Test
    public void fuzz() throws IOException {
        // shared state
        AtomicInteger nextOp = new AtomicInteger(1);
        AtomicBoolean running = new AtomicBoolean(true);
        AtomicReference<RunResult> badResult = new AtomicReference<>(null);
        AtomicReference<Throwable> error = new AtomicReference<>(null);
        Object outputLock = new Object();

        List<Thread> threads = new ArrayList<>(THREAD_COUNT);
        for (int i = 0; i < THREAD_COUNT; ++i) {
            final int threadID = i;
            Thread t = new Thread(() -> {
                Random rng = new Random(threadID);
                while (running.get()) {
                    int runID = nextOp.getAndIncrement();
                    if (runID > TRACES_TO_EXPLORE_PER_THREAD) {
                        return;
                    }
                    synchronized (outputLock) {
                        System.out.println("---- starting run " + runID);
                    }
                    try {
                        RunResult result = checkBufferedRandomAccessFileBehavior(generateRandomOps(rng, 50));
                        if (!result.ok()) {
                            badResult.set(result);
                            running.set(false);
                        }
                    } catch (Throwable e) {
                        error.set(e);
                        running.set(false);
                        return;
                    }
                }
            });
            t.setName(getClass().getSimpleName() + "-worker-" + threadID);
            t.setDaemon(true);
            t.start();
            threads.add(t);
        }

        for (Thread t : threads) {
            try {
                t.join();
            } catch (InterruptedException ignored) {
            }
        }

        RunResult result = badResult.get();
        if (result != null && !result.ok()) {
            System.out.println("Violation found on op # " + result.successes + "; minimizing...");
            java.util.List<FileOperation<?>> minimalOps = minimize(
                    result.ops.subList(0, result.successes + 1),
                    (subset) -> wellDefined(subset) && !checkBufferedRandomAccessFileBehavior(subset).ok());
            System.out.println("Minimal trace:");
            for (FileOperation<?> op : minimalOps) {
                System.out.println(" --> " + op);
            }
            RunResult minResult = checkBufferedRandomAccessFileBehavior(minimalOps);
            throw new RuntimeException("got " + minResult.actual + " but expected " + minResult.expected);
        }

        Throwable thrown = error.get();
        if (thrown != null) {
            throw new RuntimeException(thrown);
        }
    }

    private java.util.List<FileOperation<?>> generateRandomOps(Random rng, int nOps) {
        java.util.List<FileOperation<?>> ops = new ArrayList<>(nOps);
        RandomOperationGenerator gen = new RandomOperationGenerator(rng);
        for (int i = 0; i < nOps; ++i) {
            ops.add(gen.nextRandomOperation());
        }
        if (!wellDefined(ops)) {
            throw new IllegalStateException("generated not-well-defined ops: " + ops);
        }
        return ops;
    }

    /**
     * Try to find a smaller version of the given <code>list</code> that satisfies the given <code>test</code>.
     * Uses a crude version of the "delta debugging" algorithm:
     * <ul>
     *     <li>Zeller, Andreas. "Yesterday, my program worked. Today, it does not. Why?". ESEC/FSE '99.
     *         doi:<a href="https://doi.org/10.1007%2F3-540-48166-4_16">10.1007/3-540-48166-4_16</a>.</li>
     *     <li><a href="https://en.wikipedia.org/wiki/Delta_debugging">Delta debugging on Wikipedia</a></li>
     * </ul>
     *
     * @param list the list to minimize
     * @param test the test to perform
     * @return a best-effort minimized list
     * @param <T> the element type
     * @throws IOException if some application of the test fails
     */
    private static <T> java.util.List<T> minimize(java.util.List<T> list, IOPredicate<List<T>> test) throws IOException {
        int stride = list.size() / 2;

        while (stride > 0) {
            boolean listModified = false;

            for (int i = 0; i < list.size(); i += stride) {
                int cutStart = i;
                int cutEnd = Math.min(i + stride, list.size());
                List<T> candidate = append(
                        list.subList(0, cutStart),
                        list.subList(cutEnd, list.size()));
                if (test.test(candidate)) {
                    list = candidate;
                    i -= stride;
                    listModified = true;
                }
            }

            if (!listModified) {
                stride /= 2;
            }
        }

        return list;
    }

    /**
     * Helper to append two lists (in TLA+, <code>a \o b</code>).
     *
     * <p>The arguments should be immutable lists.  The returned object may be a new list, it may be <code>==</code> to
     * one of the arguments, or it may be some sort of view backed by one or both of the arguments.
     *
     * @param a the first list
     * @param b the second list
     * @return <code>a \o b</code>
     * @param <T> the element type
     */
    private static <T> List<T> append(List<T> a, List<T> b) {
        if (a.isEmpty()) {
            return b;
        }
        if (b.isEmpty()) {
            return a;
        }
        List<T> result = new ArrayList<>(a.size() + b.size());
        result.addAll(a);
        result.addAll(b);
        return result;
    }

    /**
     * A version of {@link java.util.function.Predicate} that can throw {@link IOException}.
     * @param <T> the argument type
     */
    private interface IOPredicate<T> {
        boolean test(T value) throws IOException;
    }

    /**
     * The result of checking a list of operations.  Because this is an internal helper class, it has public fields
     * rather than getters.
     *
     * <p>Note that although this class stores the list of operations for convenience ({@link #ops}), that field does
     * not play a part in equals/hashCode.
     *
     * @see #checkBufferedRandomAccessFileBehavior(List)
     */
    private static class RunResult {
        /** The executed operations. */
        final java.util.List<FileOperation<?>> ops;

        /**
         * The number of operations that succeeded.  If this is equal to <code>{@link #ops}.length()</code> then all
         * the operations succeeded and this is a successful result.  Otherwise, the operation
         * <code>{@link #ops}.get(successes)</code> was the first one that failed.
         */
        final int successes;

        /**
         * If an operation failed, this is the expected output, otherwise it is null.
         */
        final Object expected;

        /**
         * If an operation failed, this is the actual output, otherwise it is null.
         */
        final Object actual;

        public RunResult(java.util.List<FileOperation<?>> ops, int successes, Object expected, Object actual) {
            this.ops = ops;
            this.successes = successes;
            this.expected = expected;
            this.actual = actual;
        }

        public boolean ok() {
            return Objects.equals(expected, actual);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            RunResult runResult = (RunResult) o;
            return successes == runResult.successes &&
                    Objects.equals(expected, runResult.expected) &&
                    Objects.equals(actual, runResult.actual);
        }

        @Override
        public int hashCode() {
            return Objects.hash(successes, expected, actual);
        }

        @Override
        public String toString() {
            return "RunResult{" +
                    "opsExecuted=" + successes +
                    ", expected=" + expected +
                    ", actual=" + actual +
                    '}';
        }
    }

    /**
     * Execute the given operations against {@link RandomAccessFile} and {@link BufferedRandomAccessFile}.
     *
     * @param ops the operations to execute
     * @return a result that captures any disagreement
     * @throws IOException if an I/O error occurs
     */
    private RunResult checkBufferedRandomAccessFileBehavior(java.util.List<FileOperation<?>> ops) throws IOException {

        final File tmpFile1 = File.createTempFile("tmp", ".bin");
        tmpFile1.deleteOnExit();
        final File tmpFile2 = File.createTempFile("tmp", ".bin");
        tmpFile2.deleteOnExit();

        try (RandomAccessFile f1 = new RandomAccessFile(tmpFile1, "rw");
             BufferedRandomAccessFile f2 = new BufferedRandomAccessFile(tmpFile2, "rw")) {

            for (int i = 0; i < ops.size(); ++i) {
                FileOperation<?> op = ops.get(i);
                Object a = op.execute(f1);
                Object b;
                try {
                    b = op.execute(f2);
                } catch (Exception | AssertionError e) {
                    return new RunResult(ops, i, null, e.getClass());
                }
                if (!Objects.equals(a, b)) {
                    return new RunResult(ops, i, a, b);
                }
            }

        }

        return new RunResult(ops, ops.size(), null, null);
    }

    /**
     * Check if a list of operations is well-defined (i.e. no operation reads arbitrary data).
     *
     * @param ops the operations to check
     * @return whether the list of operations is well-defined
     */
    private boolean wellDefined(java.util.List<FileOperation<?>> ops) {
        AbstractFileState state = new AbstractFileState();
        for (FileOperation<?> op : ops) {
            if (!op.simulateIfWellDefined(state)) {
                return false;
            }
        }
        return true;
    }

    /**
     * A quick test to verify that {@link #wellDefined(List)} behaves correctly.
     */
    @Test
    public void testWellDefined() {
        Assert.assertFalse(wellDefined(Arrays.asList(
                new Read1Operation(), // well-defined (EOF)
                new SeekOperation(12637), // seek far forward
                new Read1Operation(), // well-defined (EOF)
                new Write1Operation((byte)(-39)), // fills the file with mostly arbitrary data, followed by -39
                new SeekOperation(4953), // seek to some arbitrary data

                // This final read observes arbitrary data, so the whole list of operations is not well-defined.
                new ReadArrayOperation(new byte[BOUND], 2121, 4449))));
    }

    /**
     * Helper class that uses {@link AbstractFileState} to generate well-defined lists of operations.
     *
     * @see #nextRandomOperation()
     */
    private static class RandomOperationGenerator {

        private final AbstractFileState state = new AbstractFileState();
        private final Random rng;

        public RandomOperationGenerator(Random rng) {
            this.rng = rng;
        }

        public FileOperation<?> nextRandomOperation() {
            while (true) { // rejection sampling: the loop body can fail to generate a well-defined operation
                FileOperation<?> result = arbitraryRandomOperation();
                if (result.simulateIfWellDefined(state)) {
                    return result;
                }
            }
        }

        private FileOperation<?> arbitraryRandomOperation() {
            switch (rng.nextInt(8)) {
                case 0: {
                    return new Write1Operation((byte) rng.nextInt(0xFF));
                }
                case 1: {
                    byte[] bytes = randomByteArray(rng);
                    int offset = rng.nextInt(bytes.length);
                    int len = rng.nextInt(bytes.length - offset);
                    return new WriteArrayOperation(bytes, offset, len);
                }
                case 2: {
                    return new Read1Operation();
                }
                case 3: {
                    // read() shouldn't depend on the contents of the buffer---but randomizing it helps catch bugs
                    // (if the implementation doesn't correctly set the bytes of the output)
                    byte[] bytes = randomByteArray(rng);
                    int offset = rng.nextInt(bytes.length);
                    int len = rng.nextInt(bytes.length - offset);
                    return new ReadArrayOperation(bytes, offset, len);
                }
                case 4: {
                    int pos = rng.nextInt(BOUND);
                    return new SeekOperation(pos);
                }
                case 5:
                    return new GetFilePointerOperation();
                case 6:
                    return new GetLengthOperation();
                case 7: {
                    int newLength = rng.nextInt(BOUND);
                    return new SetLengthOperation(newLength);
                }
                default:
                    throw new IllegalStateException("Unexpected random number");
            }
        }
    }

    /**
     * Generate a new byte array filled with random data.  The length of the array is randomly chosen from the
     * inclusive-inclusive interval <code>[1, {@link #BOUND}]</code>.
     * @param rng the source of randomness to use
     * @return a new array of random data
     */
    private static byte[] randomByteArray(Random rng) {
        int len = rng.nextInt(BOUND) + 1;
        byte[] result = new byte[len];
        rng.nextBytes(result);
        return result;
    }

    // ==============================================================================================================
    // FileOperation and its implementations live below this line.

    /**
     * An operation that can be performed on a file.
     * @param <T> the type of output the operation produces
     *
     * @see Write1Operation
     * @see WriteArrayOperation
     * @see Read1Operation
     * @see ReadArrayOperation
     * @see SeekOperation
     * @see GetFilePointerOperation
     * @see SetLengthOperation
     * @see GetLengthOperation
     */
    private interface FileOperation<T> {

        /**
         * Execute this operation against a real file.
         *
         * @param file the file
         * @return the output of the operation
         * @throws IOException if an I/O error occurs
         */
        T execute(RandomAccessFile file) throws IOException;

        /**
         * If this operation is well-defined when applied to the given {@link AbstractFileState}, then apply it to
         * the state and return true; otherwise, do nothing and return false.  This method is used by
         * {@link RandomOperationGenerator} to find well-defined lists of operations.
         *
         * @param state the abstract file state to modify
         * @return true if the output of this operation would be well-defined, or false otherwise
         */
        boolean simulateIfWellDefined(AbstractFileState state);
    }

    /** Write one byte of data. */
    private static class Write1Operation implements FileOperation<Void> {
        private final byte x;

        public Write1Operation(byte x) {
            this.x = x;
        }

        @Override
        public Void execute(RandomAccessFile file) throws IOException {
            file.write(x);
            return null;
        }

        @Override
        public boolean simulateIfWellDefined(AbstractFileState state) {
            state.writeBytes(1);
            return true;
        }

        @Override
        public String toString() {
            return "write(" + x + ")";
        }
    }

    /** Write an array of data. */
    private static class WriteArrayOperation implements FileOperation<Void> {
        private final byte[] buffer;
        private final int offset;
        private final int length;

        public WriteArrayOperation(byte[] buffer, int offset, int length) {
            this.buffer = buffer;
            this.offset = offset;
            this.length = length;
        }

        @Override
        public Void execute(RandomAccessFile file) throws IOException {
            file.write(buffer, offset, length);
            return null;
        }

        @Override
        public boolean simulateIfWellDefined(AbstractFileState state) {
            state.writeBytes(length);
            return true;
        }

        @Override
        public String toString() {
            return "write(" + Arrays.toString(buffer) + ", " + offset + ", " + length + ")";
        }
    }

    /** Read one byte of data. */
    private static class Read1Operation implements FileOperation<Integer> {

        @Override
        public Integer execute(RandomAccessFile file) throws IOException {
            return file.read();
        }

        @Override
        public boolean simulateIfWellDefined(AbstractFileState state) {
            if (state.readWouldBeWellDefined(1)) {
                state.readBytes(1);
                return true;
            }
            return false;
        }

        @Override
        public String toString() {
            return "read()";
        }
    }

    /** Read a block of data. */
    private static class ReadArrayOperation implements FileOperation<List<Byte>> {
        private final byte[] buffer;
        private final int offset;
        private final int length;

        public ReadArrayOperation(byte[] buffer, int offset, int length) {
            this.buffer = buffer;
            this.offset = offset;
            this.length = length;
        }

        @Override
        public List<Byte> execute(RandomAccessFile file) throws IOException {
            List<Byte> result = null;

            // Implementations are allowed to read fewer than the requested number of bytes.
            // To smooth out these differences, let's do a full read of exactly the requested
            // length.
            while (result == null || result.size() < length) {
                int nread = file.read(buffer, offset, length - (result == null ? 0 : result.size()));
                if (nread == -1) {
                    break;
                } else {
                    if (result == null) {
                        result = new ArrayList<>(length);
                    }
                    for (int i = 0; i < nread; ++i) {
                        result.add(buffer[offset + i]);
                    }
                }
            }

            return result;
        }

        @Override
        public boolean simulateIfWellDefined(AbstractFileState state) {
            if (state.readWouldBeWellDefined(length)) {
                state.readBytes(length);
                return true;
            }
            return false;
        }

        @Override
        public String toString() {
            return "read(buffer, " + offset + ", " + length + ")";
        }
    }

    /** Seek to a new position the file. */
    private static class SeekOperation implements FileOperation<Void> {
        private final int offset;

        public SeekOperation(int offset) {
            this.offset = offset;
        }

        @Override
        public Void execute(RandomAccessFile file) throws IOException {
            file.seek(offset);
            return null;
        }

        @Override
        public boolean simulateIfWellDefined(AbstractFileState state) {
            state.seek(offset);
            return true;
        }

        @Override
        public String toString() {
            return "seek(" + offset + ")";
        }
    }

    /** Get the file pointer. */
    private static class GetFilePointerOperation implements FileOperation<Long> {
        @Override
        public Long execute(RandomAccessFile file) throws IOException {
            return file.getFilePointer();
        }

        @Override
        public boolean simulateIfWellDefined(AbstractFileState state) {
            return true;
        }

        @Override
        public String toString() {
            return "getFilePointer()";
        }
    }

    /** Get the file length. */
    private static class GetLengthOperation implements FileOperation<Long> {
        @Override
        public Long execute(RandomAccessFile file) throws IOException {
            return file.length();
        }

        @Override
        public boolean simulateIfWellDefined(AbstractFileState state) {
            return true;
        }

        @Override
        public String toString() {
            return "length()";
        }
    }

    /** Set the file length. */
    private static class SetLengthOperation implements FileOperation<Void> {
        private final int newLength;

        public SetLengthOperation(int newLength) {
            this.newLength = newLength;
        }

        @Override
        public Void execute(RandomAccessFile file) throws IOException {
            file.setLength(newLength);
            return null;
        }

        @Override
        public boolean simulateIfWellDefined(AbstractFileState state) {
            state.setLength(newLength);
            return true;
        }

        @Override
        public String toString() {
            return "setLength(" + newLength + ")";
        }
    }

}
