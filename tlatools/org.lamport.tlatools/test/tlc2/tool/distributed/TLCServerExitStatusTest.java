package tlc2.tool.distributed;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.net.ServerSocket;
import java.nio.file.Files;
import java.nio.file.Path;
import java.rmi.NoSuchObjectException;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.WorkerException;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.FPSetFactory;
import tlc2.tool.fp.MSBDiskFPSet;
import tlc2.tool.fp.MemFPSet;
import util.Assert.TLCRuntimeException;
import util.ToolIO;
import util.UniqueString;

@RunWith(JUnit4.class)
public class TLCServerExitStatusTest extends DistributedTLCTestCase {
	private static final String SPEC = "ExitStatus";
	private static final String CLOSE_FAILURE = "test fingerprint set failed to close";
	private static final String WORKER_COUNT_PROPERTY = TLCWorker.class.getName() + ".threadCount";
	private static final String REPORT_INTERVAL_PROPERTY = TLCServer.class.getName() + ".report";

	private String workerCount;
	private String reportInterval;

	@Rule
	public final TemporaryFolder tmp = new TemporaryFolder();

	public TLCServerExitStatusTest() {
		super(SPEC, "");
	}

	@Before
	@Override
	public void setUp() {
		workerCount = System.setProperty(WORKER_COUNT_PROPERTY, "1");
		reportInterval = System.setProperty(REPORT_INTERVAL_PROPERTY, "1000");
	}

	@After
	public void restoreProperties() {
		restoreProperty(WORKER_COUNT_PROPERTY, workerCount);
		restoreProperty(REPORT_INTERVAL_PROPERTY, reportInterval);
	}

	@Test
	public void successfulSearch() throws Exception {
		assertEquals(ExitStatus.SUCCESS, checkModel("Safe", false, ExportedMemFPSet.class, true));
		assertTrue(recorder.recorded(EC.TLC_SUCCESS));
		assertTrue(recorder.recordedWithStringValueAt(EC.TLC_STATS, "2", 1));
	}

	@Test
	public void successorInvariantViolation() throws Exception {
		assertEquals(ExitStatus.VIOLATION_SAFETY, checkModel("BadNext", false, ExportedMemFPSet.class, true));
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), List.of("x = 0", "x = 2"));
	}

	@Test
	public void deadlock() throws Exception {
		assertEquals(ExitStatus.VIOLATION_DEADLOCK, checkModel("Safe", true, ExportedMemFPSet.class, true));
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), List.of("x = 0", "x = 1"));
	}

	@Test
	public void workerAssertionFailure() throws Exception {
		assertEquals(ExitStatus.VIOLATION_ASSERT, checkModel("AssertNext", false, ExportedMemFPSet.class, true));
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), List.of("x = 0"));
	}

	@Test
	public void workerExceptionUsesRuntimeCauseCode() {
		final TLCRuntimeException cause = new TLCRuntimeException(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT,
				"successor state is incomplete");
		final WorkerException error = new WorkerException(cause.getMessage(), cause, null, null, true);
		assertEquals(cause.errorCode, error.getErrorCode());
	}

	@Test
	public void initialInvariantViolationWithLocalFPSet() throws Exception {
		assertEquals(ExitStatus.VIOLATION_SAFETY, checkModel("BadInit", true, MSBDiskFPSet.class, false));
		assertTrue(recorder.recordedWithSubStringValue(EC.TLC_INITIAL_STATE, "Invariant Inv is violated"));
		assertTrue(recorder.recordedWithSubStringValue(EC.TLC_INITIAL_STATE, "x = 2"));
	}

	@Test
	public void invalidArguments() {
		final int previousMode = ToolIO.getMode();
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		try {
			assertEquals(ExitStatus.ERROR, runDistributed(new String[] { "-config" }, false));
			final List<String> messages = List.of(ToolIO.getAllMessages());
			assertTrue(messages.toString(), messages.contains("Error: configuration file required."));
			assertFalse(recorder.recorded(EC.TLC_FINISHED));
		} finally {
			ToolIO.reset();
			ToolIO.setMode(previousMode);
		}
	}

	@Test
	public void cleanupFailurePreservesInvariantViolation() throws Exception {
		final int exitStatus = checkModel("BadNext", false, FailingCloseFPSet.class, true);
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), List.of("x = 0", "x = 2"));
		assertTrue(recorder.recordedWithSubStringValue(EC.GENERAL, CLOSE_FAILURE));
		assertEquals(ExitStatus.VIOLATION_SAFETY, exitStatus);
	}

	@Test
	public void cleanupFailureAfterSuccessfulSearch() throws Exception {
		final int exitStatus = checkModel("Safe", false, FailingCloseFPSet.class, true);
		assertTrue(recorder.recorded(EC.TLC_SUCCESS));
		assertTrue(recorder.recordedWithSubStringValue(EC.GENERAL, CLOSE_FAILURE));
		assertEquals(ExitStatus.ERROR, exitStatus);
	}

	private int checkModel(String config, boolean checkDeadlock, Class<? extends FPSet> fpSetImpl, boolean startWorker)
			throws IOException {
		final Path dir = tmp.newFolder().toPath();
		for (String file : List.of(SPEC + ".tla", config + ".cfg")) {
			try (InputStream source = getClass().getResourceAsStream("/TLCServerExitStatus/" + file)) {
				Files.copy(source, dir.resolve(file));
			}
		}
		final List<String> args = new ArrayList<>(List.of("-config", config, "-fpbits", "0"));
		if (!checkDeadlock) {
			args.add("-deadlock");
		}
		args.add(dir.resolve(SPEC).toString());

		final String fpSetProperty = System.setProperty(FPSetFactory.IMPL_PROPERTY, fpSetImpl.getName());
		final String userDir = ToolIO.getUserDir();
		final int port = TLCServer.Port;
		try {
			// TLCServer creates a registry per run, so use a fresh port for each case.
			try (ServerSocket socket = new ServerSocket(0)) {
				TLCServer.Port = socket.getLocalPort();
			}
			ToolIO.setUserDir(dir.toString());
			final int exitStatus = runDistributed(args.toArray(new String[0]), startWorker);
			assertTrue(recorder.recorded(EC.TLC_FINISHED));
			return exitStatus;
		} finally {
			if (startWorker) {
				TLCWorker.shutdown();
				UniqueString.setSource(null);
			}
			TLCServer.Port = port;
			ToolIO.setUserDir(userDir);
			restoreProperty(FPSetFactory.IMPL_PROPERTY, fpSetProperty);
		}
	}

	private static void restoreProperty(String key, String value) {
		if (value == null) {
			System.clearProperty(key);
		} else {
			System.setProperty(key, value);
		}
	}

	public static class ExportedMemFPSet extends MemFPSet {
		public ExportedMemFPSet(FPSetConfiguration config) throws RemoteException {
			super(config);
			// Export the server's local fingerprint set so the loopback worker can use it over RMI.
			UnicastRemoteObject.exportObject(this, 0);
		}

		@Override
		public void close() {
			try {
				UnicastRemoteObject.unexportObject(this, true);
			} catch (NoSuchObjectException e) {
				// Already closed.
			}
		}
	}

	public static final class FailingCloseFPSet extends ExportedMemFPSet {
		public FailingCloseFPSet(FPSetConfiguration config) throws RemoteException {
			super(config);
		}

		@Override
		public void close() {
			super.close();
			throw new UncheckedIOException(new IOException(CLOSE_FAILURE));
		}
	}
}
