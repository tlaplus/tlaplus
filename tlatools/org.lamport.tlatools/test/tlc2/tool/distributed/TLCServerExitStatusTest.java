// Copyright (c) 2026 TLA+ contributors. All rights reserved.
// SPDX-License-Identifier: MIT
package tlc2.tool.distributed;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.ServerSocket;
import java.nio.file.Files;
import java.nio.file.Path;
import java.rmi.ConnectException;
import java.rmi.NotBoundException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.rmi.server.UnicastRemoteObject;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.distributed.fp.FPSetRMI;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.MSBDiskFPSet;

public class TLCServerExitStatusTest {
	private static final String HOST = "127.0.0.1";
	private static final String SPEC = "ExitStatus";
	private static final int TIMEOUT_SECONDS = 30;

	@Rule
	public final TemporaryFolder tmp = new TemporaryFolder();

	@Test
	public void successfulSearch() throws Exception {
		runDistributed("Safe", false, ExitStatus.SUCCESS, "No error has been found", "2 distinct states found");
	}

	@Test
	public void successorInvariantViolation() throws Exception {
		runDistributed("BadNext", false, ExitStatus.VIOLATION_SAFETY, "x = 0", "x = 2");
	}

	@Test
	public void deadlock() throws Exception {
		runDistributed("Safe", true, ExitStatus.VIOLATION_DEADLOCK, "x = 0", "x = 1");
	}

	@Test
	public void initialInvariantViolationWithLocalFPSet() throws Exception {
		final Path dir = model("BadInit");
		final Process server = start(dir, "server", freePort(), 0, TLCServer.class, "-config", "BadInit", SPEC);
		try {
			assertResult(dir, server, ExitStatus.VIOLATION_SAFETY, "Invariant Inv is violated", "x = 2", "Finished");
		} finally {
			stop(server);
		}
	}

	@Test
	public void invalidArguments() throws Exception {
		final Path dir = tmp.getRoot().toPath();
		final Process server = start(dir, "server", freePort(), 0, TLCServer.class, "-config");
		try {
			assertResult(dir, server, ExitStatus.ERROR, "configuration file required");
		} finally {
			stop(server);
		}
	}

	private void runDistributed(String config, boolean checkDeadlock, int status, String... messages)
			throws Exception {
		final Path dir = model(config);
		final int port = freePort();
		final List<String> args = new ArrayList<>(List.of("-config", config));
		if (!checkDeadlock) {
			args.add("-deadlock");
		}
		args.add(SPEC);

		// The CLI status belongs to the server JVM. Use the real worker CLI and a
		// single loopback FPSet to exercise the same RMI path as a distributed run.
		final Process server = start(dir, "server", port, 1, TLCServer.class, args.toArray(new String[0]));
		Process worker = null;
		FPSet fpSet = null;
		try {
			final TLCServerRMI master = awaitServer(dir, server, port);
			fpSet = new TLCServerTestCase.DummyFPSet(new FPSetConfiguration()).init(1, dir.toString(), "fpset");
			final FPSetRMI stub = (FPSetRMI) UnicastRemoteObject.exportObject(fpSet, 0);
			master.registerFPSet(stub, HOST);
			worker = start(dir, "worker", port, 0, TLCWorker.class, HOST);
			final String[] completedMessages = Arrays.copyOf(messages, messages.length + 1);
			completedMessages[messages.length] = "Finished";
			assertResult(dir, server, status, completedMessages);
		} finally {
			stop(worker);
			stop(server);
			if (fpSet != null) {
				UnicastRemoteObject.unexportObject(fpSet, true);
				fpSet.close();
			}
		}
	}

	private Path model(String config) throws IOException {
		final Path dir = tmp.newFolder().toPath();
		for (String file : List.of(SPEC + ".tla", config + ".cfg")) {
			try (InputStream source = getClass().getResourceAsStream("/TLCServerExitStatus/" + file)) {
				Files.copy(source, dir.resolve(file));
			}
		}
		return dir;
	}

	private static int freePort() throws IOException {
		try (ServerSocket socket = new ServerSocket(0)) {
			return socket.getLocalPort();
		}
	}

	private static Process start(Path dir, String name, int port, int fpSets, Class<?> main, String... args) throws IOException {
		final String java = Path.of(System.getProperty("java.home"), "bin", "java").toString();
		final String[] classPath = System.getProperty("java.class.path").split(File.pathSeparator);
		for (int i = 0; i < classPath.length; i++) {
			classPath[i] = Path.of(classPath[i]).toAbsolutePath().toString();
		}
		final List<String> command = new ArrayList<>(List.of(java, "-ea", "-Xmx128m",
				"-Djava.rmi.server.hostname=" + HOST, "-Dtlc2.tool.distributed.TLCServer.port=" + port,
				"-Dtlc2.tool.distributed.TLCServer.report=1000", "-Dtlc2.tool.distributed.TLCWorker.threadCount=1",
				"-Dtlc2.tool.distributed.TLCServer.expectedFPSetCount=" + fpSets,
				"-Dtlc2.tool.fp.FPSet.impl=" + MSBDiskFPSet.class.getName(),
				"--add-exports=java.rmi/sun.rmi.server=ALL-UNNAMED",
				"--add-exports=java.rmi/sun.rmi.transport=ALL-UNNAMED",
				"-cp", String.join(File.pathSeparator, classPath), main.getName()));
		command.addAll(Arrays.asList(args));
		return new ProcessBuilder(command).directory(dir.toFile()).redirectErrorStream(true)
				.redirectOutput(dir.resolve(name + ".log").toFile()).start();
	}

	private static TLCServerRMI awaitServer(Path dir, Process server, int port) throws Exception {
		final Registry registry = LocateRegistry.getRegistry(HOST, port);
		final long start = System.nanoTime();
		while (server.isAlive() && System.nanoTime() - start < TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS)) {
			try {
				return (TLCServerRMI) registry.lookup(TLCServer.SERVER_NAME);
			} catch (ConnectException | NotBoundException e) {
				Thread.sleep(50);
			}
		}
		throw new AssertionError("Server did not register:\n" + output(dir, "server"));
	}

	private static void assertResult(Path dir, Process server, int status, String... messages) throws Exception {
		final boolean finished = server.waitFor(TIMEOUT_SECONDS, TimeUnit.SECONDS);
		final String log = output(dir, "server");
		assertTrue("Server did not exit:\n" + log + output(dir, "worker"), finished);
		for (String message : messages) {
			assertTrue(log, log.contains(message));
		}
		assertEquals(log, status, server.exitValue());
	}

	private static String output(Path dir, String name) throws IOException {
		final Path log = dir.resolve(name + ".log");
		return Files.exists(log) ? Files.readString(log) : "";
	}

	private static void stop(Process process) throws InterruptedException {
		if (process != null && process.isAlive()) {
			process.destroyForcibly();
			process.waitFor(TIMEOUT_SECONDS, TimeUnit.SECONDS);
		}
	}
}
