package tlc2.tool.queue;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.lang.reflect.Field;
import java.nio.file.Files;

import org.junit.After;
import org.junit.Test;

public class DiskPoolWriterTest {

	private static final long TIMEOUT_MILLIS = 5000L;

	private File diskDirectory;
	private IStateQueue queue;

	@After
	public void tearDown() {
		if (this.queue != null) {
			this.queue.finishAll();
		}
		if (this.diskDirectory != null) {
			final File[] files = this.diskDirectory.listFiles();
			if (files != null) {
				for (File file : files) {
					file.delete();
				}
			}
			this.diskDirectory.delete();
		}
	}

	@Test
	public void testStatePoolWriterIgnoresEmptyWakeAndStopsOnFinish() throws Exception {
		this.diskDirectory = Files.createTempDirectory("DiskPoolWriterTest").toFile();
		final DiskStateQueue stateQueue = new DiskStateQueue(this.diskDirectory.getAbsolutePath());
		this.queue = stateQueue;

		assertIgnoresEmptyWake(stateQueue.writer);
		assertStopsOnFinish(stateQueue.writer);
	}

	@Test
	public void testByteArrayPoolWriterIgnoresEmptyWakeAndStopsOnFinish() throws Exception {
		this.diskDirectory = Files.createTempDirectory("DiskPoolWriterTest").toFile();
		final DiskByteArrayQueue byteArrayQueue = new DiskByteArrayQueue(this.diskDirectory.getAbsolutePath());
		this.queue = byteArrayQueue;

		final Field writerField = DiskByteArrayQueue.class.getDeclaredField("writer");
		writerField.setAccessible(true);
		final Thread writer = (Thread) writerField.get(byteArrayQueue);

		assertIgnoresEmptyWake(writer);
		assertStopsOnFinish(writer);
	}

	private void assertIgnoresEmptyWake(Thread writer) throws InterruptedException {
		awaitState(writer, Thread.State.WAITING);
		synchronized (writer) {
			writer.notifyAll();
			final long deadline = System.currentTimeMillis() + TIMEOUT_MILLIS;
			while (writer.getState() == Thread.State.WAITING && System.currentTimeMillis() < deadline) {
				Thread.sleep(10L);
			}
			assertTrue("writer did not observe the notification", writer.getState() != Thread.State.WAITING);
		}
		awaitState(writer, Thread.State.WAITING);
		assertTrue("writer exited after an empty wake", writer.isAlive());
	}

	private void assertStopsOnFinish(Thread writer) throws InterruptedException {
		this.queue.finishAll();
		writer.join(TIMEOUT_MILLIS);
		assertFalse("writer did not stop when the queue finished", writer.isAlive());
	}

	private static void awaitState(Thread thread, Thread.State expected) throws InterruptedException {
		final long deadline = System.currentTimeMillis() + TIMEOUT_MILLIS;
		while (thread.isAlive() && thread.getState() != expected && System.currentTimeMillis() < deadline) {
			Thread.sleep(10L);
		}
		assertTrue("writer exited while waiting for state " + expected, thread.isAlive());
		assertEquals("writer did not enter state " + expected, expected, thread.getState());
	}
}
