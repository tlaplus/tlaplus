package tlc2.tool.queue;

import static org.junit.Assert.assertEquals;

import java.io.IOException;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import tlc2.tool.TLCState;

public class DiskStateQueueCheckpointTest {

	@Rule
	public final TemporaryFolder temporaryFolder = new TemporaryFolder();

	@Test
	public void testRecoverIntLength() throws IOException {
		assertRecoversQueueLength(Integer.MAX_VALUE);
	}

	@Test
	public void testRecoverLongLength() throws IOException {
		assertRecoversQueueLength(Integer.MAX_VALUE + 1L);
	}

	private void assertRecoversQueueLength(long length) throws IOException {
		final DiskStateQueue queue = new DiskStateQueue(temporaryFolder.newFolder().getAbsolutePath());
		final TLCState originalEmpty = TLCState.Empty;
		try {
			final TLCState state = new DummyTLCState();
			state.uid = 42;
			queue.enqueue(state);
			// Exercise the count encoding without allocating billions of states.
			queue.len = length;
			queue.beginChkpt();
			queue.commitChkpt();

			queue.len = 0;
			state.uid = 0;
			queue.recover();

			assertEquals(length, queue.size());
			assertEquals(42, queue.dequeue().uid);
		} finally {
			queue.finishAll();
			TLCState.Empty = originalEmpty;
		}
	}
}
