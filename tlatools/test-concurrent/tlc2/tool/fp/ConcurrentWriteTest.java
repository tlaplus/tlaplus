// Copyright (c) 2016 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.util.ArrayList;
import java.util.Collection;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import org.junit.Test;

import tlc2.util.BufferedRandomAccessFile;

public class ConcurrentWriteTest {
	@Test
	public void test() throws IOException {
		final File tempFile = File.createTempFile("ConcurrentWriteTest_test", ".bin");
		
		RandomAccessFile tmpRAF0 = new BufferedRandomAccessFile(tempFile, "rw");
		tmpRAF0.setLength(4000L * Long.BYTES);
		for(long i = 0L; i < 1000; i++) {
			tmpRAF0.writeLong(i);
		}
		
		for(long i = 1000L; i < 2000; i++) {
			tmpRAF0.writeLong(i);
		}
		
		for(long i = 2000L; i < 3000; i++) {
			tmpRAF0.writeLong(i);
		}
		
		for(long i = 3000L; i < 4000; i++) {
			tmpRAF0.writeLong(i);
		}
		
		tmpRAF0.close();
		
		final RandomAccessFile tmpRAF = new BufferedRandomAccessFile(tempFile, "r");
		for(long i = 0L; i < 4000; i++) {
			assertEquals(i, tmpRAF.readLong());
		}
		tmpRAF.close();
	}

	@Test
	public void test1() throws IOException {
		final File tempFile = File.createTempFile("ConcurrentWriteTest_test1", ".bin");
		final long limit = 4000000L;
		final long partition = limit / 4L;
		
		final RandomAccessFile tmpRAF0 = new BufferedRandomAccessFile(tempFile, "rw");
		tmpRAF0.setLength(limit * Long.BYTES);
		for(long i = 0L; i < partition; i++) {
			tmpRAF0.writeLong(i);
		}
		
		final RandomAccessFile tmpRAF1 = new BufferedRandomAccessFile(tempFile, "rw");
		tmpRAF1.setLength(limit * Long.BYTES);
		tmpRAF1.seek(partition * Long.BYTES);
		for (long i = partition; i < (2L * partition); i++) {
			tmpRAF1.writeLong(i);
		}

		final RandomAccessFile tmpRAF2 = new BufferedRandomAccessFile(tempFile, "rw");
		tmpRAF2.setLength(limit * Long.BYTES);
		tmpRAF2.seek((2L * partition) * Long.BYTES);
		for (long i = (2L * partition); i < (3L * partition); i++) {
			tmpRAF2.writeLong(i);
		}

		final RandomAccessFile tmpRAF3 = new BufferedRandomAccessFile(tempFile, "rw");
		tmpRAF3.setLength(limit * Long.BYTES);
		tmpRAF3.seek((3L * partition) * Long.BYTES);
		for (long i = (3L * partition); i < (4L * partition); i++) {
			tmpRAF3.writeLong(i);
		}
		
		tmpRAF0.close();
		tmpRAF1.close();
		tmpRAF2.close();
		tmpRAF3.close();
		
		final RandomAccessFile tmpRAF = new BufferedRandomAccessFile(tempFile, "r");
		for(long i = 0L; i < limit; i++) {
			assertEquals(i, tmpRAF.readLong());
		}
		tmpRAF.close();
	}
	
	@Test
	public void test2() throws IOException {
		final File tempFile = File.createTempFile("ConcurrentWriteTest_test2", ".bin");
		final long limit = 4000000L;
		final long partition = limit / 4L;
		
		final RandomAccessFile tmpRAF0 = new BufferedRandomAccessFile(tempFile, "rw");
		tmpRAF0.setLength(limit * Long.BYTES);

		final RandomAccessFile tmpRAF1 = new BufferedRandomAccessFile(tempFile, "rw");
		tmpRAF1.setLength(limit * Long.BYTES);
		tmpRAF1.seek(partition * Long.BYTES);

		final RandomAccessFile tmpRAF2 = new BufferedRandomAccessFile(tempFile, "rw");
		tmpRAF2.setLength(limit * Long.BYTES);
		tmpRAF2.seek((2L * partition) * Long.BYTES);

		final RandomAccessFile tmpRAF3 = new BufferedRandomAccessFile(tempFile, "rw");
		tmpRAF3.setLength(limit * Long.BYTES);
		tmpRAF3.seek((3L * partition) * Long.BYTES);

		for(long i = 0L; i < (1L * partition); i++) {
			tmpRAF0.writeLong(i);
		}
		
		for(long i = (1L * partition); i < (2L * partition); i++) {
			tmpRAF1.writeLong(i);
		}
		
		for(long i = (2L * partition); i < (3L * partition); i++) {
			tmpRAF2.writeLong(i);
		}
		
		for(long i = (3L * partition); i < (4L * partition); i++) {
			tmpRAF3.writeLong(i);
		}
		
		tmpRAF0.close();
		tmpRAF1.close();
		tmpRAF2.close();
		tmpRAF3.close();
		
		final RandomAccessFile tmpRAF = new BufferedRandomAccessFile(tempFile, "r");
		for(long i = 0L; i < limit; i++) {
			assertEquals(i, tmpRAF.readLong());
		}
		tmpRAF.close();
	}
	
	@Test
	public void test3() throws IOException, InterruptedException {
		final File tempFile = File.createTempFile("ConcurrentWriteTest_test3", ".bin");
		final long limit = 400000000L;
		final long writers = 8L;
		final long partition = limit / writers;

		final Collection<Callable<Void>> tasks = new ArrayList<Callable<Void>>((int) writers);
		for (long i = 0L; i < writers; i++) {
			final long id = i;
			tasks.add(new Callable<Void>() {
				public Void call() throws Exception {
					final RandomAccessFile tmpRAF = new BufferedRandomAccessFile(tempFile, "rw");
					tmpRAF.setLength(limit * Long.BYTES);
					tmpRAF.seek(id * partition * Long.BYTES);

					for (long j = (id * partition); j < ((id + 1) * partition); j++) {
						tmpRAF.writeLong(j);
					}

					tmpRAF.close();
					return null;
				}
			});
		}
		
		final ExecutorService executorService = Executors.newFixedThreadPool((int) writers);
		executorService.invokeAll(tasks);
		executorService.shutdown();

		final RandomAccessFile tmpRAF = new BufferedRandomAccessFile(tempFile, "r");
		for(long i = 0L; i < limit; i++) {
			assertEquals(i, tmpRAF.readLong());
		}
		tmpRAF.close();
	}

	@Test
	public void test4() throws IOException, InterruptedException {
		final File tempFile = File.createTempFile("ConcurrentWriteTest_test4", ".bin");
		final long limit = 400000000L;
		final long writers = 8L;
		final long partition = limit / writers;
		final RandomAccessFile tmpRAF = new BufferedRandomAccessFile(tempFile, "rw");
		tmpRAF.setLength(limit * Long.BYTES);
		final FileChannel channel = tmpRAF.getChannel();

		final Collection<Callable<Void>> tasks = new ArrayList<Callable<Void>>((int) writers);
		for (long i = 0L; i < writers; i++) {
			final long id = i;
			tasks.add(new Callable<Void>() {
				public Void call() throws Exception {
					long position = id * partition * Long.BYTES;
					final ByteBuffer buffer = ByteBuffer.allocate(Long.BYTES/* * 1024*/);
					for (long j = (id * partition); j < ((id + 1) * partition); j++/*j+=1024L*/) {
//						for (int i = 0; i < buffer.capacity(); i++) {
							buffer.putLong(j/* + i*/);
							buffer.flip();
//						}
						channel.write(buffer, position + (j * Long.BYTES));
						buffer.clear();
					}
					channel.force(false);
					return null;
				}
			});
		};
		
		final ExecutorService executorService = Executors.newFixedThreadPool((int) writers);
		executorService.invokeAll(tasks);
		executorService.shutdown();
		
		tmpRAF.close();	

		final BufferedRandomAccessFile checkRaf = new BufferedRandomAccessFile(tempFile, "r");
		for(long i = 0L; i < limit; i++) {
			assertEquals(i, checkRaf.readLong());
		}
		checkRaf.close();
	}
}
