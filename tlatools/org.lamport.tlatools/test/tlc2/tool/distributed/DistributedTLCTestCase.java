/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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
package tlc2.tool.distributed;

import java.security.Permission;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Before;

import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.CommonTestCase;
import tlc2.tool.distributed.fp.DistributedFPSet;

public abstract class DistributedTLCTestCase extends CommonTestCase {
	
	protected final String[] arguments;
	protected final int fpSets;
	
	private NoExitSecurityManager noExit;
	
	public DistributedTLCTestCase(String spec, String path) {
		this(spec, path, new String[] {});
	}
	
	public DistributedTLCTestCase(String spec, String path, String[] args) {
		this(spec, path, args, 0);
	}
	
	public DistributedTLCTestCase(String spec, String path, String[] args, int fpSets) {
		super(new FilteringTestMPRecorder());
		this.arguments = new String[args.length + 1];
		this.arguments[this.arguments.length - 1] = path + spec; // Add path to additional arguments
		System.arraycopy(args, 0, arguments, 0, args.length);
		
		this.fpSets = fpSets;
	}
    
	@Before
	public void setUp() {
		Assume.assumeTrue("DistributedTLCTestCase broken with OffHeapDiskFPSet.", false);
		runDistributed(arguments, true);
	}

	protected int runDistributed(String[] serverArguments, boolean startWorker) {
		// Wait for all launchers to return before making assertions.
		final CountDownLatch latch = new CountDownLatch(1 + (startWorker ? 1 : 0) + (fpSets > 0 ? 1 : 0));
		
		final Thread worker = new Thread(() -> {
			try {
				TLCWorker.main(new String[] { "localhost" });
			} finally {
				latch.countDown();
			}
		}, "Worker");

		// master
		final Thread master = new Thread(new Runnable() {
			public void run() {
				try {
					System.setProperty(TLCServer.class.getName() + ".expectedFPSetCount", Integer.toString(fpSets));
					TLCServer.main(serverArguments);
				} catch (NoExitException e) {
					// The security manager has captured the server's exit status.
				} catch (Exception e) {
					e.printStackTrace();
				} finally {
					latch.countDown();
				}
			}
		}, "Master");

		final SecurityManager previous = System.getSecurityManager();
		Assert.assertFalse("An earlier distributed TLC run did not finish", previous instanceof NoExitSecurityManager);
		noExit = new NoExitSecurityManager(previous, master, latch);
		System.setSecurityManager(noExit);
		MP.setRecorder(recorder);
		if (startWorker) {
			worker.start();
		}
		master.start();

		// FPSet
		if (fpSets > 0) {
			new Thread(new Runnable() {
				public void run() {
					try {
						DistributedFPSet.main(new String[] { "localhost" });
					} catch (Exception e) {
						e.printStackTrace();
					} finally {
						latch.countDown();
					}
				}
			}, "FPSet").start();
		}

		try {
			Assert.assertTrue("Distributed TLC did not finish", latch.await(30, TimeUnit.SECONDS));
		} catch (InterruptedException e) {
			Thread.currentThread().interrupt();
			throw new AssertionError(e);
		} finally {
			master.interrupt();
			worker.interrupt();
		}
		Assert.assertNotNull("TLCServer did not call System.exit", noExit.exitStatus);
		return noExit.exitStatus;
	}
	
	@After
	public void tearDown() {
		if (noExit == null) {
			return;
		}
		if (noExit.launchers.getCount() == 0) {
			System.setSecurityManager(noExit.previous);
			MP.unsubscribeRecorder(recorder);
		} else {
			// A timed-out launcher can still call System.exit. Let Ant finish this fork.
			noExit.runnerMayExit = true;
		}
	}
	
	private static class NoExitSecurityManager extends SecurityManager {
		private final SecurityManager previous;
		private final Thread runner = Thread.currentThread();
		private final Thread master;
		private final CountDownLatch launchers;
		private volatile boolean runnerMayExit;
		private Integer exitStatus;

		NoExitSecurityManager(SecurityManager previous, Thread master, CountDownLatch launchers) {
			this.previous = previous;
			this.master = master;
			this.launchers = launchers;
		}

		/* (non-Javadoc)
		 * @see java.lang.SecurityManager#checkPermission(java.security.Permission)
		 */
		public void checkPermission(Permission perm) {
			// allow anything.
		}

		/* (non-Javadoc)
		 * @see java.lang.SecurityManager#checkPermission(java.security.Permission, java.lang.Object)
		 */
		public void checkPermission(Permission perm, Object context) {
			// allow anything.
		}

		/* (non-Javadoc)
		 * @see java.lang.SecurityManager#checkExit(int)
		 */
		public void checkExit(int status) {
			super.checkExit(status);
			if (runnerMayExit && Thread.currentThread() == runner) {
				if (previous != null) {
					previous.checkExit(status);
				}
				return;
			}
			// An intercepted early exit can be caught by TLCServer.main, but would end the CLI.
			if (Thread.currentThread() == master && exitStatus == null) {
				exitStatus = status;
			}
			throw new NoExitException();
		}
	}
	
	@SuppressWarnings("serial")
	public static class NoExitException extends RuntimeException {
		// Want an easily distinguishable exception.
	}
	
	private static class FilteringTestMPRecorder extends TestMPRecorder {
		/* (non-Javadoc)
		 * @see tlc2.TestMPRecorder#record(int, java.lang.Object[])
		 */
		public synchronized void record(int code, Object... objects) {
			if (EC.GENERAL == code && objects instanceof String[]) {
				// GENERAL errors contain the exceptions thrown because of the
				// intercepted System.exit(int) calls. Remove them so that 
				// tests can check for real EC.GENERAL errors.
				final String msg = ((String[]) objects)[0];
				if (msg.contains(NoExitException.class.getName())) {
					return;
				}
			}
			super.record(code, objects);
		}
	}
}
