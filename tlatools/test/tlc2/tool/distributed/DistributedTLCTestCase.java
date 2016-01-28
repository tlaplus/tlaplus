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

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;

import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.CommonTestCase;
import tlc2.tool.distributed.fp.DistributedFPSet;

public abstract class DistributedTLCTestCase extends CommonTestCase {
	
	protected final String[] arguments;
	protected final int fpSets;
	
	private SecurityManager securityManager;
	
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
		// Remember the original security manager and have it replaced with this
		// custom one. Contrary to the original, this security manager
		// intercepts calls to System.exit(int) and throws an exception instead
		// of terminating the VM. This is done to prevent TLCWorker/TLCServer/...
		// from terminating the JUnit test itself. To allow the JUnit test to
		// later terminate the VM after test completion, we have to reinstate
		// the original security manager again (see tearDown).
		securityManager = System.getSecurityManager();
		System.setSecurityManager(new NoExitSecurityManager());

		MP.setRecorder(recorder);
		
		// Wait for all processes to terminate before the setup itself is done
		final CountDownLatch latch = new CountDownLatch(fpSets + 2);
		
		// Workers
		new Thread(new Runnable() {
			public void run() {
				try {
					TLCWorker.main(new String[] { "localhost" });
				} catch (Exception e) {
					e.printStackTrace();
				} finally {
					latch.countDown();
				}
			}
		}, "Worker").start();

		// master
		new Thread(new Runnable() {
			public void run() {
				try {
					System.setProperty(TLCServer.class.getName() + ".expectedFPSetCount", Integer.toString(fpSets));
					TLCServer.main(arguments);
				} catch (Exception e) {
					e.printStackTrace();
				} finally {
					latch.countDown();
				}
			}
		}, "Master").start();

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
			latch.await();
		} catch (InterruptedException e) {
			Assert.fail();
		}
	}
	
	@After
	public void tearDown() {
		System.setSecurityManager(securityManager);
	}
	
	private static class NoExitSecurityManager extends SecurityManager {
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
		public void record(int code, Object... objects) {
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
