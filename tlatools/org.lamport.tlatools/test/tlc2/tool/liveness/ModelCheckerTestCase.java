/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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
package tlc2.tool.liveness;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import org.junit.After;
import org.junit.Before;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.output.MP;
import tlc2.tool.CommonTestCase;
import tlc2.tool.ModelChecker;
import util.FileUtil;
import util.FilenameToStream;
import util.SimpleFilenameToStream;
import util.ToolIO;

public abstract class ModelCheckerTestCase extends CommonTestCase {

	protected String path = "";
	protected String spec;
	protected String[] extraArguments = new String[0];
	protected TLC tlc;
	protected int actualExitStatus = -1;
	protected int expectedExitStatus = ExitStatus.SUCCESS;

	public ModelCheckerTestCase(String spec) {
		this(spec, ExitStatus.SUCCESS);
	}

	public ModelCheckerTestCase(String spec, final int exitStatus) {
		this(spec, "", exitStatus);
	}

	public ModelCheckerTestCase(String spec, String path) {
		this(spec, path, ExitStatus.SUCCESS);
	}
	
	public ModelCheckerTestCase(String spec, String[] extraArguments) {
		this(spec, "", extraArguments, ExitStatus.SUCCESS);
	}
	
	public ModelCheckerTestCase(String spec, String[] extraArguments, final int exitStatus) {
		this(spec, "", extraArguments, exitStatus);
	}
	
	public ModelCheckerTestCase(String spec, String path, String[] extraArguments) {
		this(spec, path, extraArguments, ExitStatus.SUCCESS);
	}
	
	public ModelCheckerTestCase(String spec, String path, String[] extraArguments, final int exitStatus) {
		this(spec, path, exitStatus);
		this.extraArguments  = extraArguments; 
	}
	
	public ModelCheckerTestCase(final String spec, final String path, final int exitStatus) {
		super(new TestMPRecorder());
		this.spec = spec;
		this.path = path;
		this.expectedExitStatus = exitStatus;
	}

	protected void beforeSetUp() {
		// No-op
	}

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	@Before
	public void setUp() {
		beforeSetUp();		
		
		// some tests might want to access the liveness graph after model
		// checking completed. Thus, prevent the liveness graph from being
		// closed too earlier.
		System.setProperty(ModelChecker.class.getName() + ".vetoCleanup", "true");

		try {
			// TEST_MODEL is where TLC should look for user defined .tla files
			ToolIO.setUserDir(BASE_PATH + path);
			
			MP.setRecorder(recorder);
			
			// Increase the liveness checking threshold to prevent liveness
			// checking of an incomplete graph. Most tests check that the 
			// state queue is empty and fail if not. This is only given 
			// when liveness checking is executed when all states have been
			// generated.
			TLCGlobals.livenessThreshold = getLivenessThreshold();
			
			tlc = new TLC();
			tlc.setResolver(getResolver());
			// * We want *no* deadlock checking to find the violation of the
			// temporal formula
			// * We use (unless overridden) a single worker to simplify
			// debugging by taking out threading
			// * MC is the name of the TLA+ specification to be checked (the file
			// is placed in TEST_MODEL
			final List<String> args = new ArrayList<String>(6);
			
			// *Don't* check for deadlocks. All tests are interested in liveness
			// checks which are shielded away by deadlock checking. TLC finds a
			// deadlock (if it exists) before it finds most liveness violations.
			if (!checkDeadLock()) {
				args.add("-deadlock");
			}
			
			if (getNumberOfThreads() == 1 && runWithDebugger()) {
				args.add("-debugger");
				args.add(String.format("nosuspend,port=%s,nohalt", 1025 + new Random().nextInt(64540)));
			}
			
			if (noGenerateSpec()) {
				args.add("-noGenerateSpecTE");
			} else {
				// Make sure the generated spec ends up in a designated location.
				args.add("-generateSpecTE");
				args.add("-teSpecOutDir");
				args.add(TTraceModelCheckerTestCase.getPath(getClass()));
			}
			
			if (noRandomFPandSeed()) {
				args.add("-fp");
				args.add("0");
				// Deterministic simulation (order in which actions are explored).
				args.add("-seed");
				args.add("1");
			}
			
			if (doCoverage()) {
				args.add("-coverage");
				args.add("1");
			}
			
			args.add("-workers");
			args.add(Integer.toString(getNumberOfThreads()));
			
			// Never create checkpoints. They distort performance tests and are
			// of no use anyway.
			args.add("-checkpoint");
			args.add(Integer.toString(doCheckpoint()));
			
			// Always print the state graph in dot file notation.
			if (doDump()) {
				args.add("-dump");
				args.add("dot");
				args.add("${metadir}" + FileUtil.separator + getClass().getCanonicalName() + ".dot");
			}

			
			if (doDumpTrace()) {
				args.add("-dumpTrace");
				args.add("json");
				args.add(TLCGlobals.metaRoot + FileUtil.separator + getClass().getCanonicalName() + ".json");
			}

			args.addAll(Arrays.asList(extraArguments));
			
			args.add(spec);
			tlc.handleParameters(args.toArray(new String[args.size()]));
			
			// Run the ModelChecker
			final int errorCode = tlc.process();
			actualExitStatus = EC.ExitStatus.errorConstantToExitStatus(errorCode);
			
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}

	protected boolean noRandomFPandSeed() {
		return true;
	}

	protected boolean runWithDebugger() {
		return true;
	}

	protected double getLivenessThreshold() {
		return Double.MAX_VALUE;
	}

	protected FilenameToStream getResolver() {
		return new SimpleFilenameToStream();
	}

	protected boolean noGenerateSpec() {
		return false;
	}	

	protected void beforeTearDown() {
		// No-op
	}

	@After
	public void tearDown() {
		beforeTearDown();
		
		assertExitStatus();
	}
	
	protected void assertExitStatus() {
		assertEquals(expectedExitStatus, actualExitStatus);
	}
	
	protected boolean doCoverage() {
		return true;
	}
	
	/**
	 * @return True if TLC is to be called with "-deadlock".
	 */
	protected boolean checkDeadLock() {
		return false;
	}
	
	protected boolean doDump() {
		return true;
	}

	protected boolean doDumpTrace() {
		return true;
	}

	protected int doCheckpoint() {
		return 0;
	}

	/**
	 * @return The number of worker threads TLC should use.
	 */
	protected int getNumberOfThreads() {
		return 1;
	}
	
	protected void setExitStatus(final int exitStatus) {
		this.expectedExitStatus = exitStatus;
	}
	
	/**
	 * E.g. 
	 * ILiveCheck liveCheck = (ILiveCheck) getField(AbstractChecker.class, "liveCheck",
	 * 				getField(TLC.class, "instance", tlc));
	 */
	protected Object getField(Class<?> targetClass, String fieldName, Object instance) {
		try {
			Field field = targetClass.getDeclaredField(fieldName);
			field.setAccessible(true);
			return field.get(instance);
		} catch (NoSuchFieldException e) {
			e.printStackTrace();
		} catch (SecurityException e) {
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			e.printStackTrace();
		}
		return null;
	}
}
