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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import org.junit.After;
import org.junit.Assume;
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
import util.TLAConstants;
import util.ToolIO;

public abstract class ModelCheckerTestCase extends CommonTestCase {

	protected final static String teSpecTimestamp = "2000000000";
	private final static String teSpecSuffix = "_" + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + "_" + teSpecTimestamp;	

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

		// If we are running a TE spec, build the correct module name.
		if (isTESpec()) {
			this.spec = spec + teSpecSuffix + "_" + mungedClassName();
		} else {
			this.spec = spec;
		}
		
		this.path = path;
		this.expectedExitStatus = exitStatus;
	}

	protected void beforeSetUp() {
		// No-op
	}

	// Use it to indicate that the test will read the generated
	// TE spec file instead of running the original spec.
	protected boolean isTESpec() {
		return false;
	}

	private String originalTESpecPath() {
		return System.getProperty("user.dir") + File.separator + this.spec;
	}

	private String clonedTESpecPath() {
		return BASE_PATH + this.path + File.separator + this.spec;
	}	

	private void checkTESpecAssumption() {
		Path sourcePath = Paths.get(originalTESpecPath() + TLAConstants.Files.TLA_EXTENSION);
		Path destPath = Paths.get(clonedTESpecPath() + TLAConstants.Files.TLA_EXTENSION);

		// First check if the file is already moved to the correct path.
		// If it doesn't, check with `Assume` that the generated file exists
		// in the original path.
		if (destPath.toFile().isFile()) {
			return;
		} else {
			Assume.assumeTrue("No TE spec was generated, please run test with original spec", sourcePath.toFile().isFile());
		}
	}

	private void moveTESpecFiles() {
		// Move generated files from their original location (user.dir) to the same folder
		// as the original TLA spec so we can run the generated TE spec.
		// First the TLA file.
		Path sourcePath = Paths.get(originalTESpecPath() + TLAConstants.Files.TLA_EXTENSION);
		Path destPath = Paths.get(clonedTESpecPath() + TLAConstants.Files.TLA_EXTENSION);

		// Check if the file is already moved to the correct path.
		if (destPath.toFile().isFile()) {
			return;
		}
		
		try {
			Files.move(sourcePath, destPath, StandardCopyOption.REPLACE_EXISTING);
		} catch (IOException exception) {
			fail(exception.toString());
		}

		// Then we move the config file.
		sourcePath = Paths.get(originalTESpecPath() + TLAConstants.Files.CONFIG_EXTENSION);
		destPath = Paths.get(clonedTESpecPath() + TLAConstants.Files.CONFIG_EXTENSION);
		try {
			Files.move(sourcePath, destPath, StandardCopyOption.REPLACE_EXISTING);
		} catch (IOException exception) {
			fail(exception.toString());
		}
	}

	private void removeGeneratedFiles(String originalPath, String clonedPath) {
        // Remove generated files, if any.
        new File(originalPath + TLAConstants.Files.TLA_EXTENSION).delete();
        new File(originalPath + TLAConstants.Files.CONFIG_EXTENSION).delete();
        new File(clonedPath + TLAConstants.Files.TLA_EXTENSION).delete();
        new File(clonedPath + TLAConstants.Files.CONFIG_EXTENSION).delete();
    }

	private String mungedClassName() {
		return this.getClass().getName().replaceAll("\\.", "_");
	}

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	@Before
	public void setUp() {
		if (!isTESpec()) {
			// Remove any generated file before running a original spec.
			removeGeneratedFiles(
				originalTESpecPath() + teSpecSuffix + "_" + mungedClassName() + "_TTraceTest", 
				clonedTESpecPath() + teSpecSuffix + "_" + mungedClassName() + "_TTraceTest");
		} else {
			checkTESpecAssumption();
			
			// If it's a TE spec run, move TE spec files so they are in the
			// correct path.
			moveTESpecFiles();			
		}

		beforeSetUp();		
		
		// some tests might want to access the liveness graph after model
		// checking completed. Thus, prevent the liveness graph from being
		// closed too earlier.
		System.setProperty(ModelChecker.class.getName() + ".vetoCleanup", "true");

		// Timestamps for traces generated by the trace expression writer (trace explorer)
		// will have the same suffix so it's easy to know beforehand the name of the
		// file.
		System.setProperty("TLC_TRACE_EXPLORER_TIMESTAMP", teSpecTimestamp + "_" + mungedClassName() + "_TTraceTest");

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
		// Also check assumption in `@After` as it's not skipped
		// if assumption in `@Before` fails.
		if (isTESpec()) {
			checkTESpecAssumption();
		}		
		
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
