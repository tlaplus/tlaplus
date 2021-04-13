/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
package tlc2;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import com.google.gson.Gson;

import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TLAConstants;

// TraceExpressionSpecTest is already taken, this is different because it runs
// the spec using `TLCRunner` AND the TE spec.
public abstract class TraceExpressionTestCase extends ModelCheckerTestCase {

    public final String originalSpec;
    public final String TESpec;
    public final Map<String, Object> options;

    public TraceExpressionTestCase(String spec, String path, final int exitStatus) {
		this(spec, path, new String[] {}, exitStatus, new HashMap<String, Object>());
	}

    public TraceExpressionTestCase(String spec, String path, String[] extraArguments, final int exitStatus) {
		this(spec, path, extraArguments, exitStatus, new HashMap<String, Object>());
	}

    public TraceExpressionTestCase(String spec, String path, String[] extraArguments, final int exitStatus, Map<String, Object> options) {
		super(
            spec + "_" + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + "_2000000000",
            path,
            extraArguments,
            exitStatus
        );
        this.originalSpec = spec;
        this.TESpec = spec + "_" + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + "_2000000000";
        this.options = options;

        List<String> defaultArguments = new ArrayList<String>();
        if (!(this.options.containsKey("removeDeadlockConfig") && (Boolean)this.options.get("removeDeadlockConfig") == true)) {
            defaultArguments.add("-deadlock");
        }
        if (!(this.options.containsKey("noRandomFPandSeed") && (Boolean)this.options.get("noRandomFPandSeed") == false)) {
            defaultArguments.add("-fp");
            defaultArguments.add("0");
            // Deterministic simulation (order in which actions are explored).
            defaultArguments.add("-seed");
            defaultArguments.add("1");
        }
        this.extraArguments = Stream.of(this.extraArguments, defaultArguments.toArray()).flatMap(Stream::of).toArray(String[]::new);
	}

    @Override
    protected void beforeSetUp() {
        this.removeGeneratedFiles();
        final File outFile = new File(BASE_PATH, "test" + TLAConstants.Files.OUTPUT_EXTENSION);

        List<String> runnerArgs = new ArrayList<>(Arrays.asList(new String[] {BASE_PATH + this.path + File.separator + this.originalSpec}));
        runnerArgs.addAll(Arrays.asList(this.extraArguments));

        final TLCRunner tlcRunner = new TLCRunner(runnerArgs, outFile);
        TLCRunner.JVM_ARGUMENTS.add("-DTLC_TRACE_EXPLORER_TIMESTAMP=2000000000");

        if (this.options.containsKey("expectedJsonPath")) {
            TLCRunner.JVM_ARGUMENTS.add("-DTLC_TRACE_EXPLORER_JSON_UNCOMMENTED=true");
        }

        if ((this.options.containsKey("LIVENESS_TESTING_IMPLEMENTATION") && (Boolean)this.options.get("LIVENESS_TESTING_IMPLEMENTATION") == true)) {
            TLCRunner.JVM_ARGUMENTS.add("-Dtlc2.tool.liveness.ILiveCheck.testing=true");
        }

        try {
            final int errorCode = tlcRunner.run();            
            if(errorCode != this.expectedExitStatus) {
                fail(String.format("The output of the original spec TLC run was not the expected exit status, it was %d instead.", errorCode));
            }
        } catch (IOException exception) {
            fail(exception.getMessage());
        }
    }

    private void testJson() {
        try {
            Gson gson = new Gson();
            Object expectedJson = gson.fromJson(new FileReader(BASE_PATH + "GeneratedTESpecs" + File.separator + "EWD840_TTrace_JsonOutput.json"), Object.class);
            Object jsonObject = gson.fromJson(new FileReader(System.getProperty("user.dir") + File.separator + this.TESpec + ".json"), Object.class);
            assertTrue(expectedJson.equals(jsonObject));
        } catch (FileNotFoundException exception) {
            fail(exception.getMessage());
        }
    }

    private void removeGeneratedFiles() {
        // Remove generated files, if any.
        new File(BASE_PATH + this.path + File.separator + this.TESpec + ".tla").delete();
        new File(BASE_PATH + this.path + File.separator + this.TESpec + ".cfg").delete();
        new File(System.getProperty("user.dir") + File.separator + this.TESpec + ".json").delete();
    }

    @Override
    protected void beforeTearDown() {
        if (this.options.containsKey("expectedJsonPath")) {
            testJson();
        }
        //this.removeGeneratedFiles();
    }

    @Override
	protected boolean doCoverage() {
		// Do not do coverage or the code to avoid a bug,
		// see https://github.com/tlaplus/tlaplus/pull/588#issuecomment-817371371.
		return false;
	}
}
