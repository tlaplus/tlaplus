/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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

import org.junit.Assume;
import org.junit.Before;
import tlc2.tool.ModelCheckerTestCase;
import util.FilenameToStream;
import util.SimpleFilenameToStream;
import util.TLAConstants;

import java.io.File;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.stream.Stream;

public abstract class TTraceModelCheckerTestCase extends ModelCheckerTestCase {

    // Make the generated stuff go into the target/ folder of the org.lamport.tlatools folder.
    private static final String GEN_SPEC_NAME = "GeneratedTESpecs";

    protected static final String GEN_SPEC_PAth = TARGET_DIR + File.separator + GEN_SPEC_NAME;
    private final Class<?> clazz;
    // Path to the original spec (not the trace spec)
    private final String specPath;


    public TTraceModelCheckerTestCase(final Class<?> clazz, final String path, final int exitStatus) {
        super(getSpecFileName(clazz), path, new String[]{"-config", getTESpecPathForLoading(clazz)}, exitStatus);
        this.clazz = clazz;
        this.specPath = GEN_SPEC_PAth;
    }

    public TTraceModelCheckerTestCase(final Class<?> clazz, final int exitStatus) {
        super(getSpecFileName(clazz), "", new String[]{"-config", getTESpecPathForLoading(clazz)}, exitStatus);
        this.clazz = clazz;
        this.specPath = GEN_SPEC_PAth;
    }
    public TTraceModelCheckerTestCase(final Class<?> clazz, final String[] extraArgs, final int exitStatus) {
        super(getSpecFileName(clazz), "", Stream
                .concat(Arrays.stream(new String[]{"-config", getTESpecPathForLoading(clazz)}), Arrays.stream(extraArgs))
                .toArray(String[]::new), exitStatus);
        this.clazz = clazz;
        this.specPath = GEN_SPEC_PAth;
    }

    public static String getTESpecPath(final Class<?> clazz) {
        return GEN_SPEC_PAth + File.separator + getSpecFileName(clazz);
    }

    public static String getTESpecPathForLoading(final Class<?> clazz) {
        return FileSystems.getDefault().getPath(getTESpecPath(clazz)).normalize().toAbsolutePath().toString();
    }

    private static String getSpecFileName(final Class<?> clazz) {
        return clazz.getSimpleName() + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME
                + TLAConstants.Files.TLA_EXTENSION;
    }

    public String getModuleName() {
        return clazz.getSimpleName() + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME;
    }

    @Override
    @Before
    public void setUp() {
        beforeSetUp();

        //TODO Assume that the generated file exist.
        final Path sourcePath = Paths
                .get(specPath + File.separator + spec);
        Assume.assumeTrue("No TE spec was generated, please run test with original spec", sourcePath.toFile().isFile());

        super.setUp();
    }

    @Override
    protected boolean noGenerateSpec() {
        return true;
    }

    @Override
    protected boolean doCoverage() {
        // A trace evaluation spec (TESpec) usually shows many warnings related to
        // coverage. Until those warnings are addressed or silenced in the
        // CostModelCreator/OpApplNodeWrapper, let's not report coverage for trace
        // evaluation specs.
        return false;
    }

    @Override
    protected FilenameToStream getResolver() {
        return new SimpleFilenameToStream(new String[]{specPath});
    }
}
