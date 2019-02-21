/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
package tlc2.util;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import org.openjdk.jmh.infra.BenchmarkParams;
import org.openjdk.jmh.profile.ExternalProfiler;
import org.openjdk.jmh.results.BenchmarkResult;
import org.openjdk.jmh.results.Result;

public class FlightRecorderProfiler implements ExternalProfiler {

	// Inspired by https://github.com/nicoulaj/jmh-utils
	
	/* (non-Javadoc)
	 * @see org.openjdk.jmh.profile.Profiler#getDescription()
	 */
	@Override
	public String getDescription() {
		return FlightRecorderProfiler.class.getSimpleName();
	}

	/* (non-Javadoc)
	 * @see org.openjdk.jmh.profile.ExternalProfiler#addJVMInvokeOptions(org.openjdk.jmh.infra.BenchmarkParams)
	 */
	@Override
	public Collection<String> addJVMInvokeOptions(BenchmarkParams arg0) {
		return new ArrayList<String>();
	}

	/* (non-Javadoc)
	 * @see org.openjdk.jmh.profile.ExternalProfiler#allowPrintErr()
	 */
	@Override
	public boolean allowPrintErr() {
		return true;
	}

	/* (non-Javadoc)
	 * @see org.openjdk.jmh.profile.ExternalProfiler#allowPrintOut()
	 */
	@Override
	public boolean allowPrintOut() {
		return true;
	}

	/* (non-Javadoc)
	 * @see org.openjdk.jmh.profile.ExternalProfiler#beforeTrial(org.openjdk.jmh.infra.BenchmarkParams)
	 */
	@Override
	public void beforeTrial(BenchmarkParams arg0) {
		//noop
	}

	/* (non-Javadoc)
	 * @see org.openjdk.jmh.profile.ExternalProfiler#afterTrial(org.openjdk.jmh.results.BenchmarkResult, long, java.io.File, java.io.File)
	 */
	@Override
	public Collection<? extends Result> afterTrial(BenchmarkResult arg0, long arg1, File arg2, File arg3) {
        return new ArrayList<>();
	}

	/* (non-Javadoc)
	 * @see org.openjdk.jmh.profile.ExternalProfiler#addJVMOptions(org.openjdk.jmh.infra.BenchmarkParams)
	 */
	@Override
	public Collection<String> addJVMOptions(BenchmarkParams bp) {
		// Create the jfr file in the current directory named after the benchmark.
		return Arrays.asList("-XX:StartFlightRecording=settings=default,disk=true,dumponexit=true,filename=./" + bp.id() + ".jfr");
	}
}
