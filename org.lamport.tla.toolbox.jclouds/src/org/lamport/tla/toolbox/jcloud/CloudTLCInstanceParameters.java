/*******************************************************************************
 * Copyright (c) 2014 Microsoft Research. All rights reserved. 
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

package org.lamport.tla.toolbox.jcloud;

import java.util.Properties;

import org.eclipse.core.runtime.IStatus;
import org.jclouds.ContextBuilder;
import org.jclouds.compute.domain.TemplateBuilder;
import org.jclouds.compute.options.TemplateOptions;

import tlc2.tool.distributed.fp.TLCWorkerAndFPSet;

/**
 * This class serves two purposes.
 * 
 * a) It describes the instance running in the cloud
 * b) It provides TLC performance parameters to max out resource usage of the cloud instance
 */
public abstract class CloudTLCInstanceParameters {
	
	protected final String tlcParams;
	
	/**
	 * The number of cloud instances to be used. A value of one means
	 * non-distributed TLC. For values greater than 1, distributed TLC is launched.
	 */
	protected final int numberOfWorkerNodes;
	
	public CloudTLCInstanceParameters(String tlcParams) {
		this(tlcParams, 1);
	}

	public CloudTLCInstanceParameters(String tlcParams, int numberOfWorkerNodes) {
		this.tlcParams = tlcParams;
		this.numberOfWorkerNodes = numberOfWorkerNodes;
	}

	// system properties
	
	public String getJavaSystemProperties() {
		if (numberOfWorkerNodes == 1) {
			return getJavaWorkerSystemProperties();
		}
		//TODO Make this property be read from the generated.properties file
		return "-Dtlc2.tool.distributed.TLCServer.expectedFPSetCount=" + (numberOfWorkerNodes - 1);
	}

	public String getJavaWorkerSystemProperties() {
		//TODO Make this property be read from the generated.properties file
		return "-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet";
	}
	
	// vm args
	public abstract String getJavaVMArgs();
	
	protected String getJavaVMArgs(final String extraVMArgs) {
		if (numberOfWorkerNodes == 1) {
			return getJavaWorkerVMArgs();
		}
		// See org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob.getAdditionalVMArgs()
		return ("--add-modules=java.activation -XX:+IgnoreUnrecognizedVMOptions "
				+ "-XX:+UseParallelGC " // Java > 1.8 has switched to a low-latency GC which isn't optimized for
										// throughput anymore. Obviously, we are not interested in latency but primarily
										// in throughput.
				+ extraVMArgs).trim();
	}

	public abstract String getJavaWorkerVMArgs();
	
	protected String getJavaWorkerVMArgs(final String extraWorkerVMArgs) {
		// See org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob.getAdditionalVMArgs()
		return ("--add-modules=java.activation -XX:+IgnoreUnrecognizedVMOptions "
				+ extraWorkerVMArgs).trim();
	}

	// tlc parameters
	public abstract String getTLCParameters();
	
	protected String getTLCParameters(final int numWorkers) {
		if (numberOfWorkerNodes == 1) {
			if (tlcParams.length() > 0) {
				return "-workers " + numWorkers + " " + tlcParams;
			}
			return "-workers " + numWorkers;
		} else {
			return "-coverage 0 -checkpoint 0";
		}
	}

	public String getTLCWorkerParameters() {
		// TODO Ideally rewrite tla2tools.jar to replace the main-class in
		// META-INF/MANIFEST.MF when the model/* stuff is stripped.
		return TLCWorkerAndFPSet.class.getName();
	}
	
	public abstract String getCloudProvider();

	public abstract String getRegion();
	
	public abstract String getImageId();

	public abstract String getHardwareId();
	
	public abstract String getIdentity();
	
	public abstract String getCredentials();
	
	public abstract IStatus validateCredentials();

	public void mungeProperties(Properties properties) {
		// Nothing to be done here
	}

	public void mungeBuilder(ContextBuilder builder) {
		// Nothing to be done here
	}

	public void mungeTemplateOptions(TemplateOptions templateOptions) {
		// no-op, subclass may override
	}

	public String getOSFilesystemTuning() {
		return "/bin/true"; // no-op, because concat with && ... && in CDTJ.
	}
	
	public String getFlightRecording() {
		return "-XX:+UnlockCommercialFeatures "
				+ "-XX:+FlightRecorder "
				+ "-XX:+UnlockDiagnosticVMOptions "
				+ "-XX:+DebugNonSafepoints "
				+ "-XX:FlightRecorderOptions=defaultrecording=true,disk=true,repository=/mnt/tlc,dumponexit=true,dumponexitpath=/mnt/tlc/tlc.jfr,maxage=12h";
	}

	public String getHostnameSetup() {
		return "/bin/true"; // no-op, because concat with && ... && in CDTJ.
	}

	public String getCloudAPIShutdown() {
		return "/bin/true"; // no-op, because concat with && ... && in CDTJ.
	}

	public String getExtraRepositories() {
		return "/bin/true"; // no-op, because concat with && ... && in CDTJ.
	}

	public String getExtraPackages() {
		return ""; // no-op, because concat with && ... && in CDTJ.
	}

	public void mungeTemplateBuilder(final TemplateBuilder templateBuilder) {
		// no-op, subclass may override
	}
}
