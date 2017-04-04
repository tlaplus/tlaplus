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

import tlc2.tool.distributed.fp.TLCWorkerAndFPSet;

/**
 * This class serves two purposes.
 * 
 * a) It describes the instance running in the cloud
 * b) It provides TLC performance parameters to max out resource usage of the cloud instance
 */
public abstract class CloudTLCInstanceParameters {
	
	protected final String tlcParams;
	protected final int numberOfWorkers;
	
	public CloudTLCInstanceParameters(String tlcParams) {
		this(tlcParams, 1);
	}

	public CloudTLCInstanceParameters(String tlcParams, int numberOfWorkers) {
		this.tlcParams = tlcParams;
		this.numberOfWorkers = numberOfWorkers;
	}

	// system properties
	
	public String getJavaSystemProperties() {
		if (numberOfWorkers == 1) {
			return getJavaWorkerSystemProperties();
		}
		//TODO Make this property be read from the generated.properties file
		return "-Dtlc2.tool.distributed.TLCServer.expectedFPSetCount=" + (numberOfWorkers - 1);
	}

	public String getJavaWorkerSystemProperties() {
		//TODO Make this property be read from the generated.properties file
		return "-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet";
	}
	
	// vm args
	
	public String getJavaVMArgs() {
		if (numberOfWorkers == 1) {
			return getJavaWorkerVMArgs();
		}
		return "-Xmx56G -Xms56G";
	}
	
	public String getJavaWorkerVMArgs() {
		return "-Xmx24G -Xms24G -XX:MaxDirectMemorySize=32g";
	}

	// tlc parameters
	
	public String getTLCParameters() {
		if (numberOfWorkers == 1) {
			if (tlcParams.length() > 0) {
				return "-workers 32 " + tlcParams;
			}
			return "-workers 32";
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
}
