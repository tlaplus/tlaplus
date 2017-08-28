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

package org.lamport.tla.toolbox.jcloud;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.jclouds.ContextBuilder;

public class AzureCloudTLCInstanceParameters extends CloudTLCInstanceParameters {

	public AzureCloudTLCInstanceParameters(final String tlcParams, int numberOfWorkers) {
        super(tlcParams.trim(), numberOfWorkers);
	}
	
	// vm args

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getJavaVMArgs()
	 */
	@Override
	public String getJavaVMArgs() {
		if (numberOfWorkers == 1) {
			return getJavaWorkerVMArgs();
		}
		// See org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob.getAdditionalVMArgs()
		return "--add-modules=java.activation -XX:+IgnoreUnrecognizedVMOptions -Xmx96G -Xms96G";
	}
	
	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getJavaWorkerVMArgs()
	 */
	@Override
	public String getJavaWorkerVMArgs() {
		// See org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob.getAdditionalVMArgs()
		return "--add-modules=java.activation -XX:+IgnoreUnrecognizedVMOptions -Xmx32G -Xms32G -XX:MaxDirectMemorySize=64g";
	}
	
	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getTLCParameters()
	 */
	@Override
	public String getTLCParameters() {
		if (numberOfWorkers == 1) {
			if (tlcParams.length() > 0) {
				return "-workers 16 " + tlcParams;
			}
			return "-workers 16";
		} else {
			return "-coverage 0 -checkpoint 0";
		}
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getCloudProvier()
	 */
	@Override
	public String getCloudProvider() {
		return "azurecompute";
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getRegion()
	 */
	@Override
	public String getRegion() {
		return "us-east";
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getImageId()
	 */
	@Override
	public String getImageId() {
		// azure vm image list eastus canonical (manually lookup image release date from output)
		return "b39f27a8b8c64d52b05eac6a62ebad85__Ubuntu-16_04-LTS-amd64-server-20170811-en-us-30GB";
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getHardwareId()
	 */
	@Override
	public String getHardwareId() {
		return "STANDARD_D14";
		// 16 cores
		// 112GB
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getIdentity()
	 */
	@Override
	public String getIdentity() {
		final String identity = System.getenv("AZURE_COMPUTE_IDENTITY");
		Assert.isNotNull(identity);
		return identity;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getCredentials()
	 */
	@Override
	public String getCredentials() {
		final String credential = System.getenv("AZURE_COMPUTE_CREDENTIALS");
		Assert.isNotNull(credential);
		return credential;
	}

	private String getSubscriptionId() {
		final String subscription = System.getenv("AZURE_COMPUTE_SUBSCRIPTION");
		Assert.isNotNull(subscription);
		return subscription;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#validateCredentials()
	 */
	@Override
	public IStatus validateCredentials() {
		final String credential = System.getenv("AZURE_COMPUTE_CREDENTIALS");
		final String identity = System.getenv("AZURE_COMPUTE_IDENTITY");
		final String subscription = System.getenv("AZURE_COMPUTE_SUBSCRIPTION");
		if (credential == null || identity == null || subscription == null) {
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					"Invalid credentials, please check the environment variables "
							+ "(AZURE_COMPUTE_CREDENTIALS & AZURE_COMPUTE_IDENTITY "
							+ "and AZURE_COMPUTE_SUBSCRIPTION) are correctly "
							+ "set up and picked up by the Toolbox.");
		}
		return Status.OK_STATUS;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#mungeBuilder(org.jclouds.ContextBuilder)
	 */
	@Override
	public void mungeBuilder(ContextBuilder builder) {
		builder.endpoint("https://management.core.windows.net/" + getSubscriptionId());
	}
}
