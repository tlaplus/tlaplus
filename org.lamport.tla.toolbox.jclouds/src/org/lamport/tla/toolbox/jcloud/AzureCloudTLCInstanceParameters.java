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

import java.io.File;

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
		return System.getProperty("azure.vmargs", super.getJavaVMArgs("-Xmx96G -Xms96G"));
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getJavaWorkerVMArgs()
	 */
	@Override
	public String getJavaWorkerVMArgs() {
		return System.getProperty("azure.vmworkerargs",
				super.getJavaWorkerVMArgs("-Xmx32G -Xms32G -XX:MaxDirectMemorySize=64g"));
	}
	
	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getTLCParameters()
	 */
	@Override
	public String getTLCParameters() {
		return System.getProperty("azure.tlcparams", super.getTLCParameters(16));
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
		return System.getProperty("azure.region", "us-east");
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getImageId()
	 */
	@Override
	public String getImageId() {
		// 'azure vm image list eastus canonical' (manually lookup image release date from output)
		// With azure-cli v2 (based on Python) extract date from 'az vm image list --all --publisher Canonical'.
		return System.getProperty("azure.image", "b39f27a8b8c64d52b05eac6a62ebad85__Ubuntu-18_04-LTS-amd64-server-20180426.2-en-us-30GB");
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getHardwareId()
	 */
	@Override
	public String getHardwareId() {
		// STANDARD_D14: 16 cores, 112GB
		return System.getProperty("azure.instanceType", "STANDARD_D14");
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
							+ "set up and picked up by the Toolbox."
							+ "\n\nPlease visit the Toolbox help and read section 4 "
							+ "of \"Cloud based distributed TLC\" on how to setup authentication.");
		}
		// Verify that the identity file exists.
		final File file = new File(identity);
		if (!file.exists()) {
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud", String.format(
					"The file %s referenced by the AZURE_COMPUTE_IDENTITY environment variable does not exist.", file));
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
	
	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getHostnameSetup()
	 */
	@Override
	public String getHostnameSetup() {
		// Append ".cloudapp.net" to automatically set hostname and add a mapping from
		// public ip (obtained via third party service ifconfig.co) to hostname in
	    // /etc/hosts. Results in FQDN being used my MailSender and thus less likely
		// to be classified or rejected as spam.
		// The suffix ".cloudapp.net" is something that might change on the Azure end in
		// the future. It will then break this statement (suffix can be found in portal).
		// It would also be nice for Azure to offer a public API to query the hostname
		// (similar to EC2CloudTLCInstanceParameters#getHostnameSetup.
		return "hostname \"$(hostname).cloudapp.net\" && echo \"$(curl -s ifconfig.co) $(hostname)\" >> /etc/hosts";
	}
}
