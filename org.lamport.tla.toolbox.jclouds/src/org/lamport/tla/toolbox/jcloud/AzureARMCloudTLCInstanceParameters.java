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

import java.util.Properties;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.jclouds.ContextBuilder;
import org.jclouds.location.reference.LocationConstants;

public class AzureARMCloudTLCInstanceParameters extends AzureCloudTLCInstanceParameters {

	public AzureARMCloudTLCInstanceParameters(final String tlcParams, int numberOfWorkers) {
        super(tlcParams.trim(), numberOfWorkers);
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getCloudProvier()
	 */
	@Override
	public String getCloudProvider() {
		return "azurecompute-arm";
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getRegion()
	 */
	@Override
	public String getRegion() {
		return System.getProperty("azure.region", "eastus");
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getImageId()
	 */
	@Override
	public String getImageId() {
		// With azure-cli v2 (based on Python) extract name from 'az vm image list --all --publisher Canonical'.
		return System.getProperty("azure.image", "eastus/Canonical/UbuntuServer/18.04-LTS");	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getHardwareId()
	 */
	@Override
	public String getHardwareId() {
		// STANDARD_D14: 16 cores, 112GB
		return System.getProperty("azure.instanceType", "eastus/Standard_D14");
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getIdentity()
	 */
	@Override
	public String getIdentity() {
		final String identity = System.getenv("AZURE_COMPUTE_SERVICE_PRINCIPAL");
		Assert.isNotNull(identity);
		return identity;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getCredentials()
	 */
	@Override
	public String getCredentials() {
		final String credential = System.getenv("AZURE_COMPUTE_SERVICE_PRINCIPAL_PASSWORD");
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
		final String credential = System.getenv("AZURE_COMPUTE_SERVICE_PRINCIPAL_PASSWORD");
		final String identity = System.getenv("AZURE_COMPUTE_SERVICE_PRINCIPAL");
		final String subscription = System.getenv("AZURE_COMPUTE_SUBSCRIPTION");
		final String tenantId = System.getenv("AZURE_COMPUTE_TENANT");
		if (credential == null || identity == null || subscription == null || tenantId == null) {
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					"Invalid credentials, please check the environment variables "
							+ "(AZURE_COMPUTE_SERVICE_PRINCIPAL_PASSWORD & AZURE_COMPUTE_SERVICE_PRINCIPAL "
							+ "& AZURE_COMPUTE_TENANT and AZURE_COMPUTE_SUBSCRIPTION) are correctly "
							+ "set up and picked up by the Toolbox."
							+ "\n\nPlease visit the Toolbox help and read section 4 "
							+ "of \"Cloud based distributed TLC\" on how to setup authentication.");
		}
		return Status.OK_STATUS;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#mungeProperties(java.util.Properties)
	 */
	@Override
	public void mungeProperties(final Properties properties) {
        properties.setProperty("azurecompute-arm.tenantId", System.getenv("AZURE_COMPUTE_TENANT"));
		// Minimize back and forth with Azure API by limiting images to those provided
		// by Canoncial. Also only talk to Azure in US east. Both properties reduce
		// startup time.
        // org/jclouds/azurecompute/arm/config/AzureComputeProperties.IMAGE_PUBLISHERS
        properties.setProperty("jclouds.azurecompute.arm.publishers", "Canonical");
        properties.setProperty(LocationConstants.PROPERTY_REGIONS, "eastus");
		super.mungeProperties(properties);
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#mungeBuilder(org.jclouds.ContextBuilder)
	 */
	@Override
	public void mungeBuilder(ContextBuilder builder) {
		builder.endpoint("https://management.azure.com/subscriptions/" + getSubscriptionId());
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
