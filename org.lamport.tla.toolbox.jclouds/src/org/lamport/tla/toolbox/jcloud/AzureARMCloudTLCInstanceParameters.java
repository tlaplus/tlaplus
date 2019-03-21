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

	private static final String AZURE_COMPUTE_SUBSCRIPTION = "AZURE_COMPUTE_SUBSCRIPTION";
	private static final String AZURE_COMPUTE_SERVICE_PRINCIPAL = "AZURE_COMPUTE_SERVICE_PRINCIPAL";
	private static final String AZURE_COMPUTE_SERVICE_PRINCIPAL_PASSWORD = "AZURE_COMPUTE_SERVICE_PRINCIPAL_PASSWORD";
	private static final String AZURE_COMPUTE_TENANT = "AZURE_COMPUTE_TENANT";

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
		final String identity = System.getenv(AZURE_COMPUTE_SERVICE_PRINCIPAL);
		Assert.isNotNull(identity);
		return identity;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getCredentials()
	 */
	@Override
	public String getCredentials() {
		final String credential = System.getenv(AZURE_COMPUTE_SERVICE_PRINCIPAL_PASSWORD);
		Assert.isNotNull(credential);
		return credential;
	}

	private String getSubscriptionId() {
		final String subscription = System.getenv(AZURE_COMPUTE_SUBSCRIPTION);
		Assert.isNotNull(subscription);
		return subscription;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#validateCredentials()
	 */
	@Override
	public IStatus validateCredentials() {
		final String credential = System.getenv(AZURE_COMPUTE_SERVICE_PRINCIPAL_PASSWORD);
		final String identity = System.getenv(AZURE_COMPUTE_SERVICE_PRINCIPAL);
		final String subscription = System.getenv(AZURE_COMPUTE_SUBSCRIPTION);
		final String tenantId = System.getenv(AZURE_COMPUTE_TENANT);
		if (credential == null || identity == null || subscription == null || tenantId == null) {
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					"Invalid credentials, please check the environment variables "
							+ "(" + AZURE_COMPUTE_SERVICE_PRINCIPAL_PASSWORD + " & " + AZURE_COMPUTE_SERVICE_PRINCIPAL + " "
							+ "& " + AZURE_COMPUTE_TENANT + " and " + AZURE_COMPUTE_SUBSCRIPTION + ") are correctly "
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
        properties.setProperty("azurecompute-arm.tenantId", System.getenv(AZURE_COMPUTE_TENANT));
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

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getExtraRepositories()
	 */
	@Override
	public String getExtraRepositories() {
		// https://docs.microsoft.com/en-us/cli/azure/install-azure-cli-apt?view=azure-cli-latest
		return "echo \"deb [arch=amd64] https://packages.microsoft.com/repos/azure-cli/ $(lsb_release -cs) main\" | sudo tee /etc/apt/sources.list.d/azure-cli.list"
				+ " && "
				+ "apt-key adv --keyserver packages.microsoft.com --recv-keys BC528686B50D79E339D3721CEB3E94ADBE1229CF";
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getExtraPackages()
	 */
	@Override
	public String getExtraPackages() {
		// https://docs.microsoft.com/en-us/cli/azure/install-azure-cli?view=azure-cli-latest#install-on-debianubuntu-with-apt-get
		// see getExtraRepositories too.
		return "azure-cli";
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getCloudAPIShutdown(java.lang.String, java.lang.String)
	 */
	@Override
	public String getCloudAPIShutdown(final String credentials, final String groupName) {
		final String servicePrincipal = System.getenv(AZURE_COMPUTE_SERVICE_PRINCIPAL);
		final String password = System.getenv(AZURE_COMPUTE_SERVICE_PRINCIPAL_PASSWORD);
		final String tenant = System.getenv(AZURE_COMPUTE_TENANT);
		if (servicePrincipal == null || password == null || tenant == null) {
			// Missing credentials.
			return super.getCloudAPIShutdown(credentials, groupName);
		}
		// What we try to accomplish is to purge the complete Azure Resource Group (a RG
		// combines all Azure resources associated with the VM (storage, networking,
		// ips, ...).
		//
		// Unfortunately, the azure CLI needs credentials to talk to the Azure API. The
		// switch to jclouds's azurecompute-arm provider means we can simply reuse the
		// service-principal credentials here.
		//
		// An alternative to calling the az login process would be to use an
		// auth.properties file, but this doesn't seem supported by azure CLI yet. Read
		// "File based authentication" at
		// https://docs.microsoft.com/en-us/java/azure/java-sdk-azure-authenticate#mgmt-file
		return String.format(
				// Sign into azure during instance provisioning to catch auth error early and not only during instance termination.
				// Nest in "sudo -i" to make sure azure credentials are created for root account which runs
				// "az group delete ..." during instance shutdown. 
				"/usr/bin/sudo -i /usr/bin/az login --service-principal -u %s -p %s --tenant %s"
				+ " && "
				// @see PacketNetCloudTLCInstanceParameters#getCloudAPIShutdown
				+ "printf \"[Unit]\\nDescription=Delete Azure resource group via azure-cli on instance shutdown\\n"
				+ "Requires=network.target\\n"
				+ "After=network.target\\n"
				+ "DefaultDependencies=no\\n"
				+ "Before=shutdown.target\\n"
				+ "[Service]\\n"
				+ "Type=oneshot\\n"
				+ "RemainAfterExit=true\\n"
				+ "ExecStart=/bin/true\\n"
				// Great, this is much simpler compared to 589e6fc82ce182b0c49c4c1fb63bc0aae711cf5f
				+ "ExecStop=/usr/bin/az group delete --name %s -y\\n"
				+ "[Install]\\n"
				+ "WantedBy=multi-user.target\\n\" | sudo tee /lib/systemd/system/delete-on-shutdown.service"
				+ " && systemctl enable delete-on-shutdown" // restart delete-on-shutdown service after a reboot.
				+ " && service delete-on-shutdown start",
				servicePrincipal, password, tenant, groupName);
	}
}
