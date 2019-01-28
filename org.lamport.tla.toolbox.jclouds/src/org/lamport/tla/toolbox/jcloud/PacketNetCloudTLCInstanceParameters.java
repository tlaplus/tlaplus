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
package org.lamport.tla.toolbox.jcloud;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.jclouds.compute.domain.TemplateBuilder;

public class PacketNetCloudTLCInstanceParameters extends CloudTLCInstanceParameters {

	public PacketNetCloudTLCInstanceParameters(final String tlcParams, int numberOfWorkers) {
		super(tlcParams.trim(), numberOfWorkers);
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getJavaVMArgs()
	 */
	@Override
	public String getJavaVMArgs() {
		return System.getProperty("packetnet.vmargs", super.getJavaVMArgs("-Xmx6G -Xms6G"));
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getJavaWorkerVMArgs()
	 */
	@Override
	public String getJavaWorkerVMArgs() {
		return System.getProperty("packetnet.vmworkerargs",
				super.getJavaWorkerVMArgs("-Xmx4G -Xms4G -XX:MaxDirectMemorySize=2g"));
	}
	
	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getTLCParameters()
	 */
	@Override
	public String getTLCParameters() {
		return System.getProperty("packetnet.tlcparams", super.getTLCParameters(16));
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getCloudProvier()
	 */
	@Override
	public String getCloudProvider() {
		return "packet"; // as defined by jclouds.
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getRegion()
	 */
	@Override
	public String getRegion() {
		return System.getProperty("packetnet.region", "sjc1");
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getImageId()
	 */
	@Override
	public String getImageId() {
		return System.getProperty("packetnet.image", "ubuntu_18_04");
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getHardwareId()
	 */
	@Override
	public String getHardwareId() {
		return System.getProperty("packetnet.instanceType", "baremetal_0"); // t1.small.x86 whose "slug" is baremetal_0.
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getIdentity()
	 */
	@Override
	public String getIdentity() {
		final String identity = System.getenv("PACKET_NET_DEFAULT_PROJECT_ID");
		Assert.isNotNull(identity);
		return identity;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getCredentials()
	 */
	@Override
	public String getCredentials() {
		final String credential = System.getenv("PACKET_NET_APIKEY");
		Assert.isNotNull(credential);
		return credential;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#validateCredentials()
	 */
	@Override
	public IStatus validateCredentials() {
		final String credential = System.getenv("PACKET_NET_DEFAULT_PROJECT_ID");
		final String identity = System.getenv("PACKET_NET_APIKEY");
		if (credential == null || identity == null) {
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					"Invalid credentials, please check the environment variables "
							+ "(PACKET_NET_DEFAULT_PROJECT_ID "
							+ "and PACKET_NET_APIKEY) are correctly "
							+ "set up and picked up by the Toolbox."
							+ "\n\nPlease visit the Toolbox help and read section 4 "
							+ "of \"Cloud based distributed TLC\" on how to setup authentication.");
		}
		return Status.OK_STATUS;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#mungeTemplateBuilder(org.jclouds.compute.domain.TemplateBuilder)
	 */
	@Override
	public void mungeTemplateBuilder(TemplateBuilder templateBuilder) {
        templateBuilder.locationId(getRegion());
	}
}
