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
		final String identity = System.getenv("PACKET_NET_PROJECT_ID");
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
		final String credential = System.getenv("PACKET_NET_PROJECT_ID");
		final String identity = System.getenv("PACKET_NET_APIKEY");
		if (credential == null || identity == null) {
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					"Invalid credentials, please check the environment variables "
							+ "(PACKET_NET_PROJECT_ID "
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

	@Override
	public String getCloudAPIShutdown(final String credentials) {
		// One might think we could simply invoke curl and terminate the instance right
		// away. That doesn't work because we want the instance to idle until the
		// scheduled shutdown call executes in case the Toolbox reuses the instance to
		// run another model.
//		return String.format("/usr/bin/curl -X DELETE -H X-Auth-Token:%s https://api.packet.net/devices/%s", credentials, nodeId);
		return String.format(
				"printf \"#!/bin/bash\\n"
				+ "if /usr/bin/curl https://metadata.packet.net/metadata 2>/dev/null | jq -e -r '.tags | index(\\\"power_off\\\")' > /dev/null; then\\n"
				+ " /usr/bin/curl -X POST -H X-Auth-Token:%s https://api.packet.net/devices/$(curl https://metadata.packet.net/metadata 2>/dev/null | jq -r '.id')/actions?type=power_off\\n"
				+ "else\\n"
				+ " /usr/bin/curl -X DELETE -H X-Auth-Token:%s https://api.packet.net/devices/$(curl https://metadata.packet.net/metadata 2>/dev/null | jq -r '.id')\\n"
				+ "fi\\n\" | sudo tee /usr/local/bin/packetnet.sh"
				+ " && sudo chmod +x /usr/local/bin/packetnet.sh"
				+ " && "
				+ "printf \"[Unit]\\nDescription=Delete instance via packetnet api on shutdown\\n"
				+ "Requires=network.target\\n"
				+ "DefaultDependencies=no\\n"
				+ "Before=shutdown.target\\n"
				+ "[Service]\\n"
				+ "Type=oneshot\\n"
				+ "RemainAfterExit=true\\n"
				+ "ExecStart=/bin/true\\n"
				+ "ExecStop=/usr/local/bin/packetnet.sh\\n"
				+ "[Install]\\n"
				+ "WantedBy=multi-user.target\\n\" | sudo tee /lib/systemd/system/delete-on-shutdown.service"
				+ " && systemctl enable delete-on-shutdown" // restart delete-on-shutdown service after a reboot.
				+ " && service delete-on-shutdown start",
				credentials, credentials);
		
		/*
			@packethost Can I somehow set (upon creation) servers to be automatically be deleted on an OS shutdown?
			@lemmster Not at the moment - you can control that from your automation / etc but we're not in the habit (in our API or otherwise) of deleting things on the behalf of clients.  Make sense?
			@packethost Others (Azure & AWS) do support automatic deletion. Why not make it a flag on instance creation?
			@lemmster Actually I lied, we do revoke in our spot market. We actually have the ability but always found that the risk (why did you delete my database) was more than the benefit.  Sorry!
			@packethost Me: Why did you delete my database? You: Because you told us to (by setting the delete-upon-shutdown flag during instance creation)!
			@lemmster For Ubuntu pass this userdata to create the delete-on-shutdown service for Packet's API. Not quite a flag but works!  gist.github.com/nathangoulding…
			@NathanGoulding Thanks! Just slightly worried about the security implications of having API token on the instance.
			@lemmster For sure, best to pull from an envvar or something like Vault vs. embedding (and certainly not passing via https userdata).
			@NathanGoulding I don't understand how an envvar or a vault - for which I need another secret to unlock, no? - solves the fundamental problem of having the API token on the instance?
			@lemmster You can limit the blast radius significantly with certs/keys that are single-use, tied to that specific instance, and/or revocable. If you can't trust the instance at all then yes you're stuck.
			@NathanGoulding Can I generate a single-use API subkey which is possibly even restricted to a specific instance?
			@NathanGoulding Could even be part of the response to the instance creation API call.
			@NathanGoulding Generally though, an instance creation flag is both simple and secure.
			@lemmster Agreed, unfortunately we don't have a hypervisor present to intercept the system shutdown call.
			@lemmster 'Unfortunately' in this one case at least ;)
			@NathanGoulding I assume that the same reason why servers show up as running in the admin frontend when shutdown locally?
			@lemmster Exactly, and I think our API calls them "active" to avoid "on/off" verbiage, but that green circle does look a lot like "on"
			
			https://twitter.com/NathanGoulding/status/1089990444287696897
			
			https://gist.github.com/nathangoulding/6a69b3fd7023bf3f558acfc7bb9ba645
		 */
	}
}
