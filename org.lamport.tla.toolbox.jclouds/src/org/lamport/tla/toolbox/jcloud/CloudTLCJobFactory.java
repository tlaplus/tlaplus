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

import java.io.File;
import java.util.Properties;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.jobs.Job;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJobFactory;

public class CloudTLCJobFactory implements TLCJobFactory {

	private static final String AZURECOMPUTE = "Azure";
	private static final String AWS_EC2 = "aws-ec2";
	private static final String PACKET_NET = "PacketNet";

	@Override
	public Job getTLCJob(String aName, File aModelFolder, int numberOfWorkers, final Properties props, String tlcparams) {
		Assert.isNotNull(aName);
		Assert.isLegal(numberOfWorkers > 0);
		if (AWS_EC2.equalsIgnoreCase(aName)) {
			return new CloudDistributedTLCJob(aName, aModelFolder, numberOfWorkers, props,
					new EC2CloudTLCInstanceParameters(tlcparams, numberOfWorkers));
		} else if (AZURECOMPUTE.equalsIgnoreCase(aName)) {
			return new CloudDistributedTLCJob(aName, aModelFolder, numberOfWorkers, props,
					new AzureARMCloudTLCInstanceParameters(tlcparams, numberOfWorkers));
		} else if (PACKET_NET.equalsIgnoreCase(aName)) {
			return new CloudDistributedTLCJob(aName, aModelFolder, numberOfWorkers, props,
					new PacketNetCloudTLCInstanceParameters(tlcparams, numberOfWorkers));
		}
		throw new IllegalArgumentException(aName + " is an unknown cloud");
	}
}
