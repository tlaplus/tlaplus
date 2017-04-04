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
import org.eclipse.core.runtime.Status;
import org.jclouds.aws.ec2.reference.AWSEC2Constants;
import org.jclouds.location.reference.LocationConstants;

public class EC2CloudTLCInstanceParameters extends CloudTLCInstanceParameters {

	public EC2CloudTLCInstanceParameters(final String tlcParams, int numberOfWorkers) {
        super(tlcParams.trim(), numberOfWorkers);
	}

	private String getOwnerId() {
		// ubuntu official
		return "owner-id=owner-id=099720109477;state=available;image-type=machine";
	}

	@Override
	public String getCloudProvider() {
		return "aws-ec2";
	}

	@Override
	public String getImageId() {
		// Ubuntu 64bit 14.04.4 Trusty paravirtual/instance-store release
		// https://cloud-images.ubuntu.com/releases/14.04/release/
		// or http://cloud-images.ubuntu.com/locator/ec2/
		// See http://aws.amazon.com/amazon-linux-ami/instance-type-matrix/
		// for paravirtual vs. hvm
		return getRegion() + "/ami-59ce434e";
	}

	private String getRegion() {
		return "us-east-1";
	}

	@Override
	public String getHardwareId() {
		// m2 only support paravirtual
		return "m2.4xlarge";
	}

	@Override
	public String getIdentity() {
		return System.getenv("AWS_ACCESS_KEY_ID");
	}

	@Override
	public String getCredentials() {
		return System.getenv("AWS_SECRET_ACCESS_KEY");
	}
	
	// http://docs.aws.amazon.com/AWSSimpleQueueService/latest/SQSDeveloperGuide/AWSCredentials.html
	@Override
	public IStatus validateCredentials() {
		// must not be null
		if (getIdentity() != null && getCredentials() != null) {
			// identity always starts with "AIKA" and has 20 chars
			if (getIdentity().matches("AKIA[a-zA-Z0-9]{16}")) {
				// secret has 40 chars
				if (getCredentials().length() == 40) {
					return Status.OK_STATUS;
				}
			}
		}
		return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
				"Invalid credentials, please check the environment variables "
						+ "(AWS_ACCESS_KEY_ID & AWS_SECRET_ACCESS_KEY) are correctly "
						+ "set up and picked up by the Toolbox.");
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#mungeProperties(java.util.Properties)
	 */
	@Override
	public void mungeProperties(Properties properties) {
		properties.setProperty(AWSEC2Constants.PROPERTY_EC2_AMI_QUERY, getOwnerId());
		// Confine jclouds to a single region. Since the Toolbox only supports a
		// single region, there is no point in querying others. This has been
		// added because I was seeing intermittent timeouts with other regions
		// (i.e. South America).
		properties.setProperty(LocationConstants.PROPERTY_REGIONS, getRegion());
	}
}
