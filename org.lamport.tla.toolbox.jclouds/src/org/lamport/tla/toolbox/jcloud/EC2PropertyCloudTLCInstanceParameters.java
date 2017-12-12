/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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

public class EC2PropertyCloudTLCInstanceParameters extends EC2CloudTLCInstanceParameters {

	public EC2PropertyCloudTLCInstanceParameters(final String tlcParams, int numberOfWorkers) {
        super(tlcParams.trim(), numberOfWorkers);
	}

	@Override
	public String getImageId() {
		final String imageId = System.getProperty("aws-ec2.image");
		if (imageId == null) {
			return super.getImageId();
		}
		return getRegion() + "/" + imageId;
	}

	@Override
	public String getRegion() {
		return System.getProperty("aws-ec2.region", super.getRegion());
	}

	@Override
	public String getHardwareId() {
		return System.getProperty("aws-ec2.instanceType", super.getHardwareId());
	}

	@Override
	public String getOSFilesystemTuning() {
		return System.getProperty("aws-ec2.tuning", super.getOSFilesystemTuning());
	}

	@Override
	public String getJavaVMArgs() {
		return System.getProperty("aws-ec2.vmargs", super.getJavaVMArgs());
	}

	@Override
	public String getTLCParameters() {
		return System.getProperty("aws-ec2.tlcparams", super.getTLCParameters());
	}
}
