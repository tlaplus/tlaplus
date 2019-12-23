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

import java.util.Properties;

import org.jclouds.location.reference.LocationConstants;

public class TLAAzureARMCloudTLCInstanceParameters extends AzureARMCloudTLCInstanceParameters {

	public TLAAzureARMCloudTLCInstanceParameters(final String tlcParams, int numberOfWorkers) {
        super(tlcParams.trim(), numberOfWorkers);
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getImageId()
	 */
	@Override
	public String getImageId() {
		// With azure-cli v2 (based on Python) extract name from 'az vm image list --all --publisher Canonical'.
		return System.getProperty("azure.image", "tlaplus/" + getRegion() + "/tlaplus-tlc-2019.12");
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getRegion()
	 */
	@Override
	public String getRegion() {
		return System.getProperty("azure.region", "westus");
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#mungeProperties(java.util.Properties)
	 */
	@Override
	public void mungeProperties(final Properties properties) {
		super.mungeProperties(properties);
		// Receiving publisher images can take a long time if the publisher has many
		// images. We know which image we want to use (ours!!!), which is why we don't
		// want to wait. A bogus name won't have images.
        properties.setProperty("jclouds.azurecompute.arm.publishers", "APublisherThatDoesNotExist");
        properties.setProperty(LocationConstants.PROPERTY_REGIONS, getRegion());
	}

	@Override
	protected boolean isVanillaVMImage() {
		return false;
	}
	
	/*
	 * How to create a TLA+ VM image?
	 * 1. Start a regular Axure image with Cloud TLC.
	 * 2. Disable/Remove Cloud Shutdown hook!!!
	 * 3. Stop the Azure VM through the portal or az command-line app.
	 * 4. Trigger image creation through Azure portal and wait for Azure to do its thing.
	 * 5. Delete remnant of the actual Azure instance.
	 * 6. Subst azure.image above with name given in 4.
	 * 
	 * Note that the image won't have a working shutdown hook.
	 */
}
