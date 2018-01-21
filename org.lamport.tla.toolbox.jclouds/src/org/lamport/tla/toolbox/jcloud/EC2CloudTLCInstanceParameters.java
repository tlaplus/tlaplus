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

	@Override
	public String getHostnameSetup() {
		// Lookup public ipv4 hostname and configure /etc/hosts accordingly. Otherwise,
		// MailSender uses the internal name which increases likelihood of email being
		// classified/rejected as spam.
		return "echo \"$(curl -s http://169.254.169.254/latest/meta-data/local-ipv4) $(curl -s http://169.254.169.254/latest/meta-data/public-hostname)\" >> /etc/hosts && hostname $(curl -s http://169.254.169.254/latest/meta-data/public-hostname)";
	}
	

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getImageId()
	 */
	@Override
	public String getImageId() {
		// Ubuntu 64bit 16.04 Xenial
		// http://cloud-images.ubuntu.com/locator/ec2/
		// See http://aws.amazon.com/amazon-linux-ami/instance-type-matrix/
		// for paravirtual vs. hvm (if instance startup fails with funny errors
		// such as symlinks failing to be created, you accidentally picked paravirtual.
		 // "us-east-1,xenial,amd64,hvm:instance-store"
		final String imageId = System.getProperty("aws-ec2.image", "ami-51025a2b");
		return getRegion() + "/" + imageId;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getRegion()
	 */
	@Override
	public String getRegion() {
		return System.getProperty("aws-ec2.region", "us-east-1");
	}

	@Override
	public String getHardwareId() {
		return System.getProperty("aws-ec2.instanceType", "c3.8xlarge");
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getOSFilesystemTuning()
	 */
	@Override
	public String getOSFilesystemTuning() {
		return System.getProperty("aws-ec2.tuning", getOSFilesystemTuningDefault());
	}
	
	private String getOSFilesystemTuningDefault() {
		// Create a raid0 out of the two instance store
		// disks and optimize its fs towards performance
		// by sacrificing data durability.
		return "umount /mnt && "
		+ "/usr/bin/yes|/sbin/mdadm --create --force --auto=yes /dev/md0 --level=0 --raid-devices=2 --assume-clean --name=tlaplus /dev/xvdb /dev/xvdc && "
		+ "/sbin/mdadm --detail --scan >> /etc/mdadm/mdadm.conf && "
		+ "sed -i '\\?^/dev/xvdb?d' /etc/fstab && "
		+ "echo \"/dev/md127 /mnt ext4 defaults 0 0\" >> /etc/fstab && "
		+ "/sbin/mkfs.ext4 -O ^has_journal /dev/md0 && "
		+ "mount /dev/md0 /mnt";
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getJavaVMArgs()
	 */
	@Override
	public String getJavaVMArgs() {
		return System.getProperty("aws-ec2.vmargs", super.getJavaVMArgs("-Xmx56G -Xms56G"));
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getTLCParameters()
	 */
	@Override
	public String getTLCParameters() {
		return System.getProperty("aws-ec2.tlcparams", super.getTLCParameters(32));
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.jcloud.CloudTLCInstanceParameters#getJavaWorkerVMArgs()
	 */
	@Override
	public String getJavaWorkerVMArgs() {
		return System.getProperty("aws-ec2.vmworkerargs", super.getJavaWorkerVMArgs("-Xmx24G -Xms24G -XX:MaxDirectMemorySize=32g"));
	}
}
