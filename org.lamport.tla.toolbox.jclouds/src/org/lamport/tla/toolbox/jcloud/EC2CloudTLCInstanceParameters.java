package org.lamport.tla.toolbox.jcloud;

public class EC2CloudTLCInstanceParameters extends CloudTLCInstanceParameters {

	private final String tlcParams;

	public EC2CloudTLCInstanceParameters(final String tlcParams) {
        this.tlcParams = tlcParams.trim();
	}

	@Override
	public String getOwnerId() {
		// ubuntu official
		return "owner-id=owner-id=099720109477;state=available;image-type=machine";
	}

	@Override
	public String getCloudProvier() {
		return "aws-ec2";
	}

	@Override
	public String getImageId() {
		// Ubuntu 64bit 14.04.2 Trusty paravirtual/instance-store release
		// https://cloud-images.ubuntu.com/releases/14.04/release/
		// or http://cloud-images.ubuntu.com/locator/ec2/
		// See http://aws.amazon.com/amazon-linux-ami/instance-type-matrix/
		// for paravirtual vs. hvm
		return "us-east-1/ami-3234315a";
	}

	@Override
	public String getHardwareId() {
		// m2 only support paravirtual
		return "m2.4xlarge";
	}

	@Override
	public String getJavaSystemProperties() {
		return "-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet";
	}

	@Override
	public String getJavaVMArgs() {
		return "-Xmx24G -Xms24G -XX:MaxDirectMemorySize=32g";
	}

	@Override
	public String getTLCParameters() {
		if (tlcParams.length() > 0) {
			return "-workers 12 " + tlcParams;
		}
		return "-workers 12";
	}
}
