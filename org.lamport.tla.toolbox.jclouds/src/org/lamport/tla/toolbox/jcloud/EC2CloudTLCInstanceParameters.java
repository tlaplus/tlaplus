package org.lamport.tla.toolbox.jcloud;

public class EC2CloudTLCInstanceParameters extends CloudTLCInstanceParameters {

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
		// ubuntu 64bit 14.04 trusty paravirtual release
		// https://cloud-images.ubuntu.com/releases/14.04/release/
		return "us-east-1/ami-e411d98c";
	}

	@Override
	public String getHardwareId() {
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
		return "-workers 12";
	}
}
