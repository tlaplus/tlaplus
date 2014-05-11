package org.lamport.tla.toolbox.jcloud;

/**
 * This class serves two purposes.
 * 
 * a) It describes the instance running in the cloud
 * b) It provides TLC performance parameters to max out resource usage of the cloud instance
 */
public abstract class CloudTLCInstanceParameters {
	
	public abstract String getOwnerId();

	public abstract String getCloudProvier();

	public abstract String getImageId();

	public abstract String getHardwareId();
	
	public abstract String getJavaSystemProperties();
	
	public abstract String getJavaVMArgs();
	
	public abstract String getTLCParameters();
}
