package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob;

import util.TLCRuntime;

/**
 * This enum represents the profile types of TLC running.
 */
public enum TLCConsumptionProfile {

	LOCAL_MOST("Local Most", 0.7, 0.8, null, "local most"),
	LOCAL_NORMAL("Local Medium", 0.5, 0.4, null, "local nomal"),
	LOCAL_MINIMAL("Local Minimal", 0.2, ((double)TLCProcessJob.HEAP_SIZE_DEFAULT / 100.0), null, "local minimal"),
	REMOTE_AD_HOC("Ad Hoc", 0, 0.3, "ad hoc", "ad hoc"),
	REMOTE_AWS("Amazon", 0, 0, MainModelPage.CLOUD_CONFIGURATION_KEY, "aws-ec2"),
	REMOTE_AZURE("Azure", 0, 0, MainModelPage.CLOUD_CONFIGURATION_KEY, "Azure"),
	REMOTE_PACKET_NET("PacketNet", 0, 0, MainModelPage.CLOUD_CONFIGURATION_KEY, "PacketNet");
	
	public static TLCConsumptionProfile getProfileWithPreferenceValue(final String value) {
		for (final TLCConsumptionProfile profile : TLCConsumptionProfile.values()) {
			if (value.equals(profile.getPreferenceValue())) {
				return profile;
			}
		}
		
		return null;
	}
	
	public static TLCConsumptionProfile getProfileWithDisplayName(final String displayName) {
		for (final TLCConsumptionProfile profile : TLCConsumptionProfile.values()) {
			if (displayName.equals(profile.getDisplayName())) {
				return profile;
			}
		}
		
		return null;
	}
	
	
	private final double m_workerThreadPercentage;
	private final double m_memoryPercentage;
	private final String m_displayName;
	
	private final String m_configurationKey;
	
	private final String m_preferenceValue;
	
	private TLCConsumptionProfile(final String name, final double threadPercentage, final double memoryPercentage,
			final String uiConfigurationKey, final String preferenceValue) {
		m_displayName = name;
		
		m_workerThreadPercentage = threadPercentage;
		m_memoryPercentage = memoryPercentage;
		
		m_configurationKey = uiConfigurationKey;
		
		m_preferenceValue = preferenceValue;
	}
	
	public String getDisplayName() {
		return m_displayName;
	}
	
	public boolean profileIsForRemoteWorkers() {
		return (m_configurationKey != null);
	}
	
	public String getConfigurationKey() {
		return m_configurationKey;
	}
	
	public String getPreferenceValue() {
		return m_preferenceValue;
	}
	
	/**
	 * @return the 0-100 representation of percentage
	 */
	public int getMemoryPercentage() {
		return (int)(100.0 * m_memoryPercentage);
	}
	
	public long getMemory() {
		return TLCRuntime.getInstance().getAbsolutePhysicalSystemMemory(m_memoryPercentage);
	}
	
	public int getWorkerThreads() {
		return (int)Math.ceil((float)Runtime.getRuntime().availableProcessors() * m_workerThreadPercentage);
	}
	
}
