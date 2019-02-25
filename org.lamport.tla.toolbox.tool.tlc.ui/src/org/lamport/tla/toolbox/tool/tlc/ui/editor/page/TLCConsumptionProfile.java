package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob;

import util.TLCRuntime;

/**
 * This enum represents the profile types of TLC running.
 */
public enum TLCConsumptionProfile {

	GREEDY("Most", 0.7, 0.8),
	NORMAL("Medium", 0.4, 0.4),
	LAZY("Minimal", 0.2, ((double)TLCProcessJob.HEAP_SIZE_DEFAULT / 100.0));
	
	
	private final double m_workerThreadPercentage;
	private final double m_memoryPercentage;
	private final String m_displayName;
	
	private TLCConsumptionProfile(final String name, final double threadPercentage, final double memoryPercentage) {
		m_displayName = name;
		m_workerThreadPercentage = threadPercentage;
		m_memoryPercentage = memoryPercentage;
	}
	
	public String getDisplayName() {
		return m_displayName;
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
