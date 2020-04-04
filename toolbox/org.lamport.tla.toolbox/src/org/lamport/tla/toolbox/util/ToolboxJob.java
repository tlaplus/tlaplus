package org.lamport.tla.toolbox.util;

import org.eclipse.core.runtime.jobs.Job;

public abstract class ToolboxJob extends Job {

	/**
	 * Jobs marked by this family will be disposed by the TLCLifeCycleParticipant 
	 * in bundle org.lamport.tla.toolbox.tlc
	 */
	//TODO refactor lifecycleparticipant to live in .toolbox instead of .tlc
	public static final String FAMILY = ToolboxJob.class.getName() + ".TOOLBOX_JOBS_FAMILY";

	public ToolboxJob(String name) {
		super(name);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.jobs.Job#belongsTo(java.lang.Object)
	 */
	@Override
	public boolean belongsTo(Object aFamily) {
		if(FAMILY.equals(aFamily)) {
			return true;
		}
		return super.belongsTo(aFamily);
	}
}
