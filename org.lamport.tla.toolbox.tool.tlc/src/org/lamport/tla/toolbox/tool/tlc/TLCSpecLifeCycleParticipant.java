package org.lamport.tla.toolbox.tool.tlc;

import org.eclipse.core.runtime.jobs.Job;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
import org.lamport.tla.toolbox.tool.SpecRenameEvent;
import org.lamport.tla.toolbox.tool.tlc.model.TLCSpec;

/**
 * React on spec operations with cancellation of the corresponding processes  
 */
public class TLCSpecLifeCycleParticipant extends SpecLifecycleParticipant {

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.SpecLifecycleParticipant#eventOccured(org.lamport.tla.toolbox.tool.SpecEvent)
	 */
	public boolean eventOccured(SpecEvent event) {
		switch (event.getType()) {
		case SpecEvent.TYPE_CLOSE:
			cancelRunningJobs(event);
			break;
		case SpecEvent.TYPE_DELETE:
			cancelRunningJobs(event);
			break;
		case SpecEvent.TYPE_RENAME:
			cancelRunningJobs(event);

			// if a spec gets renamed, it corresponding models have to be
			// renamed to prevent models from becoming unusable
			final TLCSpec tlcSpec = event.getSpec().getAdapter(TLCSpec.class);
			tlcSpec.rename(((SpecRenameEvent) event).getNewSpec());

			break;
		default:
			break;
		}
		return true;
	}

	private void cancelRunningJobs(SpecEvent event) {
		final Job[] runningSpecJobs = Job.getJobManager().find(event.getSpec());
		for (int i = 0; i < runningSpecJobs.length; i++) {
			// send cancellations to all jobs...
			runningSpecJobs[i].cancel();
		}
	}
}
