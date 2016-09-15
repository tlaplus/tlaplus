package org.lamport.tla.toolbox.editor.basic.util;

import org.eclipse.core.runtime.IProgressMonitor;

public class ProgressMonitorDecorator implements IProgressMonitor {
	private final IProgressMonitor pm;
	
	public ProgressMonitorDecorator(IProgressMonitor pm) {
		this.pm = pm;
	}

	public void beginTask(String name, int totalWork) {
		pm.beginTask(name, totalWork);
	}

	public void done() {
		pm.done();
	}

	public void internalWorked(double work) {
		pm.internalWorked(work);
	}

	public boolean isCanceled() {
		return pm.isCanceled();
	}

	public void setCanceled(boolean value) {
		pm.setCanceled(value);
	}

	public void setTaskName(String name) {
		pm.setTaskName(name);
	}

	public void subTask(String name) {
		pm.subTask(name);
	}

	public void worked(int work) {
		pm.worked(work);
	}
}
