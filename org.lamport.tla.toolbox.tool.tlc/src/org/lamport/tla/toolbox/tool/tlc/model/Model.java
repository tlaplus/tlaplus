/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

package org.lamport.tla.toolbox.tool.tlc.model;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;
import java.util.concurrent.CopyOnWriteArraySet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.filefilter.DirectoryFileFilter;
import org.apache.commons.io.filefilter.NotFileFilter;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceRuleFactory;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Model.StateChangeListener.ChangeEvent;
import org.lamport.tla.toolbox.tool.tlc.model.Model.StateChangeListener.ChangeEvent.State;
import org.lamport.tla.toolbox.tool.tlc.traceexplorer.SimpleTLCState;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.output.MP;

/**
 * This class represents a Toolbox Model that can be executed by TLC.
 */
public class Model implements IModelConfigurationConstants, IAdaptable {
	/**
     * Marker indicating an error in the model
     */
	private static final String TLC_MODEL_ERROR_MARKER = "org.lamport.tla.toolbox.tlc.modelErrorMarker";
    /**
     * boolean attribute indicating if the original trace of a model checking
     * run should be shown in the error view for that model
     */
	private static final String IS_ORIGINAL_TRACE_SHOWN = "isOriginalTraceShown";
    /**
     * marker on .launch file with boolean attribute modelIsRunning; only used for historic clean-ups as of 1.5.5
     */
	private static final String TLC_MODEL_IN_USE_MARKER = "org.lamport.tla.toolbox.tlc.modelMarker";
    /**
     * marker on .launch file, binary semantics
     */
    private static final String TLC_CRASHED_MARKER = "org.lamport.tla.toolbox.tlc.crashedModelMarker";
    /**
     * marker on .launch file, with boolean attribute isOriginalTraceShown
     */
    private static final String TRACE_EXPLORER_MARKER = "org.lamport.tla.toolbox.tlc.traceExplorerMarker";

    public static final String SPEC_MODEL_DELIM = "___";

	static String sanitizeName(String aModelName) {
		Assert.isNotNull(aModelName);
		if (aModelName.contains(SPEC_MODEL_DELIM)) {
			// Strip spec prefix
			aModelName = aModelName.split(SPEC_MODEL_DELIM)[1];
		}
		if (aModelName.endsWith(".launch")) {
			// Strip file name extension
			aModelName = aModelName.substring(0, aModelName.length() - ".launch".length());
		}
		return aModelName;
	}

	/**
	 * @param fullQualifiedModelName The full-qualified (includes the Spec name and separator too) name of the Model.
	 * @return A Model, iff a Model by the given name exists and <code>null</code> otherwise.
	 */
	public static Model getByName(final String modelName) {
		return TLCModelFactory.getByName(modelName);
	}
	       
	/**
	 * A {@link StateChangeListener} is notified when the running state of the model
	 * changes. There is no guarantee as to which thread is being used to send the
	 * notification. A {@link StateChangeListener} has subscribe and unsubscribe
	 * via {@link Model#add(StateChangeListener)} and {@link Model#remove(StateChangeListener)}.
	 */
	public static class StateChangeListener {

		public static class ChangeEvent {

			public enum State {
				RUNNING, NOT_RUNNING, DELETED;
				
				public boolean in(State ... states) {
					for (State state : states) {
						if (state == this) {
							return true;
						}
					}
					return false;
				}
			}

			private final State state;
			private final Model model;

			private ChangeEvent(Model model, State state) {
				this.model = model;
				this.state = state;
			}

			public State getState() {
				return state;
			}

			public Model getModel() {
				return model;
			}
		}

		/**
		 * @return true iff the listener should be unsubscribed from receiving future
		 *         events after it handled the event.
		 */
		public boolean handleChange(ChangeEvent event) {
			return false;
		}
	}

	private final Set<StateChangeListener> listeners = new CopyOnWriteArraySet<StateChangeListener>();
	private TLCSpec spec;
	private ILaunchConfiguration launchConfig;

	// transient fields
	/**
	 * The working copy is the temporary storage for pending model changes until
	 * they are saved. Upon save, the changes are merged back into launchConfig
	 * and the working copy is nulled.
	 * <p>
	 * A null workingCopy indicates that the model is *not* dirty/has no pending,
	 * unsaved changes.
	 */
	private ILaunchConfigurationWorkingCopy workingCopy;
	private ILaunch launch;
	
	/**
	 * Marker indicating the SANY Errors
	 */
	public static final String TLC_MODEL_ERROR_MARKER_SANY = "org.lamport.tla.toolbox.tlc.modelErrorSANY";

	/**
	 * Only supposed to be called by {@link TLCModelFactory}
	 */
	protected Model(ILaunchConfiguration launchConfig) {
		/*
		 * The only caller of this method should only ever be
		 * TLCModelFactory.getAdapter(Object, Class<T>). All others should use
		 * ILaunchConfiguration.getAdapter(Model.class).
		 */
		Assert.isNotNull(launchConfig);
		this.launchConfig = launchConfig;
	}
	
	public boolean add(StateChangeListener stateChangeListener) {
		return this.listeners.add(stateChangeListener);
	}

	public boolean remove(StateChangeListener stateChangeListener) {
		return this.listeners.remove(stateChangeListener);
	}

	private void notifyListener(final StateChangeListener.ChangeEvent event) {
		for (StateChangeListener scl : listeners) {
			if (scl.handleChange(event)) {
				// Listener wants to be deregistered as a listener.
				listeners.remove(scl);
			}
		}
	}
		       
	public TLCSpec getSpec() {
		if (this.spec == null) {
			final String launchName = this.launchConfig.getName();
			Assert.isTrue(launchName.contains(SPEC_MODEL_DELIM));
			
			final Spec spec = ToolboxHandle.getSpecByName(launchName.split(SPEC_MODEL_DELIM)[0]);
			Assert.isNotNull(spec, "Failed to lookup spec with name " + launchName.split(SPEC_MODEL_DELIM)[0]);
			
			this.spec = spec.getAdapter(TLCSpec.class);
		}
		return this.spec;
	}

	public Model copy(String newModelName) {
		newModelName = sanitizeName(newModelName);
		try {
			final ILaunchConfigurationWorkingCopy copy = this.launchConfig
					.copy(getSpec().getName() + SPEC_MODEL_DELIM + newModelName);
            copy.setAttribute(ModelHelper.MODEL_NAME, newModelName);
            return copy.doSave().getAdapter(Model.class);
		} catch (CoreException e) {
			TLCActivator.logError("Error cloning model.", e);
			return null;
		}
	}

	public void rename(String newModelName, IProgressMonitor monitor) throws CoreException {
		final Collection<Model> snapshots = getSnapshots();
		
		// Rename the model directory to the new name.
		final IFolder modelDir = getTargetDirectory();
		if (modelDir != null && modelDir.exists()) {
			final IPath src = modelDir.getFullPath();
			final String segment = src.lastSegment().replaceFirst(getName(), newModelName);
			final IPath dst = src.removeLastSegments(1).append(segment);
			modelDir.move(dst, true, monitor);
		}

		renameLaunch(getSpec(), sanitizeName(newModelName));
		
		for (Model snapshot : snapshots) {
			snapshot.rename(newModelName + snapshot.getSnapshotSuffix(), monitor);
		}
	}
	
	/**
	 * The {@link Model}'s parent {@link TLCSpec} has been renamed. Update the {@link Model} too.
	 * @param newSpecName
	 */
	void specRename(final Spec newSpec) {
		final Collection<Model> snapshots = getSnapshots();

		renameLaunch(newSpec, getName());
		// The spec's name has changed. Force a re-lookup of the instance with
		// the updated name.
		this.spec = null;
		
		for (Model snapshot : snapshots) {
			snapshot.specRename(newSpec);;
		}
	}

	private void renameLaunch(final Spec newSpec, String newModelName) {
		try {
			// create the model with the new name
			final ILaunchConfigurationWorkingCopy copy = this.launchConfig
					.copy(newSpec.getName() + SPEC_MODEL_DELIM + newModelName);
			copy.setAttribute(SPEC_NAME, newSpec.getName());
			copy.setAttribute(ModelHelper.MODEL_NAME, newModelName);
			copy.setContainer(newSpec.getProject());
			final ILaunchConfiguration renamed = copy.doSave();

			// delete the old model
			this.launchConfig.delete();
			this.launchConfig = renamed;
		} catch (CoreException e) {
			TLCActivator.logError("Error renaming model.", e);
		}
	}

	public String getName() {
		try {
			return this.launchConfig.getAttribute(ModelHelper.MODEL_NAME, (String) null);
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
			return null;
		}
	}

	public String getComments() {
		try {
			return this.launchConfig.getAttribute(IModelConfigurationConstants.MODEL_COMMENTS, "");
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
			return "";
		}
	}

	public boolean isRunning() {
		final ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
		final ILaunch[] launches = launchManager.getLaunches();
		for (int i = 0; i < launches.length; i++) {
			final ILaunch launch = launches[i];
			if (launch.getLaunchConfiguration() != null
					&& launch.getLaunchConfiguration().contentsEqual(this.launchConfig)) {
				if (!launch.isTerminated()) {
					return true;
				}
			}
		}
		return false;
	}
	
	public void setRunning(boolean isRunning) {
		if (isRunning) {
			// Clear the crashed marker. After all, the model is obviously
			// running now.
			recover();
		}
		notifyListener(new StateChangeListener.ChangeEvent(this, isRunning ? State.RUNNING : State.NOT_RUNNING));
	}

    /**
	 * Looks up if the model has a stale marker. The stale marker is installed
	 * when the TLC process crashed (terminated with exit code > 0).
	 */
	public boolean isStale() {
        final IFile resource = getFile();
		if (resource.exists()) {
			IMarker[] foundMarkers;
			try {
				foundMarkers = resource.findMarkers(TLC_CRASHED_MARKER, false, IResource.DEPTH_ZERO);
				if (foundMarkers.length > 0) {
					return true;
				} else {
					return false;
				}
			} catch (CoreException shouldNotHappen) {
				TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
			}
		}
		return false;
	}
	
	public void setStale() {
		try {
			getFile().createMarker(TLC_CRASHED_MARKER);
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
		}
	}

	/*
	 * Snapshot related methods.
	 */

    private static final String SNAP_SHOT = "_SnapShot_";
	static final String SNAPSHOT_REGEXP = SNAP_SHOT + "[0-9]*$";
	
	private String getSnapshotSuffix() {
		if (isSnapshot()) {
			final int idx = getName().lastIndexOf(SNAP_SHOT);
			return getName().substring(idx, getName().length());
		}
		return "";
	}
	
	public long getSnapshotTimeStamp() {
		final int idx = getName().lastIndexOf(SNAP_SHOT) + 10;
		return Long.valueOf(getName().substring(idx));
	}
	
	public Collection<Model> getSnapshots() {
		return getSpec().getModels(getName() + SNAPSHOT_REGEXP, true).values();
	}

	public boolean isSnapshot() {
		return getName().matches(".*" + SNAPSHOT_REGEXP);
	}

	public boolean hasSnapshots() {
		return !getSpec().getModels(getName() + SNAPSHOT_REGEXP, true).isEmpty();
	}

	public Model getSnapshotFor() {
		return getSpec().getModel(getName().replaceFirst(SNAPSHOT_REGEXP, ""));
	}

	public Model snapshot() throws CoreException {
		// Create a copy of the underlying launch configuration.
		final Model snapshot = copy(getName() + SNAP_SHOT + System.currentTimeMillis());

		// Snapshot the model's markers as well (e.g. the information about errors, see hasErrors()).
    	final IMarker[] markers = getMarkers();
    	for (IMarker iMarker : markers) {
    		snapshot.setMarker(iMarker.getAttributes(), iMarker.getType());
		}
		
    	// Set the snapshot to be locked? Do we want the user to be able to run it again?
//    	snapshot.setLocked(true);

		/*
		 * Snapshot (copy) the model folder which include the TLC output as well as the version
		 * of the spec and module overwrites with which TLC ran.
		 */
		final IPath snapshotPath = getSpec().getProject().getFolder(snapshot.getName()).getLocation();
		final IPath modelFolder = getSpec().getProject().getFolder(this.getName()).getLocation();
		// Use non-Eclipse API instead of modelFolder.copy(snapshotFolder, false,
		// monitor which supports a non-recursive copy. A recursive copy includes the
		// states/ directory leftover from TLC which waste quite some space and might
		// take some time to copy.
		try {
			FileUtils.copyDirectory(modelFolder.toFile(), snapshotPath.toFile(),
					new NotFileFilter(DirectoryFileFilter.DIRECTORY));
			                       
			// Rename .dot file name because hasStateGraphDump checks if a .dot file exists
			// that matches the name of the model.
			if (hasStateGraphDump()) {
				final IPath oldDotFile = getSpec().getProject()
						.getFolder(snapshot.getName() + File.separator + this.getName() + ".dot").getLocation();
				final IPath newDotFile = getSpec().getProject()
						.getFolder(snapshot.getName() + File.separator + snapshot.getName() + ".dot").getLocation();
				FileUtils.moveFile(oldDotFile.toFile(), newDotFile.toFile());
			}
			
			// Now that we've had a successful save, prune any snapshots, starting with the oldest, in order to assure the
			// cardinality no greater than snapshotKeepCount.
			pruneOldestSnapshots();
			
			// Refresh the snapshot folder after having copied files without using the
			// Eclipse resource API. Otherwise, the resource API does not see the files
			// which e.g. results in an incomplete model deletion or hasStateGraphDump
			// incorrectly returning false.
			snapshot.getFolder().refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
		} catch (IOException e) {
			throw new CoreException(new Status(Status.ERROR, TLCActivator.PLUGIN_ID, e.getMessage(), e));
		}
        
		return snapshot;
	}

	private void pruneOldestSnapshots() throws CoreException {
		// Sort model by snapshot timestamp and remove oldest ones.
		final int snapshotKeepCount = TLCActivator.getDefault().getPreferenceStore().getInt(TLCActivator.I_TLC_SNAPSHOT_KEEP_COUNT);
		final List<Model> snapshotModels = new ArrayList<>(getSnapshots());
		if (snapshotModels.size() > snapshotKeepCount) {
		    final int pruneCount = snapshotModels.size() - snapshotKeepCount;
		    Collections.sort(snapshotModels, new Comparator<Model>() {
		        public int compare (final Model model1, final Model model2) {
		        	final long ts1 = model1.getSnapshotTimeStamp();
		        	final long ts2 = model2.getSnapshotTimeStamp();
		        	return Long.compare(ts1, ts2);
		        }
		    });
		    for (int i = 0; i < pruneCount; i++) {
		        final Model model = snapshotModels.get(i);
		        model.delete(new NullProgressMonitor());
		    }
		}
	}

	/*
	 * End of snapshot related methods.
	 */
	
	/*
	 * State Graph dump in dot file format (GraphViz).
	 */

	private static final String DOT_FILE_EXT = ".dot";
	
	public boolean hasStateGraphDump() {
		final String name = getName().concat(DOT_FILE_EXT);
		// Convert to java.io.File rather than Eclipse's IFile. For the latter
		// file.exists might return null if Eclipse's internal FS cache is stale.
		final File file = getFolder().getFile(name).getLocation().toFile();
		return file.exists();
	}

	public IFile getStateGraphDump() {
		final String name = getName().concat(DOT_FILE_EXT);
		return getFolder().getFile(name);
	}

	/*
	 * End of state graph dump related methods.
	 */	

	/**
     * Returns whether the original trace or the trace with trace explorer expressions from the
     * most recent run of the trace explorer for the model should be shown in the TLC error view.
     * 
     * See {@link ModelHelper#setOriginalTraceShown(ILaunchConfiguration, boolean)} for setting this
     * return value.
     * 
     * @return whether the original trace or the trace with trace explorer expressions from the
     * most recent run of the trace explorer for the model should be shown in the TLC error view
     */
    public boolean isOriginalTraceShown() {
    	return isMarkerSet(TRACE_EXPLORER_MARKER, IS_ORIGINAL_TRACE_SHOWN);
    }

    /**
     * Sets whether the original trace or the trace with trace explorer expressions
     * should be shown in the TLC error view for the model represented by this
     * configuration.
     * 
     * Code the raises the TLC error view or updates the TLC error view for a model
     * can use {@link ModelHelper#isOriginalTraceShown(ILaunchConfiguration)} to determine
     * if the original trace should be shown for a given model.
     * 
     * @param isOriginalTraceShown true if the original trace should be shown, false if
     * the trace with trace explorer expressions should be shown
     */
	public void setOriginalTraceShown(boolean isOriginalTraceShown) {
		setMarker(TRACE_EXPLORER_MARKER, IS_ORIGINAL_TRACE_SHOWN, isOriginalTraceShown);
	}

	public boolean hasError() {
		return getMarkers().length > 0;
	}

	private boolean isMarkerSet(String markerType, final String attributeName) {
		// marker
		final IFile resource = getFile();
		if (resource.exists()) {
			try {
				final IMarker[] foundMarkers = resource.findMarkers(markerType, false, IResource.DEPTH_ZERO);
				if (foundMarkers.length > 0) {
					boolean set = foundMarkers[0].getAttribute(attributeName, false);
					// remove trash if any
					for (int i = 1; i < foundMarkers.length; i++) {
						foundMarkers[i].delete();
					}
					return set;
				} else {
					return false;
				}
			} catch (CoreException shouldNotHappen) {
				TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
			}
		}
		return false;
	}
	
	private void setMarker(final String markerType, final String attributeName, boolean value) {
		final IFile resource = getFile();
		if (resource.exists()) {
			try {
				IMarker marker;
				final IMarker[] foundMarkers = resource.findMarkers(markerType, false, IResource.DEPTH_ZERO);
				if (foundMarkers.length > 0) {
					marker = foundMarkers[0];
					// remove trash if any
					for (int i = 1; i < foundMarkers.length; i++) {
						foundMarkers[i].delete();
					}
				} else {
					marker = resource.createMarker(markerType);
				}

				marker.setAttribute(attributeName, value);
			} catch (CoreException shouldNotHappen) {
				TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
			}
		}
	}

    /**
     * Installs a marker on the model
	 * @param properties a map of attribute names to attribute values 
	 *		(key type : <code>String</code> value type : <code>String</code>, 
	 *		<code>Integer</code>, or <code>Boolean</code>) or <code>null</code>
     */
	public IMarker setMarker(Map<String, Object> properties, String markerType) {
		try {
			IMarker marker = getFile().createMarker(markerType);
			marker.setAttributes(properties);
			return marker;
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
		}
		return null;
	}
	
	public IMarker[] getMarkers() {
		final IFile resource = getFile();
		if (resource.exists()) {
			try {
				return resource.findMarkers(TLC_MODEL_ERROR_MARKER, true, IResource.DEPTH_ZERO);
			} catch (CoreException shouldNotHappen) {
				TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
			}
		}
		return new IMarker[0];
	}

	public void removeMarkers(final String markerType) {
		try {
			final IMarker[] foundMarkers = getFile().findMarkers(markerType, true,
					IResource.DEPTH_ONE);
			for (int i = 0; i < foundMarkers.length; i++) {
				foundMarkers[i].delete();
			}
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
		}
	}

    /**
     * Tries to recover model after an abnormal TLC termination
     * It deletes all temporary files on disk and restores the state to unlocked.
     */
	public void recover() {
		final IFile resource = getFile();
		if (resource.exists()) {
			try {
				// remove any crashed markers
				IMarker[] foundMarkers = resource.findMarkers(TLC_CRASHED_MARKER, false, IResource.DEPTH_ZERO);
				if (foundMarkers.length == 0) {
					return;
				}
				
				for (int i = 0; i < foundMarkers.length; i++) {
					foundMarkers[i].delete();
				}
				
				foundMarkers = resource.findMarkers(TLC_MODEL_IN_USE_MARKER, false, IResource.DEPTH_ZERO);
				for (int i = 0; i < foundMarkers.length; i++) {
					foundMarkers[i].delete();
				}
			} catch (CoreException shouldNotHappen) {
				TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
			}
		}
	}

	public ILaunchConfiguration getLaunchConfiguration() {
		return this.launchConfig;
	}

	public void delete(IProgressMonitor monitor) throws CoreException {
		
		// First delete the Model's snapshots. If left undelete, they disappear from the
		// Toolbox have to be deleted manually.
		final Collection<Model> snapshots = getSnapshots();
		for (Model model : snapshots) {
			model.delete(SubMonitor.convert(monitor));
		}
		
		notifyListener(new ChangeEvent(this, State.DELETED));
		
		final IResource[] members;

		// if the model has never been model checked, no model folder will exist
		final IFolder modelFolder = getTargetDirectory();
		if(modelFolder != null) {
			members = new IResource[2];
			members[0] = modelFolder; // model folder
			members[1] = getLaunchConfiguration().getFile(); // modle launch config
		} else {
			members = new IResource[]{getLaunchConfiguration().getFile()};
		}
		
		// schedule combined deletion of both the model folder as well as the
		// launch config
		final ISchedulingRule deleteRule = ResourceHelper.getDeleteRule(members);

		ResourcesPlugin.getWorkspace().run(
				new IWorkspaceRunnable() {

					/* (non-Javadoc)
					 * @see org.eclipse.core.resources.IWorkspaceRunnable#run(org.eclipse.core.runtime.IProgressMonitor)
					 */
					public void run(IProgressMonitor subMonitor)
							throws CoreException {
						subMonitor.beginTask("Deleting files", members.length);

						// actually deletes all IResource members
						try {
							for (int i = 0; i < members.length; i++) {
								members[i].delete(IResource.FORCE,
										SubMonitor.convert(subMonitor, 1));
							}
						} catch (CoreException e) {
							TLCActivator.logError("Error deleting a file "
									+ e.getMessage(), e);
							throw e;
						}
						
						subMonitor.done();
					}
				}, deleteRule, IWorkspace.AVOID_UPDATE,
				SubMonitor.convert(monitor, members.length));
	}
	
    /**
	 * Retrieves the working directory for the model. Returns null if the model has
	 * not run yet. In other words, gets created by running TLC.<br>
	 * Note, this is a handle operation only, the resource returned may not exist
	 * 
	 * @param config
	 * @return the Folder.
	 * @see Model#getFolder()
	 */
	public IFolder getTargetDirectory() {
        return (IFolder) getSpec().getProject().findMember(getName());
	}

	/**
	 * Retrieves the TLA file that is being model checked on the model run
	 * 
	 * @param config
	 *            configuration representing the model
	 * @return a file handle or <code>null</code>
	 */
	public IFile getTLAFile() {
		return getFile(ModelHelper.FILE_TLA);
	}

	/**
	 * Retrieves the TE file that is being used by the trace explorer.
	 * 
	 * @param config
	 *            configuration representing the model
	 * @return a file handle or <code>null</code>
	 */
	public IFile getTEFile() {
		return getFile(ModelHelper.TE_FILE_TLA);
	}

	public IFile getOutputLogFile() {
		return getOutputLogFile(false);
	}
	
    /**
     * Retrieves a file where the log of the TLC run is written. If isTraceExploration is true, this
     * will return the log file for trace exploration. If that flag is false, this will return the log file
     * for normal model checking.
     * 
     * @param config configuration representing the model
     * @param getTraceExplorerOutput flag indicating if the log file for trace exploration is to be returned
     * @return the file handle, or null
     */
	public IFile getOutputLogFile(boolean getTraceExplorerOutput) {
		if (getTraceExplorerOutput) {
			return getFile(ModelHelper.TE_FILE_OUT);
		} else {
			return getFile(ModelHelper.FILE_OUT);
		}
	}

    /**
     * Retrieves the TLA file used by the trace explorer
     * @return a file handle or <code>null</code>
     */
	public IFile getTraceExplorerTLAFile() {
		return getFile(ModelHelper.TE_FILE_TLA);
	}
	
	private IFile getFile(final String id) {
		final IFolder targetFolder = getTargetDirectory();
		if (targetFolder != null && targetFolder.exists()) {
			final IFile teFile = (IFile) targetFolder.findMember(id);
			if (teFile != null && teFile.exists()) {
				return teFile;
			}
		}
		return null;
	}

    /**
     * Returns a handle to the output file {@link ModelHelper#TE_TRACE_SOURCE} used by the
     * trace explorer to retrieve the trace from the most recent run of TLC on
     * the config.
     * 
     * Note that this is a handle-only operation. The file need not exist in the
     * underlying file system.
     * 
     * @return
     */
	public IFile getTraceSourceFile() {
		final IFolder targetFolder = getTargetDirectory();
		if (targetFolder != null && targetFolder.exists()) {
			final IFile logFile = targetFolder.getFile(ModelHelper.TE_TRACE_SOURCE);
			Assert.isNotNull(logFile);
			return logFile;
		}
		return null;
	}

    public void createModelOutputLogFile(InputStream is, IProgressMonitor monitor) throws CoreException {
        IFolder targetFolder = getTargetDirectory();
		// Create targetFolder which might be missing if the model has never
		// been checked but the user wants to load TLC output anyway.
		// This happens with distributed TLC, where the model is executed
		// remotely and the log is send to the user afterwards.
        if (targetFolder == null || !targetFolder.exists()) {
            String modelName = getName();
    		targetFolder = getSpec().getProject().getFolder(modelName);
    		targetFolder.create(true, true, monitor);
        }
        if (targetFolder != null && targetFolder.exists())
        {
			// Always refresh the folder in case it has to override an existing
			// file that is out-of-sync with the Eclipse foundation layer.
        	targetFolder.refreshLocal(IFolder.DEPTH_INFINITE, monitor);
        	
        	// Import MC.out
        	IFile mcOutFile = targetFolder.getFile(ModelHelper.FILE_OUT);
        	if (mcOutFile.exists()) {
        		mcOutFile.delete(true, monitor);
        	}
        	mcOutFile.create(is, true, monitor); // create closes the InputStream is.
        	
        	// Import MC_TE.out by copying the MC.out file to MC_TE.out.
			// The reason why there are two identical files (MC.out and
			// MC_TE.out) has been lost in history.
        	IFile mcTEOutfile = targetFolder.getFile(ModelHelper.TE_TRACE_SOURCE);
        	if (mcTEOutfile.exists()) {
        		mcTEOutfile.delete(true, monitor);
        	}
        	mcOutFile.copy(mcTEOutfile.getFullPath(), true, monitor);
        }
    }
    

	public IFolder getFolder() {
		return getSpec().getProject().getFolder(getName());
	}

    private static final String CHECKPOINT_STATES = ModelHelper.MC_MODEL_NAME + ".st.chkpt";
    private static final String CHECKPOINT_QUEUE = "queue.chkpt";
    private static final String CHECKPOINT_VARS = "vars.chkpt";

    /**
     * Checks whether the checkpoint files exist for a given model
     * If doRefresh is set to true, this method will refresh the model directory,
     * and if a checkpoint folder is found, it will refresh the contents of that folder.
     * This means that the eclipse workspace representation of that directory will
     * synch with the file system. This is a long running job, so this method should not
     * be called within the running of another job unless the scheduling rule for
     * refreshing the model directory is included in the scheduling rule of the job which
     * is calling this method. This scheduling rule can be found by calling
     * 
     * Note: Because the Toolbox deletes any existing checkpoint when running TLC,
     * there should be at most one checkpoint.  Therefore, this method should return an array
     * of length 0 or 1.
     * 
     * {@link IResourceRuleFactory#refreshRule(IResource)}
     * @param config
     * @param doRefresh whether the model directory's contents and any checkpoint
     * folders contents should be refreshed
     * @return the array of checkpoint directories, sorted from last to first
     */
    public IResource[] getCheckpoints(boolean doRefresh) throws CoreException
    {
        // yy-MM-dd-HH-mm-ss
        Pattern pattern = Pattern.compile("[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}");

        Vector<IResource> checkpoints = new Vector<IResource>();
        IFolder directory = getTargetDirectory();

        if (directory != null && directory.exists())
        {
            // refreshing is necessary because TLC creates
            // the checkpoint folders, but they may not have
            // been incorporated into the toolbox workspace
            // yet
            // the depth is one to find any checkpoint folders
            if (doRefresh)
            {
                directory.refreshLocal(IResource.DEPTH_ONE, null);
            }
            IResource[] members = directory.members();
            for (int i = 0; i < members.length; i++)
            {
                if (members[i].getType() == IResource.FOLDER)
                {
                    Matcher matcher = pattern.matcher(members[i].getName());
                    if (matcher.matches())
                    {
                        // if there is a checkpoint folder, it is necessary
                        // to refresh its contents because they may not
                        // be part of the workspace yet
                        if (doRefresh)
                        {
                            members[i].refreshLocal(IResource.DEPTH_ONE, null);
                        }
                        if (((IFolder) members[i]).findMember(CHECKPOINT_QUEUE) != null
                                && ((IFolder) members[i]).findMember(CHECKPOINT_VARS) != null
                                && ((IFolder) members[i]).findMember(CHECKPOINT_STATES) != null)
                        {
                            checkpoints.add(members[i]);
                        }
                    }
                }
            }
        }
        IResource[] result = (IResource[]) checkpoints.toArray(new IResource[checkpoints.size()]);
        // sort the result
        Arrays.sort(result, new Comparator<IResource>() {
            public int compare(IResource arg0, IResource arg1)
            {
                return arg0.getName().compareTo(arg1.getName());
            }
        });

        return result;
    }

    private static final String CR = "\n";
    private static final String SPACE = " ";

    /**
     * Returns a possibly empty List of {@link SimpleTLCState} that represents
     * the error trace produced by the most recent run of TLC on config, if an error
     * trace was produced.
     */
    public List<SimpleTLCState> getErrorTrace()
    {
        /*
         * Use a file editor input and file document provider to gain access to the
         * document representation of the file containing the trace.
         */
        FileEditorInput logFileEditorInput = new FileEditorInput(getTraceSourceFile());
        FileDocumentProvider logFileDocumentProvider = new FileDocumentProvider();
        try
        {
            logFileDocumentProvider.connect(logFileEditorInput);
            IDocument logFileDocument = logFileDocumentProvider.getDocument(logFileEditorInput);

            FindReplaceDocumentAdapter logFileSearcher = new FindReplaceDocumentAdapter(logFileDocument);

            // the regular expression for searching for the start tag for state print outs
            String regExStartTag = MP.DELIM + MP.STARTMSG + "[0-9]{4}" + MP.COLON + MP.STATE + SPACE + MP.DELIM + CR;
            // the regular expression for searching for the end tag for state print outs
            String regExEndTag = MP.DELIM + MP.ENDMSG + "[0-9]{4}" + SPACE + MP.DELIM;

            IRegion startTagRegion = logFileSearcher.find(0, regExStartTag, true, true, false, true);

            // vector of SimpleTLCStates
            Vector<SimpleTLCState> trace = new Vector<SimpleTLCState>();

            while (startTagRegion != null)
            {
                IRegion endTagRegion = logFileSearcher.find(startTagRegion.getOffset() + startTagRegion.getLength(),
                        regExEndTag, true, true, false, true);

                if (endTagRegion != null)
                {
                    int stateInputStart = startTagRegion.getOffset() + startTagRegion.getLength();
                    int stateInputLength = endTagRegion.getOffset() - stateInputStart;
                    // string from which the state can be parsed
                    String stateInputString = logFileDocument.get(stateInputStart, stateInputLength);

                    trace.add(SimpleTLCState.parseSimpleTLCState(stateInputString));

                } else
                {
                    TLCActivator.logDebug("Found start tag region in model log file without end tag for model "
                            + getName() + ".");
                }
                // TLCActivator.getDefault().logDebug(logFileDocument.get(startTagRegion.getOffset() + startTagRegion.getLength(),
                // endTagRegion.getOffset() - startTagRegion.getLength() - startTagRegion.getOffset()));

                startTagRegion = logFileSearcher.find(startTagRegion.getOffset() + startTagRegion.getLength(),
                        regExStartTag, true, true, false, true);
            }

            return trace;
        } catch (CoreException e)
        {
            TLCActivator.logError("Error connecting to model log file for model " + getName() + ".", e);
        } catch (BadLocationException e)
        {
            TLCActivator.logError("Error searching model log file for " + getName() + ".", e);
        } finally
        {
            /*
             * The document provider is not needed. Always disconnect it to avoid a memory leak.
             * 
             * Keeping it connected only seems to provide synchronization of
             * the document with file changes. That is not necessary in this context.
             */
            logFileDocumentProvider.disconnect(logFileEditorInput);
        }

        return new Vector<SimpleTLCState>();
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
    	// The model's full-qualified name
    	return getSpec().getName() + SPEC_MODEL_DELIM + getName();
    }

	public List<String> getTraceExplorerExpressions() {
		final Vector<String> defaultValue = new Vector<String>();
		try {
			return this.launchConfig.getAttribute(IModelConfigurationConstants.TRACE_EXPLORE_EXPRESSIONS, defaultValue);
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
			return defaultValue;
		}
	}

	public void setTraceExplorerExpression(List<String> serializedInput) {
		// TODO Why is this written into a working copy? => One can only write
		// into a working copy, which is synced on save. Thus, make sure never
		// to write to different copies concurrently.
        try {
        	getWorkingCopy().setAttribute(IModelConfigurationConstants.TRACE_EXPLORE_EXPRESSIONS, serializedInput);
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
		}
	}

	public IFile getFile() {
		return getLaunchConfiguration().getFile();
	}

	/**
	 * @return The last {@link ILaunch} or <code>null</code> if {@link Model} has never been run.
	 */
	public ILaunch getLastLaunch() {
		return launch;
	}
	
	public void launch(String mode, IProgressMonitor subProgressMonitor, boolean build) throws CoreException {
		Assert.isTrue(this.workingCopy == null, "Cannot launch dirty model, save first.");
		this.launch = this.launchConfig.launch(mode, subProgressMonitor, build);
	}

	public Model save(final IProgressMonitor monitor) {
		if (this.workingCopy != null) {
			//TODO This is a workspace operation and thus should be decoupled from the UI thread.
			try {
				this.launchConfig = this.workingCopy.doSave();
				// Null the temporary working copy . Save effectively merges the
				// changes in the working copy back into the launch config.
				this.workingCopy = null;
			} catch (CoreException shouldNotHappen) {
				TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
			}
		}
		TLCActivator.logDebug("Trying to save a clean Model.");
		
		// Fluent
		return this;
	}
	
	private ILaunchConfigurationWorkingCopy getWorkingCopy() throws CoreException {
		if (this.workingCopy == null) {
			this.workingCopy = this.launchConfig.getWorkingCopy();
		}
		return this.workingCopy;
	}
	
	public void unsavedSetEvalExpression(final String expression) {
		setAttribute(MODEL_EXPRESSION_EVAL, expression);
	}

	public String getEvalExpression() {
		try {
			return this.launchConfig.getAttribute(MODEL_EXPRESSION_EVAL, "");
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
			return "";
		}
	}

	public int getAttribute(String key, int defaultValue) throws CoreException {
		// TODO Replace this generic lookup method with real getters for the
		// various keys. E.g. see getEvalExpression/unsavedSetEvalExpression
		return this.launchConfig.getAttribute(key, defaultValue);
	}

	public String getAttribute(String key, String defaultValue) throws CoreException {
		// TODO Replace this generic lookup method with real getters for the
		// various keys. E.g. see getEvalExpression/unsavedSetEvalExpression
		return this.launchConfig.getAttribute(key, defaultValue);
	}

	public boolean getAttribute(String key, boolean defaultValue) throws CoreException {
		// TODO Replace this generic lookup method with real getters for the
		// various keys. E.g. see getEvalExpression/unsavedSetEvalExpression
		return this.launchConfig.getAttribute(key, defaultValue);
	}

	public List<String> getAttribute(String key, List<String> defaultValue) throws CoreException {
		// TODO Replace this generic lookup method with real getters for the
		// various keys. E.g. see getEvalExpression/unsavedSetEvalExpression
		return this.launchConfig.getAttribute(key, defaultValue);
	}

	public void setAttribute(String key, int value) {
		// TODO Replace this generic lookup method with real getters for the
		// various keys. E.g. see getEvalExpression/unsavedSetEvalExpression
		try {
			getWorkingCopy().setAttribute(key, value);
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
		}
	}

	public void setAttribute(String key, String value) {
		// TODO Replace this generic lookup method with real getters for the
		// various keys. E.g. see getEvalExpression/unsavedSetEvalExpression
		try {
			getWorkingCopy().setAttribute(key, value);
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
		}
	}

	public void setAttribute(String key, boolean value) {
		// TODO Replace this generic lookup method with real getters for the
		// various keys. E.g. see getEvalExpression/unsavedSetEvalExpression
		try {
			getWorkingCopy().setAttribute(key, value);
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
		}
	}

	public void setAttribute(String key, List<String> value) {
		// TODO Replace this generic lookup method with real getters for the
		// various keys. E.g. see getEvalExpression/unsavedSetEvalExpression
		try {
			getWorkingCopy().setAttribute(key, value);
		} catch (CoreException shouldNotHappen) {
			TLCActivator.logError(shouldNotHappen.getMessage(), shouldNotHappen);
		}
	}
	
	/* IAdaptable */

	public <T> T getAdapter(Class<T> adapter) {
        return Platform.getAdapterManager().getAdapter(this, adapter);
	}
}
