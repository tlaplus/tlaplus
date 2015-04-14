/**
 * 
 */
package org.lamport.tla.toolbox.ui.contribution;

import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.menus.WorkbenchWindowControlContribution;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.ToolboxDirectoryVisitor;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * @author lamport
 *
 */
public class SizeControlContribution extends WorkbenchWindowControlContribution implements IResourceChangeListener
{
    // the element
    private Composite composite;
    // label to display status
    private Label sizeLabel;

    /**
     * 
     */
    public SizeControlContribution()
    {
        // We have no idea what this string does.
        // The corresponding one for ParseStatusContributionItem
        // does not appear elsewhere in the code.
        super("specDirectorySize");
        
		// Register a listener to find any changed .toobox directories of specs.
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this, IResourceChangeEvent.POST_CHANGE);
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.action.ControlContribution#createControl(org.eclipse.swt.widgets.Composite)
     */
    protected Control createControl(Composite parent)
    {
        // If the composite is good just return it.
        if (composite != null && !composite.isDisposed())
        {
            return composite;
        }

        // Create a composite to place the label in
        composite = new Composite(parent, SWT.NONE);
        // composite.setData(this);

        // Give some room around the control
        FillLayout layout = new FillLayout();
        layout.marginHeight = 2;
        layout.marginWidth = 20;
        composite.setLayout(layout);

        // label informing the user that this reflects the parse status of the spec
        Label description = new Label(composite, SWT.NONE);
        description.setText("Storage (KB): ");
        description.setSize(50, 20);
        // description.setBackground(description.getDisplay().getSystemColor(SWT.COLOR_YELLOW));

        // Create label inside composite.
        sizeLabel = new Label(composite, SWT.BORDER | SWT.CENTER);
        sizeLabel.setText("n/a");
        sizeLabel.setToolTipText("Size of .toolbox directory");
        sizeLabel.setSize(100, 20);
        sizeLabel.setBackground(description.getDisplay().getSystemColor(SWT.COLOR_YELLOW));
        // update status
        updateSize();
        return composite;
    }

    // Updates status from the specification currently loaded in the SpecManager
	public void updateSize() {
		if (sizeLabel == null || sizeLabel.isDisposed()) {
			return;
		}

		final Job j = new ToolboxJob("Calculating specification size...") {
			/* (non-Javadoc)
			 * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
			 */
			protected IStatus run(IProgressMonitor monitor) {
				final Spec spec = Activator.getSpecManager().getSpecLoaded();

				UIHelper.runUIAsync(new Runnable() {
					/* (non-Javadoc)
					 * @see java.lang.Runnable#run()
					 */
					public void run() {
						if (spec == null && !composite.isDisposed()) {
							composite.setVisible(false);
						} else if (!sizeLabel.isDisposed() && !composite.isDisposed()) {
							final IPreferenceStore preferenceStore = PreferenceStoreHelper.getProjectPreferenceStore(spec
									.getProject());
							final String size = preferenceStore.getString(IPreferenceConstants.P_PROJECT_TOOLBOX_DIR_SIZE);
							sizeLabel.setText(size);

							// Make invisible if less than the
							// I_MIN_DISPLAYED_SIZE
							// preference.
							if (Long.parseLong(size) < Activator.getDefault().getPreferenceStore()
									.getInt(IPreferenceConstants.I_MIN_DISPLAYED_SIZE)) {
								composite.setVisible(false);
								return;
							}
							// sizeLabel.setBackground(sizeLabel.getDisplay().getSystemColor(AdapterFactory.getStatusAsSWTBGColor(spec)));
							// sizeLabel.setForeground(sizeLabel.getDisplay().getSystemColor(AdapterFactory.getStatusAsSWTFGColor(spec)));
							sizeLabel.redraw();
							composite.setVisible(true);
						}
					}
				});
				return Status.OK_STATUS;
			}
		};
		j.schedule();
	}

	public void resourceChanged(final IResourceChangeEvent event) {
		UIHelper.runUIAsync(new Runnable() {
			public void run() {
				final IResourceDelta delta = event.getDelta();
				if (delta != null) {
					try {
						// We cannot get the spec manager if it has not been
						// instantiated
						// because this would trigger a resource change event,
						// and this code
						// is being called within a resourceChanged method. Such
						// an
						// infinite loop is not allowed.
						if (Activator.isSpecManagerInstantiated()) {
							// delta.accept calls the visit method of the
							// visitor
							// on the delta.
							final ToolboxDirectoryVisitor toolboxDirectoryFinder = new ToolboxDirectoryVisitor();
							delta.accept(toolboxDirectoryFinder);
							List<IProject> directories = toolboxDirectoryFinder.getDirectories();
							// Set resource to the IResource representing a
							// project for a spec. This resource is embodied in
							// the file system as the spec's .toolbox director.
							for (Iterator<IProject> it = directories.iterator(); it.hasNext();) {
								IProject resource = it.next();
								ResourceHelper.setToolboxDirSize(resource);

								// TO-DO: If this is the currently opened spec,
								// change display of
								// that spec's size.
								Spec curSpec = ToolboxHandle.getCurrentSpec();
								if ((curSpec != null) && curSpec.getProject().equals(resource)) {
									SizeControlContribution.this.updateSize();
								}
							}
						}
					} catch (CoreException e) {
						Activator.getDefault().logError("Error during post save status update", e);
					}
				}
			}
		});
	}
}
