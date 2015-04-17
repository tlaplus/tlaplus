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
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.menus.WorkbenchWindowControlContribution;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.ToolboxDirectoryVisitor;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;

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
		// E.g. when the model checker is running for a long time, the size
		// should be shown eventually.
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this, IResourceChangeEvent.POST_CHANGE);
		
		// Register for Spec events like open, close, delete... to change
		// visibility of composite accordingly.
		Activator.getSpecManager().addSpecLifecycleParticipant(new SpecLifecycleParticipant() {
			/* (non-Javadoc)
			 * @see org.lamport.tla.toolbox.tool.SpecLifecycleParticipant#eventOccured(org.lamport.tla.toolbox.tool.SpecEvent)
			 */
			public boolean eventOccured(final SpecEvent event) {
				if (event.getType() == SpecEvent.TYPE_CLOSE || event.getType() == SpecEvent.TYPE_DELETE) {
					// SpecEvents don't give a guarantee that they are fired
					// from inside the UI thread.
					UIHelper.runUISync(new Runnable() {
						public void run() {
							composite.setVisible(false);
						}
					});
					return false;
				} else if (event.getType() == SpecEvent.TYPE_OPEN || event.getType() == SpecEvent.TYPE_OPEN) {
					final Job job = new ToolboxJob("Calculating spec size...") {
						protected IStatus run(IProgressMonitor monitor) {
							// TO-DO: If this is the currently opened spec,
							// change display of that spec's size.
							final Spec spec = event.getSpec();
							final long specSize = ResourceHelper
									.getSizeOfJavaFileResource(event.getSpec().getProject());
							spec.setSize(specSize);
							updateSize(specSize);
							return Status.OK_STATUS;
						}
					};
					job.schedule();
				}
				return true;
			}
		});
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
        composite.setVisible(false);
        return composite;
    }

    // Updates status from the specification currently loaded in the SpecManager
	private void updateSize(final long size) {
		if (sizeLabel == null || sizeLabel.isDisposed()) {
			return;
		}
		UIHelper.runUIAsync(new Runnable() {
			public void run() {
				if (!composite.isDisposed()) {
					composite.setVisible(false);
				}

				if (!sizeLabel.isDisposed() && !composite.isDisposed()) {
					sizeLabel.setText(Long.toString(size / 1000L)); // convert to KB

					// Make invisible if less than the
					// I_MIN_DISPLAYED_SIZE preference.
					// Size calculated is in bytes, preference in kilobytes.
					if ((size / 1000L) < Activator.getDefault().getPreferenceStore()
							.getInt(IPreferenceConstants.I_MIN_DISPLAYED_SIZE)) {
						composite.setVisible(false);
						return;
					}
					sizeLabel.redraw();
					composite.setVisible(true);
				}
			}
		});
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.IResourceChangeListener#resourceChanged(org.eclipse.core.resources.IResourceChangeEvent)
	 */
	public void resourceChanged(final IResourceChangeEvent event) {
		final IResourceDelta delta = event.getDelta();
		if (delta != null) {
			try {
				// We cannot get the spec manager if it has not been
				// instantiated because this would trigger a resource change
				// event, and this code is being called within a resourceChanged
				// method. Such an infinite loop is not allowed.
				if (Activator.isSpecManagerInstantiated()) {
					// delta.accept calls the visit method of the
					// visitor on the delta.
					final ToolboxDirectoryVisitor toolboxDirectoryFinder = new ToolboxDirectoryVisitor();
					delta.accept(toolboxDirectoryFinder);
					final List<IProject> directories = toolboxDirectoryFinder.getDirectories();
					// Set resource to the IResource representing a
					// project for a spec. This resource is embodied in
					// the file system as the spec's .toolbox director.
					for (Iterator<IProject> it = directories.iterator(); it.hasNext();) {
						final IProject resource = it.next();
						final long specSize = ResourceHelper.getSizeOfJavaFileResource(resource);

						// TO-DO: If this is the currently opened spec,
						// change display of that spec's size.
						final Spec curSpec = ToolboxHandle.getCurrentSpec();
						if (curSpec != null) {
							curSpec.setSize(specSize);
							if (curSpec.getProject().equals(resource)) {
								updateSize(specSize);
							}
						}
					}
				}
			} catch (CoreException e) {
				Activator.getDefault().logError("Error during post save status update", e);
			}
		}
	}
}
