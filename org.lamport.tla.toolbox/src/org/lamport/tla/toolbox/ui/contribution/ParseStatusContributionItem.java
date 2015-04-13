package org.lamport.tla.toolbox.ui.contribution;

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
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A widget placed to the status line that shows the parse status of the root
 * module <br>
 * For additional help look at org.eclipse.ui.examples.contributions plugin
 * 
 * @author Simon Zambrovski
 * @version $Id: ParseStatusContributionItem.java 13736 2009-08-28 23:51:29Z
 *          lamport $
 */
public class ParseStatusContributionItem extends WorkbenchWindowControlContribution
{
    // the element
    private Composite composite;
    // label to display status
    private Label statusLabel;

    public ParseStatusContributionItem()
    {
        super("specParseStatusState");
        
        // Updates the Parse status widget on any spec operations
        Activator.getSpecManager().addSpecLifecycleParticipant(new SpecLifecycleParticipant() {
			
			/* (non-Javadoc)
			 * @see org.lamport.tla.toolbox.tool.SpecLifecycleParticipant#eventOccured(org.lamport.tla.toolbox.tool.SpecEvent)
			 */
			public boolean eventOccured(SpecEvent event) {
				ParseStatusContributionItem.this.updateStatus();
				return true;
			}
		});
    }

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
        layout.marginWidth = 2;
        composite.setLayout(layout);

        // label informing the user that this reflects the parse status of the spec
        Label description = new Label(composite, SWT.NONE);
        description.setText("Spec Status : ");
        description.setSize(70, 20);

        // Create label inside composite.
        statusLabel = new Label(composite, SWT.BORDER | SWT.CENTER);
        statusLabel.setToolTipText("Specification Parse Status");
        statusLabel.setSize(100, 20);

        // update status
        updateStatus();
        return composite;
    }

    // Updates status from the specification currently loaded in the SpecManager
	public void updateStatus() {
		if (statusLabel == null || statusLabel.isDisposed()) {
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
						} else if(!statusLabel.isDisposed() && !composite.isDisposed()) {
							statusLabel.setText(AdapterFactory.getStatusAsString(spec));
							statusLabel.setBackground(statusLabel.getDisplay().getSystemColor(AdapterFactory.getStatusAsSWTBGColor(spec)));
							statusLabel.setForeground(statusLabel.getDisplay().getSystemColor(AdapterFactory.getStatusAsSWTFGColor(spec)));
							statusLabel.redraw();
							composite.setVisible(true);
						}
					}
				});
				return Status.OK_STATUS;
			}
		};
		j.schedule();
	}
	
    public void update()
    {
        updateStatus();
    }

    protected int computeWidth(Control control)
    {
        return 170;
    }

}

