package org.lamport.tla.toolbox.ui.contribution;

import org.eclipse.jface.action.ContributionItem;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.AdapterFactory;

/**
 * A widget placed to the status line that shows the parse status of the root module 
 * @version $Id$
 * @author Simon Zambrovski
 */
public class ParseStatusContributionItem extends ContributionItem
{
    private Label statusLabel = null;

    public ParseStatusContributionItem()
    {

    }

    public ParseStatusContributionItem(String id)
    {
        super(id);
    }
    /**
     * Creates the control 
     */
    public void fill(Composite parent)
    {
        // Create a composite to place the label in
        Composite comp = new Composite(parent, SWT.NONE);

        // Give some room around the control
        FillLayout layout = new FillLayout();
        layout.marginHeight = 2;
        layout.marginWidth = 2;
        comp.setLayout(layout);

        // Create a label for the trim.
        statusLabel = new Label(comp, SWT.BORDER | SWT.CENTER);
        statusLabel.setForeground(parent.getDisplay().getSystemColor(SWT.COLOR_BLACK));
        statusLabel.setToolTipText("Parse status");
        
        // display status
        this.updateStatus();
    }


    /**
     * Updates status from the specification currently loaded in the SpecManager
     */
    public void updateStatus()
    {
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec == null) 
        {
            return;
        }
        statusLabel.setText(AdapterFactory.getStatusAsString(spec));
        statusLabel.setBackground(statusLabel.getDisplay().getSystemColor(AdapterFactory.getStatusAsSWTBGColor(spec)));
        statusLabel.setForeground(statusLabel.getDisplay().getSystemColor(AdapterFactory.getStatusAsSWTFGColor(spec)));
        statusLabel.redraw();
    }
}
