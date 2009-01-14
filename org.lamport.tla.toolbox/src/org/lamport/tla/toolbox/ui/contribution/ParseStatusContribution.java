package org.lamport.tla.toolbox.ui.contribution;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.menus.WorkbenchWindowControlContribution;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.IParseResultListner;
import org.lamport.tla.toolbox.util.AdapterFactory;

/**
 * A widget placed to the status line that shows the parse status of the root module 
 * @version $Id$
 * @author zambrovski
 */
public class ParseStatusContribution extends WorkbenchWindowControlContribution implements IParseResultListner
{
    private Label statusLabel = null;

    public ParseStatusContribution()
    {
        Activator.getParserRegistry().addParseResultListener(this);
    }

    public ParseStatusContribution(String id)
    {
        super(id);
        Activator.getParserRegistry().addParseResultListener(this);
    }

    protected Control createControl(Composite parent)
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

        parseResultChanged(IParseConstants.UNKNOWN);
        
        return comp;

    }

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.parser.IParseResultListner#parseResultChanged(int)
     */
    public void parseResultChanged(int parseStatus)
    {
        if (statusLabel != null && !statusLabel.isDisposed())
        {
            Spec spec = Activator.getSpecManager().getSpecLoaded();
            statusLabel.setText(AdapterFactory.getStatusAsString(spec));
            statusLabel.setBackground(statusLabel.getDisplay().getSystemColor(AdapterFactory.getStatusAsSWTColor(spec)));
            statusLabel.redraw();
        }
    }

}
