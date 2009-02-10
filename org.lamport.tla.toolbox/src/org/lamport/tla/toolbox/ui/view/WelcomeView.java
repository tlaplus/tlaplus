package org.lamport.tla.toolbox.ui.view;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Th welcome view
 * @author Simon Zambrovski
 * @version $Id$
 */
public class WelcomeView extends ViewPart
{

    public static final String ID = "toolbox.view.WelcomeView";

    public void createPartControl(Composite parent)
    {
        Composite top = new Composite(parent, SWT.NONE);
        GridLayout layout = new GridLayout();
        layout.marginHeight = 0;
        layout.marginWidth = 0;
        top.setLayout(layout);
        // message contents
        Text text = new Text(top, SWT.MULTI | SWT.WRAP);
        text.setLayoutData(new GridData(GridData.FILL_BOTH));
        UIHelper.setHelp(top, "WelcomeView");
        showInfo(text);
    }

    /**
     * @param text
     */
    private void showInfo(Text text)
    {
        text.setText("Welcome to the TLA Toolbox\n" + "Version 0.2 of 25 October 2008\n\n" +
        "Don't forget to click on help.  You can\n" + "learn about features that you never knew\n"
                + "about or have forgotten.");
    }

    public void setFocus()
    {
    }
}
