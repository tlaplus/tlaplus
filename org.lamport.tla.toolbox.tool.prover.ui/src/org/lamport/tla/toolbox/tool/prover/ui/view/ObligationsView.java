package org.lamport.tla.toolbox.tool.prover.ui.view;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;

public class ObligationsView extends ViewPart
{

    public static final String VIEW_ID = "org.lamport.tla.toolbox.tool.prover.ui.rejectedObligations";

    public ObligationsView()
    {
    }

    public void createPartControl(Composite parent)
    {
        /*
         * TODO:
         * 
         * 1.) Create control.
         * 2.) Attach context help to control.
         * 3.) Fill control with data.
         */

        fillData(Activator.getSpecManager().getSpecLoaded());
    }

    private void fillData(Spec specLoaded)
    {

    }

    public void setFocus()
    {
        /*
         * Set focus on appropriate control to which
         * context help is attached.
         */
    }

}
