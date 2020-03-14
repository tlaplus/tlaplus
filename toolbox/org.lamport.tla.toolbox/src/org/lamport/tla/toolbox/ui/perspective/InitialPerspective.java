package org.lamport.tla.toolbox.ui.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

/**
 * The initial perspective with actions for the spec manager and the welcome view
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class InitialPerspective implements IPerspectiveFactory
{

    public static final String ID = "org.lamport.tla.toolbox.ui.perspective.initial";

    public void createInitialLayout(IPageLayout layout)
    {
        layout.setEditorAreaVisible(false);
    }
}
