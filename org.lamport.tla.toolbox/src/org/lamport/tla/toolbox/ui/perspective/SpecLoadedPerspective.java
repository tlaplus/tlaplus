package org.lamport.tla.toolbox.ui.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

/**
 * Spec loaded perspective containing the editor and spec actions
 * 
 * @author zambrovski
 */
public class SpecLoadedPerspective implements IPerspectiveFactory
{

    public final static String ID = "org.lamport.tla.toolbox.ui.perspective.specLoaded";

    public void createInitialLayout(IPageLayout layout)
    {
        layout.setEditorAreaVisible(true);
    }
}
