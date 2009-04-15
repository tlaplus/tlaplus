package org.lamport.tla.toolbox.ui.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.lamport.tla.toolbox.ui.view.ProblemView;

/**
 * Spec loaded perspective containing the editor and spec actions
 * @version $Id$
 * @author Simon Zambrovski
 */
public class SpecLoadedPerspective implements IPerspectiveFactory
{

    public final static String ID = "org.lamport.tla.toolbox.ui.perspective.specLoaded";

    public void createInitialLayout(IPageLayout layout)
    {
        layout.setEditorAreaVisible(true);
        String editorArea = layout.getEditorArea();
        
        layout.addPlaceholder(ProblemView.ID, IPageLayout.LEFT, 0.75f, editorArea);
        
    }
}
