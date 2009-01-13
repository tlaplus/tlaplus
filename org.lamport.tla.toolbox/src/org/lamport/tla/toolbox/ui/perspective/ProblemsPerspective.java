package org.lamport.tla.toolbox.ui.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.lamport.tla.toolbox.ui.view.ProblemView;

/**
 * The "perspective" that is used to show the problem view in a spearate window
 * 
 * @author zambrovski
 */
public class ProblemsPerspective implements IPerspectiveFactory
{

    public static final String ID = "org.lamport.tla.toolbox.ui.perspective.problems";

    public void createInitialLayout(IPageLayout layout)
    {
        layout.setEditorAreaVisible(false);
        String editorArea = layout.getEditorArea();
        layout.addStandaloneView(ProblemView.ID, false, IPageLayout.LEFT, 0.5f, editorArea);
        layout.addStandaloneView("org.eclipse.ui.views.ProblemView", false, IPageLayout.BOTTOM, 0.75f, ProblemView.ID);
        layout.getViewLayout(ProblemView.ID).setCloseable(false);
    }
}
