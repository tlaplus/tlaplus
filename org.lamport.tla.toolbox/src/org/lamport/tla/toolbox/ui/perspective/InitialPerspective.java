package org.lamport.tla.toolbox.ui.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

/**
 * The initial perspective with actions for the spec manager and the welcome view
 * 
 * @author zambrovski
 */
public class InitialPerspective implements IPerspectiveFactory
{

    public static final String ID = "org.lamport.tla.toolbox.ui.perspective.initial";

    public void createInitialLayout(IPageLayout layout)
    {
        String editorArea = layout.getEditorArea();
        layout.setEditorAreaVisible(false);
        layout.addStandaloneView("org.eclipse.ui.internal.introview", false, IPageLayout.LEFT, 0.9f, editorArea);
        layout.getViewLayout("org.eclipse.ui.internal.introview").setCloseable(false);
        // layout.getViewLayout("org.eclipse.ui.internal.introview").setMoveable(false);
        /*
        layout.addStandaloneView(WelcomeView.ID, true, IPageLayout.LEFT, 0.5f, editorArea);
        layout.getViewLayout(WelcomeView.ID).setCloseable(true);
        */
        
        // layout.addStandaloneView("toolbox.view.Navigator", true, IPageLayout.RIGHT, 0.5f, editorArea);
    }
}
