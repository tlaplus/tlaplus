package org.lamport.tla.toolbox.ui.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.lamport.tla.toolbox.ui.provider.SpecExplorer;

/**
 * The initial perspective with actions for the spec manager and the welcome view
 * 
 * @author zambrovski
 */
public class InitialPerspective implements IPerspectiveFactory
{

    /**
     * TODO refactor
     */
    public static final String INTRO_VIEW_ID = "org.eclipse.ui.internal.introview";
    public static final String ID = "org.lamport.tla.toolbox.ui.perspective.initial";

    public void createInitialLayout(IPageLayout layout)
    {
        String editorArea = layout.getEditorArea();
        layout.setEditorAreaVisible(false);
        layout.addStandaloneView(INTRO_VIEW_ID, false, IPageLayout.LEFT, 0.9f, editorArea);
        layout.getViewLayout(INTRO_VIEW_ID).setCloseable(false);
        
        layout.addFastView(SpecExplorer.VIEW_ID, 0.25f);
        layout.getViewLayout(SpecExplorer.VIEW_ID).setCloseable(false);
    }
}
