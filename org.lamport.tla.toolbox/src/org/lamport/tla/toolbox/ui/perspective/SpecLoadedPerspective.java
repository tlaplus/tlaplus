package org.lamport.tla.toolbox.ui.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.lamport.tla.toolbox.ui.provider.SpecExplorer;
import org.lamport.tla.toolbox.ui.view.ProblemView;

/**
 * Spec loaded perspective containing the editor and spec actions
 * @version $Id$
 * @author Simon Zambrovski
 */
public class SpecLoadedPerspective implements IPerspectiveFactory
{

    public final static String ID = "org.lamport.tla.toolbox.ui.perspective.specLoaded";

    // move
    // public final static String CONSOLE_VIEW_ID = "org.eclipse.ui.console.ConsoleView";
    

    public void createInitialLayout(IPageLayout layout)
    {
        layout.setEditorAreaVisible(true);
        String editorArea = layout.getEditorArea();
        
        layout.addPlaceholder(ProblemView.ID, IPageLayout.RIGHT, 0.75f, editorArea);
        // even if there is no dependency to the console plugin, we specify the possible location of the console
        // this might be useful for tools
        // layout.addPlaceholder(CONSOLE_VIEW_ID, IPageLayout.BOTTOM, 0.75f, editorArea);
        layout.addFastView(SpecExplorer.VIEW_ID, 0.25f);
        layout.getViewLayout(SpecExplorer.VIEW_ID).setCloseable(false);
    }
}
