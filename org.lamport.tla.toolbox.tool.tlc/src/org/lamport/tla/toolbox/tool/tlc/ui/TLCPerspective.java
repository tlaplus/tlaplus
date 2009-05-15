package org.lamport.tla.toolbox.tool.tlc.ui;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.eclipse.ui.console.IConsoleConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.ui.ModelExplorer;
import org.lamport.tla.toolbox.ui.provider.SpecExplorer;
import org.lamport.tla.toolbox.ui.view.ProblemView;

/**
 * Perspective for TLC tool
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCPerspective implements IPerspectiveFactory
{

    /**
     * Perspective ID
     */
    public static final String ID = "org.lamport.tla.toolbox.tool.perspective.tlc";

    public void createInitialLayout(IPageLayout layout)
    {
        layout.setEditorAreaVisible(true);
        String editorArea = layout.getEditorArea();
        
        layout.addPlaceholder(ProblemView.ID, IPageLayout.RIGHT, 0.75f, editorArea);
        
        layout.addFastView(SpecExplorer.VIEW_ID, 0.25f);
        layout.getViewLayout(SpecExplorer.VIEW_ID).setCloseable(false);

        layout.addFastView(ModelExplorer.VIEW_ID, 0.25f);
        layout.getViewLayout(ModelExplorer.VIEW_ID).setCloseable(false);
        
        layout.addPlaceholder(IConsoleConstants.ID_CONSOLE_VIEW, IPageLayout.BOTTOM, 0.75f, editorArea);
    }
}
