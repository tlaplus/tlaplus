package org.lamport.tla.toolbox.tool.tlc.ui;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.eclipse.ui.console.IConsoleConstants;

public class TLCPerspective implements IPerspectiveFactory
{

    public void createInitialLayout(IPageLayout layout)
    {
        layout.setEditorAreaVisible(true);
        String editorArea = layout.getEditorArea();
        layout.addPlaceholder(IConsoleConstants.ID_CONSOLE_VIEW, IPageLayout.RIGHT, 0.75f, editorArea);
    }

}
