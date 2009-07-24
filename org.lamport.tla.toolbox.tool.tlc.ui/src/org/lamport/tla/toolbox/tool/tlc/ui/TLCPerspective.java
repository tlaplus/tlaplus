package org.lamport.tla.toolbox.tool.tlc.ui;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

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
    }
}
