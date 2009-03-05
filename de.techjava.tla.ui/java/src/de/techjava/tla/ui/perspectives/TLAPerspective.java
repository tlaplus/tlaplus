package de.techjava.tla.ui.perspectives;

import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

/**
 * TLA+ Perspective
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAPerspective.java,v 1.1 2005/08/22 15:43:38 szambrovski Exp $
 */
public class TLAPerspective 
	implements IPerspectiveFactory 
{
    /**
     * @see org.eclipse.ui.IPerspectiveFactory#createInitialLayout(org.eclipse.ui.IPageLayout)
     */
    public void createInitialLayout(IPageLayout layout) 
    {
        defineActions(layout);
        defineLayout(layout);
    }

    /**
     * Defines the initial actions for a page.  
     */
    public void defineActions(IPageLayout layout) 
    {
    	// Add "new wizards".
    	layout.addNewWizardShortcut("org.eclipse.ui.wizards.new.folder");
    	layout.addNewWizardShortcut("org.eclipse.ui.wizards.new.file");
    	layout.addNewWizardShortcut("de.techjava.tla.ui.wizards.TLANewProjectWizard");
    	layout.addNewWizardShortcut("de.techjava.tla.ui.wizards.TLANewFileWizard");
    	
    	

    	// Add "show views".
    	layout.addShowViewShortcut(IPageLayout.ID_RES_NAV);
    	layout.addShowViewShortcut(IPageLayout.ID_BOOKMARKS);
    	layout.addShowViewShortcut(IPageLayout.ID_OUTLINE);
    	layout.addShowViewShortcut(IPageLayout.ID_PROP_SHEET);
    	layout.addShowViewShortcut(IPageLayout.ID_PROBLEM_VIEW);
    	layout.addShowViewShortcut(IPageLayout.ID_TASK_LIST);
    	
    	layout.addActionSet(IPageLayout.ID_NAVIGATE_ACTION_SET);
    }
    /**
     * Defines the initial layout for a page.  
     */
    public void defineLayout(IPageLayout layout) 
    {
    	// Editors are placed for free.
    	String editorArea = layout.getEditorArea();

    	// Top left.
    	IFolderLayout topLeft = layout.createFolder("topLeft", IPageLayout.LEFT, (float)0.25, editorArea);
    	topLeft.addView(IPageLayout.ID_RES_NAV);
    	topLeft.addPlaceholder(IPageLayout.ID_BOOKMARKS);

    	// Bottom left.
    	IFolderLayout bottomLeft = layout.createFolder("bottomLeft", IPageLayout.BOTTOM, (float)0.50, "topLeft");
    	bottomLeft.addView(IPageLayout.ID_OUTLINE);

    	// Bottom right.
    	layout.addView(IPageLayout.ID_TASK_LIST, IPageLayout.BOTTOM, (float)0.66, editorArea);
    }
    
}

/*
 * $Log: TLAPerspective.java,v $
 * Revision 1.1  2005/08/22 15:43:38  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/13 10:50:56  bgr
 * ids changed
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 *
 */