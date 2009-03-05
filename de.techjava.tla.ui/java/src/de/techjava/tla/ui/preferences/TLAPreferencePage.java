package de.techjava.tla.ui.preferences;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.util.ITLAProjectConstants;
import de.techjava.tla.ui.widgets.ProjectLayoutComposite;

/**
 * TLA Preferences
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAPreferencePage.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class TLAPreferencePage 
	extends PreferencePage
	implements IWorkbenchPreferencePage 
{
    private ProjectLayoutComposite projectLayoutComposite;
    /**
     * Constructs the preference page
     */
    public TLAPreferencePage()
    {
		setDescription("TLA+ Preferences");
    }
    /**
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(IWorkbench workbench) 
    {
		setPreferenceStore(UIPlugin.getDefault().getPreferenceStore());
    }
	/**
	 * @see org.eclipse.jface.preference.IPreferencePage#performOk()
	 */
    public boolean performOk() 
    {
        IPreferenceStore store = UIPlugin.getDefault().getPreferenceStore();
        store.setValue(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED, this.projectLayoutComposite.isProjectLayoutSeparated());
        store.setValue(ITLAProjectConstants.TLA_PROJECT_LAYOUT_WORKINGDIR, this.projectLayoutComposite.getWorkingFolder());
        store.setValue(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_CONFIGDIR, this.projectLayoutComposite.getConfigFolder());
        store.setValue(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_SOURCEDIR, this.projectLayoutComposite.getSourceFolder());
        return true;
    }
    /**
     * @see org.eclipse.jface.preference.PreferencePage#performDefaults()
     */
    protected void performDefaults() 
	{

	    IPreferenceStore store = UIPlugin.getDefault().getPreferenceStore();
	    this.projectLayoutComposite.setSourceFolder(store.getDefaultString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_SOURCEDIR));
	    this.projectLayoutComposite.setConfigFolder(store.getDefaultString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_CONFIGDIR));
	    this.projectLayoutComposite.setWorkingFolder(store.getDefaultString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_WORKINGDIR));
		this.projectLayoutComposite.setProjectLayout(store.getDefaultBoolean(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED)); 
	}

    private void initValues()
	{
	    IPreferenceStore store = UIPlugin.getDefault().getPreferenceStore();
	    this.projectLayoutComposite.setSourceFolder(store.getString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_SOURCEDIR));
	    this.projectLayoutComposite.setConfigFolder(store.getString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_CONFIGDIR));
	    this.projectLayoutComposite.setWorkingFolder(store.getString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_WORKINGDIR));
		this.projectLayoutComposite.setProjectLayout(store.getBoolean(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED)); 
	}
	/**
     * @see org.eclipse.jface.preference.PreferencePage#createContents(org.eclipse.swt.widgets.Composite)
     */
    protected Control createContents(Composite parent) 
    {
        Composite main = new Composite(parent, SWT.NULL);
        main.setLayout(new GridLayout());
        
        this.projectLayoutComposite = new ProjectLayoutComposite(main);
        initValues();
        
		return main;
    }
}

/*
 * $Log: TLAPreferencePage.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.3  2004/10/15 01:16:53  sza
 * working directory added
 *
 * Revision 1.2  2004/10/13 14:44:49  sza
 * project storage
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:11  sza
 * additions
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */