package de.techjava.tla.ui.properties;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.dialogs.PropertyPage;
import org.osgi.service.prefs.BackingStoreException;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.natures.TLANature;
import de.techjava.tla.ui.util.ITLAProjectConstants;
import de.techjava.tla.ui.util.ProjectUtils;
import de.techjava.tla.ui.widgets.ProjectLayoutComposite;


public class TLAProjectProperties 
	extends PropertyPage 
{

    private IPreferenceStore 		store;
    private ProjectLayoutComposite 	projectLayoutComposite;
	/**
	 * Constructor.
	 */
	public TLAProjectProperties() 
	{
		super();
		store = UIPlugin.getDefault().getPreferenceStore();
	}

	/**
	 * @see PreferencePage#createContents(Composite)
	 */
	protected Control createContents(Composite parent) 
	{
		Composite composite = new Composite(parent, SWT.NONE);
		GridLayout layout = new GridLayout();
		composite.setLayout(layout);
		GridData data = new GridData(GridData.FILL);
		data.grabExcessHorizontalSpace = true;
		composite.setLayoutData(data);

	    IProject project = ((IResource)getElement()).getProject();
	    
	    try {
            if (project.hasNature(TLANature.NATURE_ID)) 
            {
        		addProjectLayoutSection(composite);
        		addSeparator(composite);
        		initValues(project);
            } else {
                addNotificationSection(composite);
            }
        } catch (CoreException e) 
        {
            e.printStackTrace();
        }
		return composite;
	}
	/**
	 * @see org.eclipse.jface.preference.PreferencePage#performDefaults()
	 */
	protected void performDefaults() 
	{
	    this.projectLayoutComposite.setSourceFolder(store.getDefaultString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_SOURCEDIR));
	    this.projectLayoutComposite.setConfigFolder(store.getDefaultString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_CONFIGDIR));
	    this.projectLayoutComposite.setWorkingFolder(store.getDefaultString(ITLAProjectConstants.TLA_PROJECT_LAYOUT_WORKINGDIR));
	    this.projectLayoutComposite.setProjectLayout(store.getDefaultBoolean(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED));
	}
	/**
	 * @see org.eclipse.jface.preference.IPreferencePage#performOk()
	 */
	public boolean performOk() 
	{
	    IProject project = ((IResource)getElement()).getProject();
	    return validateProperties(project);
	}
	/**
	 * @see org.eclipse.jface.preference.PreferencePage#performApply()
	 */
    protected void performApply() 
    {
	    IProject project = ((IResource)getElement()).getProject();
	    validateProperties(project);
    }
	/** 
	 * Adds notification section
     * @param composite
     */
    private void addNotificationSection(Composite parent) 
    {
		Composite composite = createDefaultComposite(parent);
		Label label = new Label(composite, SWT.NULL);
		GridData labelLayoutData = new GridData(GridData.FILL_HORIZONTAL);
		label.setLayoutData(labelLayoutData);
		label.setText("Current project is not a TLA+ project. Please add a TLA+ nature first to get access to TLA+ project properties.");
        
    }
    private void addProjectLayoutSection(Composite parent)
    {
        this.projectLayoutComposite = new ProjectLayoutComposite(parent);
    }
	/**
	 * Initialize persistent values
	 * @param project
	 */
    private void initValues(IProject project)
	{
        IEclipsePreferences projectNode = ProjectUtils.getProjectNode(project);
    	if (projectNode != null) 
    	{

			boolean projectLayoutSeparated 	= projectNode.getBoolean(ITLAProjectConstants.PERSIST_PROJECT_LAYOUT_SEPARATED, ITLAProjectConstants.DEFAULT_TLA_PROJECT_LAYOUT_SEPARATED);
		    String projectSource 			= projectNode.get(ITLAProjectConstants.PERSIST_PROJECT_SOURCE_FOLDER, ITLAProjectConstants.DEFAULT_ROOT_FOLDER);
		    String projectConfig			= projectNode.get(ITLAProjectConstants.PERSIST_PROJECT_CONFIG_FOLDER, ITLAProjectConstants.DEFAULT_ROOT_FOLDER);
		    String projectWorking			= projectNode.get(ITLAProjectConstants.PERSIST_PROJECT_WORKING_FOLDER, ITLAProjectConstants.DEFAULT_TLA_PROJECT_LAYOUT_WORKINGDIR);

            this.projectLayoutComposite.setProjectLayout(projectLayoutSeparated);
                
            this.projectLayoutComposite.setSourceFolder( projectSource );
            this.projectLayoutComposite.setConfigFolder( projectConfig );
            this.projectLayoutComposite.setWorkingFolder( projectWorking );
    	}
	}
	/**
	 * Validate properties
	 * @return
	 * @throws BackingStoreException
	 */
    private boolean validateProperties(IProject project) 
    {
	        String projectConfig = this.projectLayoutComposite.getConfigFolder();
	        String projectSource = this.projectLayoutComposite.getSourceFolder();
	        String projectWorking = this.projectLayoutComposite.getWorkingFolder();
	        IEclipsePreferences projectNode = ProjectUtils.getProjectNode(project);
	    	if (projectNode != null) 
	    	{
	    	    projectNode.putBoolean(ITLAProjectConstants.PERSIST_PROJECT_LAYOUT_SEPARATED, this.projectLayoutComposite.isProjectLayoutSeparated());
	    	    projectNode.put(ITLAProjectConstants.PERSIST_PROJECT_SOURCE_FOLDER, projectSource);
	    	    projectNode.put(ITLAProjectConstants.PERSIST_PROJECT_CONFIG_FOLDER, projectConfig);
	    	    projectNode.put(ITLAProjectConstants.PERSIST_PROJECT_WORKING_FOLDER, projectWorking);
				ProjectUtils.createDirectories(project);
				try 
				{
				    projectNode.flush();
				    project.refreshLocal(IProject.DEPTH_INFINITE, null);
				} catch (BackingStoreException bse)
				{
				    bse.printStackTrace();
				    return false;
				} catch (CoreException ce) 
				{
				    ce.printStackTrace();
				    return false;
				}
	    	}
			
        return true;
    }
	/**
	 * Adds a horizontal line
	 * @param parent
	 */
	private void addSeparator(Composite parent) 
	{
		Label separator = new Label(parent, SWT.SEPARATOR | SWT.HORIZONTAL);
		GridData gridData = new GridData();
		gridData.horizontalAlignment = GridData.FILL;
		gridData.grabExcessHorizontalSpace = true;
		separator.setLayoutData(gridData);
	}

	/**
	 * Create default composite
	 * @param parent
	 * @return
	 */
	private Composite createDefaultComposite(Composite parent) 
	{
		Composite composite = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		composite.setLayout(layout);

		GridData data = new GridData();
		data.verticalAlignment = GridData.FILL;
		data.horizontalAlignment = GridData.FILL;
		composite.setLayoutData(data);

		return composite;
	}
}