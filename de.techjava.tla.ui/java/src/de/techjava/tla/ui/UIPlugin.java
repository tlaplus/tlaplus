package de.techjava.tla.ui;

import java.io.IOException;
import java.net.URL;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import de.techjava.tla.ui.editors.scanner.TLAPartitionScanner;
import de.techjava.tla.ui.editors.scanner.TLASourceScanner;
import de.techjava.tla.ui.util.ColorManager;
import de.techjava.tla.ui.util.ExtensionManager;
import de.techjava.tla.ui.util.ITLAProjectConstants;
import de.techjava.tla.ui.util.ParserManager;

/**
 * Plugin providing UI for using TLA inside Eclipse plattform
 * 
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: UIPlugin.java,v 1.1 2005/08/22 15:43:37 szambrovski Exp $
 */
public class UIPlugin 
	extends AbstractUIPlugin 
{
    /** Plugin ID is de.techjava.tla.ui */
    public 	static final 	String 		PLUGIN_ID = "de.techjava.tla.ui";
    private static 			UIPlugin 	plugin;
    
    

	private ColorManager 			colorManager;
	private ParserManager			sanyManager;
	private ExtensionManager		extensionManager;

	private ResourceBundle 			resourceBundle;
	private TLASourceScanner 		sourceScanner;
	private TLAPartitionScanner		partitionScanner;
	/**
	 * The constructor.
	 */
	public UIPlugin() 
	{
		super();
		plugin = this;
		try 
		{
			resourceBundle = ResourceBundle.getBundle("de.techlinux.tla.ui.UiPluginResources");
		} catch (MissingResourceException x) 
		{
			resourceBundle = null;
		}
	}

	/**
	 * This method is called upon plug-in activation
	 */
	public void start(BundleContext context) 
		throws Exception 
	{
		super.start(context);
	}

	/**
	 * This method is called when the plug-in is stopped
	 */
	public void stop(BundleContext context) 
		throws Exception 
	{
		super.stop(context);
		colorManager.dispose();
	}
	/** 
	 * Initializes a preference store with default preference values 
	 * for this plug-in.
	 * @param store the preference store to fill
	 */
	protected void initializeDefaultPreferences(IPreferenceStore store) 
	{
	    getColorManager().initializeDefaultPreferences();
	    getSANYManager().initializeDefaults();

	    store.setDefault(ITLAProjectConstants.TLA_PROJECT_LAYOUT_WORKINGDIR, 			ITLAProjectConstants.DEFAULT_TLA_PROJECT_LAYOUT_WORKINGDIR );
	    store.setDefault(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED, 			ITLAProjectConstants.DEFAULT_TLA_PROJECT_LAYOUT_SEPARATED );
	    store.setDefault(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_CONFIGDIR, 	ITLAProjectConstants.DEFAULT_TLA_PROJECT_LAYOUT_SEPARATED_CONFIGDIR );
	    store.setDefault(ITLAProjectConstants.TLA_PROJECT_LAYOUT_SEPARATED_SOURCEDIR, 	ITLAProjectConstants.DEFAULT_TLA_PROJECT_LAYOUT_SEPARATED_SOURCEDIR );
	    
	    
	}
	/**
	 * Returns the plugin's resource bundle,
	 */
	public ResourceBundle getResourceBundle() 
	{
		return resourceBundle;
	}
	/**
	 * Returns an instance of a color manager
	 * @return color manager instance
	 */
	public ColorManager getColorManager() 
	{
		if (colorManager == null) {
			colorManager = new ColorManager(getPreferenceStore());
		}
		return colorManager;
	}
	/**
	 * Returns an instance of a color manager
	 * @return color manager instance
	 */
	public ParserManager getSANYManager() 
	{
		if (sanyManager == null) 
		{
		    sanyManager = new ParserManager(getPreferenceStore());
		}
		return sanyManager;
	}
	/**
	 * Retrieves extension manager
	 * @return
	 */
	public ExtensionManager getExtensionManager()
	{
	    if (extensionManager == null) 
	    {
	        extensionManager = new ExtensionManager();
	    }
	    return extensionManager;
	}

	/**
	 * Retrieves an image description
	 * @param name
	 * @return
	 */
	public ImageDescriptor getImageDescriptor(String name) 
	{
		URL url = this.getBundle().getEntry("/" + name);
	    return ImageDescriptor.createFromURL(url);
	}

	/**
	 * retrieves default installation module path 
	 * @return string with module location
	 */
	public String getInstallationModulesPath()
	{
	    IPath relative = new Path("modules");
		URL bundleURL = Platform.find(getBundle(), relative);
		if (bundleURL != null) 
		{
			URL fileURL = null;
            try {
                fileURL = Platform.asLocalURL(bundleURL);
            } catch (IOException e) {
                e.printStackTrace();
            }
            return (fileURL != null ) ? fileURL.getFile().substring(1) : null;
		}
		return null;
	}
	
	/**
	 * Retrieves a scanner for reserved words
	 * @return a scanner for reserved words
	 */
	public TLASourceScanner getTLASourceScanner() 
	{
	    if (sourceScanner == null) {
			sourceScanner = new TLASourceScanner(colorManager);
		}
		return sourceScanner;

	}
	/**
	 * Retrieves TLA partitioner scanner instance
	 * @return
	 */
	public TLAPartitionScanner getTLAPartitionScanner()
	{
	    if (partitionScanner == null)
	    {
	        partitionScanner = new TLAPartitionScanner();
	    }
	    
	    return partitionScanner;
	}


	/**
	 * Returns the workspace instance.
	 */
	public static IWorkspace getWorkspace() 
	{
		return ResourcesPlugin.getWorkspace();
	}

	/**
	 * Returns the string from the plugin's resource bundle,
	 * or 'key' if not found.
	 */
	public static String getResourceString(String key) 
	{
		ResourceBundle bundle = UIPlugin.getDefault().getResourceBundle();
		try {
			return (bundle != null) ? bundle.getString(key) : key;
		} catch (MissingResourceException e) {
			return key;
		}
	}
	/**
	 * Returns the shared instance.
	 */
	public static UIPlugin getDefault() 
	{
		return plugin;
	}
	/**
	 * Logs an error
	 * @param description Error description
	 * @param cause cause of an error
	 */
	public static void logError(String description, Throwable cause)
	{
	    getDefault().getLog().log(
				new Status(
					IStatus.ERROR,
					UIPlugin.PLUGIN_ID,
					0,
					description,
					cause));
	    
	}

}
