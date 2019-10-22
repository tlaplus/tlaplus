package org.lamport.tla.toolbox.editor.basic;

import java.util.Dictionary;
import java.util.Hashtable;

import org.eclipse.e4.ui.css.swt.theme.ITheme;
import org.eclipse.e4.ui.css.swt.theme.IThemeEngine;
import org.eclipse.e4.ui.css.swt.theme.IThemeManager;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.ITokenScanner;
import org.eclipse.swt.widgets.Display;
import org.lamport.tla.toolbox.AbstractTLCActivator;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.tla.PCALCodeScanner;
import org.lamport.tla.toolbox.editor.basic.tla.TLACodeScanner;
import org.osgi.framework.BundleContext;
import org.osgi.framework.ServiceReference;
import org.osgi.framework.ServiceRegistration;
import org.osgi.service.event.Event;
import org.osgi.service.event.EventConstants;
import org.osgi.service.event.EventHandler;

/**
 * The activator class controls the plug-in life cycle
 */
@SuppressWarnings("restriction")
public class TLAEditorActivator extends AbstractTLCActivator {
    // The plug-in ID
    public static final String PLUGIN_ID = "org.lamport.tla.toolbox.editor.basic";

    // The shared instance
    private static TLAEditorActivator plugin;
    
    private static final String DARK_THEME_ID_PREFIX = "org.eclipse.e4.ui.css.theme.e4_dark";

    /**
     * Returns the shared instance
     *
     * @return the shared instance
     */
	public static TLAEditorActivator getDefault() {
        return plugin;
    }

    
    private TLAPartitionScanner partitionTokenScanner;
    private TLAColorProvider colorProvider;
    private TLACodeScanner tlaCodeScanner;
    private PCALCodeScanner pcalCodeScanner;

    private ServiceRegistration<?> themeChangeEventRegistration;
    
    private Boolean currentThemeIsDark;

    /**
     * The constructor
     */
	public TLAEditorActivator() {
    	super(PLUGIN_ID);
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
     */
	public void start(final BundleContext context) throws Exception {
    	plugin = this;
    	
        super.start(context);
        
    	final Dictionary<String, Object> serviceRegistrationProperties = new Hashtable<>();
    	serviceRegistrationProperties.put(EventConstants.EVENT_TOPIC, IThemeEngine.Events.THEME_CHANGED);
    	
    	themeChangeEventRegistration = context.registerService(EventHandler.class.getName(), new EventHandler() {
    		@Override
    		public void handleEvent(final Event event) {
    			tlaCodeScanner = null;
    			pcalCodeScanner = null;
    			setDarkThemeStatus();
    		}
    	}, serviceRegistrationProperties);
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
     */
	public void stop(final BundleContext context) throws Exception {
		themeChangeEventRegistration.unregister();
		plugin = null;
		super.stop(context);
	}

    private void setDarkThemeStatus () {
    	final BundleContext context = Activator.getDefault().getBundle().getBundleContext();
    	final ServiceReference<IThemeManager> serviceReference = context.getServiceReference(IThemeManager.class);
    	
    	if (serviceReference != null) {
            final IThemeManager manager = context.getService(serviceReference);

            if (manager != null) {
            	final Display d = Display.getDefault();
            	final IThemeEngine engine = manager.getEngineForDisplay(d);
            	final ITheme it = engine.getActiveTheme();
            	
            	if (it != null) {
            		boolean newThemeStatus = it.getId().startsWith(DARK_THEME_ID_PREFIX);
            		
            		if ((currentThemeIsDark == null) || (currentThemeIsDark.booleanValue() != newThemeStatus)) {
						if (currentThemeIsDark != null) {
							d.asyncExec(() -> {
								MessageDialog.openInformation(d.getActiveShell(), "Theme Change",
										"You will need to close any open views and editors, then re-open them, to have "
												+ "your theme change fully reflected (or restart the Toolbox.)");
							});
            			}
						
            			currentThemeIsDark = Boolean.valueOf(newThemeStatus);
            		}
            	}
            }
    	}
    }
	
	/**
	 * @return true if the current UI theme is dark
	 */
	public boolean isCurrentThemeDark() {
		return (currentThemeIsDark == null) ? false : currentThemeIsDark.booleanValue();
	}

    /**
     * @return
     */
    public IPartitionTokenScanner getTLAPartitionScanner()
    {
        if (partitionTokenScanner == null) 
        {
            partitionTokenScanner = new TLAPartitionScanner();
        }
        return partitionTokenScanner; 
    }

    /**
     * @return
     */
    public TLAColorProvider getTLAColorProvider()
    {
        if (colorProvider == null) 
        {
            colorProvider = new TLAColorProvider();
        }
        return colorProvider; 
    }

    /**
     * @return
     */
    public ITokenScanner getTLACodeScanner()
    {
        if (tlaCodeScanner== null) 
        {
            tlaCodeScanner = new TLACodeScanner();
        }
        return tlaCodeScanner; 
    }
    
    // Added for PlusCal
    public ITokenScanner getPCALCodeScanner()
    {
        if (pcalCodeScanner== null) 
        {
            pcalCodeScanner = new PCALCodeScanner();
        }
        return pcalCodeScanner; 
    }
}
