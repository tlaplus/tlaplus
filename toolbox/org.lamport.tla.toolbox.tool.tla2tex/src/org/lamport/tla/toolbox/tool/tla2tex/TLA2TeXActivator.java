package org.lamport.tla.toolbox.tool.tla2tex;

import java.io.File;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.lamport.tla.toolbox.AbstractTLCActivator;
import org.lamport.tla.toolbox.tool.tla2tex.preference.ITLA2TeXPreferenceConstants;
import org.osgi.framework.BundleContext;

import com.abstratt.graphviz.GraphVizActivator;
import com.abstratt.graphviz.GraphVizActivator.DotMethod;

/**
 * The activator class controls the plug-in life cycle
 */
public class TLA2TeXActivator extends AbstractTLCActivator {
    // The plug-in ID
    public static final String PLUGIN_ID = "org.lamport.tla.toolbox.tool.tlatex";

    private static final boolean IS_WINDOWS = Platform.OS_WIN32.equals(Platform.getOS());
    private static final String USR_LOCAL_BIN_PATH = "/usr/local/bin/dot";
    
    // The shared instance
    private static TLA2TeXActivator plugin;

	// Listen to preference changes in the TLA2TexPreferencePage. If the value for
	// dot command changes, we send the update to the GraphViz preference store.
	// GraphViz reads the value from its own store instead of ours.
    // Alternatively, we could instantiate GraphViz's own preference page, which
    // writes to GraphViz's preference store. However, we don't want to clutter
    // the Toolbox's preference with a dedicate GraphViz page.
    //  <page
    //    category="toolbox.ui.preferences.GeneralPreferencePage"
    //    class="com.abstratt.graphviz.ui.GraphVizPreferencePage"
    //    id="toolbox.ui.preferences.StateGraphPreferences"
    //    name="State Graph">
    // </page>
	private IPropertyChangeListener listener = new IPropertyChangeListener() {
		public void propertyChange(PropertyChangeEvent event) {
			if (ITLA2TeXPreferenceConstants.DOT_COMMAND.equals(event.getProperty())) {
				configureGraphViz((String)event.getNewValue());
			}
		}
	};

    /**
     * The constructor
     */
    public TLA2TeXActivator() {
    	super(PLUGIN_ID);
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
     */
    public void start(BundleContext context) throws Exception {
        super.start(context);
        plugin = this;
        
		final IPreferenceStore preferenceStore = getPreferenceStore();
		preferenceStore.addPropertyChangeListener(listener);
		configureGraphViz(preferenceStore.getString(ITLA2TeXPreferenceConstants.DOT_COMMAND));
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
     */
    public void stop(BundleContext context) throws Exception
    {
        plugin = null;
        super.stop(context);
    }

    /**
     * Returns the shared instance
     *
     * @return the shared instance
     */
    public static TLA2TeXActivator getDefault()
    {
        return plugin;
    }
    
    private void configureGraphViz(final String dotLocationPreferenceValue) {
    	// This will be blank if the user has never entered a value in the preference panel
		String dotCommand = dotLocationPreferenceValue;
		
		// Per GitHub #412
		if (!IS_WINDOWS
					&& ((dotCommand == null)
							|| (dotCommand.trim().length() == 0)
							|| "dot".equals(dotCommand))) {
			final File f = new File(USR_LOCAL_BIN_PATH);
			
			if (f.exists() && f.canExecute()) {
				dotCommand = USR_LOCAL_BIN_PATH;
			}
		}
		
		if ("dot".equals(dotCommand)) {
			// Setting it to "dot" implies auto lookup.
			logInfo("dot command set to automatic lookup.");
			GraphVizActivator.getInstance().setDotSearchMethod(DotMethod.AUTO);
		} else {
			// Explicit path is given.
			logInfo("dot command set to: " + dotCommand);
			GraphVizActivator.getInstance().setDotSearchMethod(DotMethod.MANUAL);
			GraphVizActivator.getInstance().setManualDotPath(dotCommand);
		}
    }
}
