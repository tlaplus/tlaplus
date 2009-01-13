package org.lamport.tla.toolbox;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.lamport.tla.toolbox.spec.manager.ISpecManager;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.spec.parser.IParseResultListner;
import org.lamport.tla.toolbox.spec.parser.IParserRegistry;
import org.lamport.tla.toolbox.spec.parser.ParserRegistry;
import org.lamport.tla.toolbox.spec.parser.problem.ProblemDisplayingParseResultListener;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "org.lamport.tla.toolbox";

	// The shared instance
	private static Activator plugin;

    private static ISpecManager    specManager;
    private static IParserRegistry parserRegistry;

    
    private IParseResultListner parseResultListener = null;

	/**
	 * The constructor
	 */
	public Activator() {
	}

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
     */
    public void start(BundleContext context) throws Exception
    {
        super.start(context);
        plugin = this;
        
        // register the parse result change reacting listeners
        parseResultListener = new ProblemDisplayingParseResultListener();
        Activator.getParserRegistry().addParseResultListener(parseResultListener);
        
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
     */
    public void stop(BundleContext context) throws Exception
    {
        Activator.getParserRegistry().removeParseResultListener(parseResultListener);

        specManager = null;
        parserRegistry = null;
        plugin = null;
        
        super.stop(context);
    }


	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return plugin;
	}

    /**
     * Retrieves a working spec manager instance
     */
    public static synchronized ISpecManager getSpecManager()
    {
        if (specManager == null)
        {
            specManager = new WorkspaceSpecManager(); // DummySpecManager();
        }
        return specManager;
    }

    /**
     * Retrieves a working parser registry
     */
    public static synchronized IParserRegistry getParserRegistry()
    {
        if (parserRegistry == null)
        {
            parserRegistry = new ParserRegistry();
        }
        return parserRegistry;
    }
}
