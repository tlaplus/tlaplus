/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.ModuleParserLauncher;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;
import org.osgi.framework.Bundle;
import org.osgi.framework.Version;

import tla2sany.modanalyzer.SpecObj;

/**
 * Provides shortcuts to the internal toolbox methods, that should be made accessible to the other tools
 */
public class ToolboxHandle
{
    public static String I_RESTORE_LAST_SPEC = IPreferenceConstants.I_RESTORE_LAST_SPEC;

    /**
     * Retrieves the root file of the loaded spec or <code>null</code> if no spec selected
     */
    public static IFile getRootModule()
    {
        return ((Activator.getSpecManager().getSpecLoaded() == null) ? null : Activator.getSpecManager()
                .getSpecLoaded().getRootFile());
    }
    /**
     * Retrieves the root file of the specification project
     * @param project
     * @return the resource
     */
    public static IResource getRootModule(IProject project) 
    {
        return PreferenceStoreHelper.readProjectRootFile(project);
    }

    /**
     * Returns the instance preference store
     */
    public static IPreferenceStore getInstanceStore()
    {
        return PreferenceStoreHelper.getInstancePreferenceStore();
    }


    /**
     * Returns the SpecObj of the current loaded specification
     * @return SpecObj produced by the previous SANY run, or null
     */
    public static SpecObj getSpecObj()
    {
        Spec spec = null;
        try
        {
            spec = Activator.getSpecManager().getSpecLoaded();
        } catch (IllegalStateException e)
        {
            // this happens is the workspace is closed
            // just return null for e.G. JUnit tests
        }
        if (spec != null)
        {
            return spec.getValidRootModule();
        }
        return null;
    }

    /**
     * Retrieves the spec by name
     * @param name
     * @return
     */
    public static Spec getSpecByName(String name)
    {
        return Activator.getSpecManager().getSpecByName(name);
    }

    /**
     * @return
     */
    public static Spec getCurrentSpec()
    {
        return Activator.getSpecManager().getSpecLoaded();
    }

    /**
     * Determines if the module is a user module (not StandardModule)<br>
     * Note: only looks for parsed spec...
     * @param name a filename of the module (like foo.tla)
     * @return true if the user belongs to the spec
     * 
     */
    public static boolean isUserModule(String name)
    {
        if (name == null || name.length() == 0)
        {
            return false;
        }
        return Activator.getModuleDependencyStorage().hasModule(name);
    }

    /**
     * Retrieves the list of modules that are EXTEND-ed by current module
     * <br><b>Note:</b>Only works for current spec
     * @param rootModule, name of the module
     * @return list of modules it depends (EXTEND) on
     */
    @SuppressWarnings("unchecked")
	public static List<String> getExtendedModules(String moduleName)
    {
        return Activator.getModuleDependencyStorage().getListOfExtendedModules(moduleName);
    }

    /**
     * Returns the classpath entry of the tla2tool.jar (the TLA tools) 
     */
    public static IPath getTLAToolsClasspath() {
    	Bundle bundle = null;
    	
    	// find the tlatools bundle among all installed bundles
    	// (this code assumes tlatools has a bundle shape "dir")
		Bundle[] bundles = Activator.getDefault().getBundle()
				.getBundleContext().getBundles();
        for (int i = 0; i < bundles.length; i++) {
			Bundle aBundle = bundles[i];
			if ("org.lamport.tlatools".equals(aBundle.getSymbolicName())) {
				// OSGi supports multiple bundles with the same symbolic name, but
				// different versions. This e.g. occurs after a Toolbox update
				// before the old bundle version gets purged from the
				// installation directory.
				// Without this explicitly version check, the Toolbox
				// might accidentally use an old tla version which leads to
				// undefined behavior.
				// @see Bug #285 in general/bugzilla/index.html
				Version otherVersion = bundle != null ? bundle.getVersion()
						: Version.parseVersion("0.0.0");
				if (aBundle.getVersion().compareTo(otherVersion) > 0) {
					bundle = aBundle;
				}
			}
		}
        if (bundle == null)
            return null;

        URL local = null;
        try
        {
            local = FileLocator.toFileURL(bundle.getEntry("/")); //$NON-NLS-1$
        } catch (IOException e)
        {
            return null;
        }
        String fullPath = new File(local.getPath()).getAbsolutePath();
        return Path.fromOSString(fullPath);
    }
    
    /**
     * Parses the module
     * @param resource
     * @param monitor
     */
    public static IParseResult parseModule(IResource resource, IProgressMonitor monitor, boolean installMarkers, boolean updateDependencies)
    {
        ModuleParserLauncher moduleParser = new ModuleParserLauncher();
        ParseResult result = moduleParser.parseModule(resource, monitor, installMarkers, updateDependencies);
        return result;
    }
    
 
}
