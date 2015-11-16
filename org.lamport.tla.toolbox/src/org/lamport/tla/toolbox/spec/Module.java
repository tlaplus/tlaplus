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
 *   Simon Zambrowski - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.spec;

import java.io.File;

import org.eclipse.core.resources.IResource;
import org.lamport.tla.toolbox.util.RCPNameToFileIStream;

import tla2sany.semantic.ModuleNode;

/**
 * Representation of a module
 */
public class Module
{
    private final File file;
    
    private ModuleNode node;
    private boolean isRoot = false;
	private IResource resource;

    public Module(String absoluteFilename)
    {
        file = new File(absoluteFilename);
    }

    public Module(IResource resource) {
    	this(resource.getLocation().toOSString());
    	this.resource = resource;
	}

	/**
     * Retrieves absolute path of the module file
     * 
     * @return path of the module file
     */
    public String getAbsolutePath()
    {
        return file.getAbsolutePath();
    }

    /**
     * Retrieves the file handle
     * 
     * @return the file
     */
    public File getFile()
    {
        return file;
    }

	/**
	 * @return null or the Eclipse specific resource handle for this module. A
	 *         IResource is the pendant to the non-Eclipse specific
	 *         java.io.File.
	 * 
	 * @see {@link Module#getFile()}
	 */
    public IResource getResource() {
    	return resource;
    }

	public void setResource(IResource aResource) {
		this.resource = aResource;
	}
   
    /**
     * Retrieves the module name
     * @return the name of the module
     */
    public String getModuleName()
    {
        String filename = file.getName();
        if (filename.toLowerCase().indexOf(".tla") != -1)
        {
            filename = filename.substring(0, filename.indexOf(".tla"));
        }
        return filename;
    }

    /**
     * Retrieves the semantic node of the module (only available if the module has been parsed successfully)
     * 
     * @return the node
     */
    public ModuleNode getNode()
    {
        return node;
    }

    /**
     * Sets the semantic module node
     * 
     * @param node
     *            the node to set
     */
    public void setNode(ModuleNode node)
    {
        this.node = node;
    }

    /**
     * Determines if current module is a standard module <br>
     * TODO Fishy method. improve/unify it
     * 
     * @return true iff the absolute path of the module contains RCPNameToFileIStream.STANDARD_MODULES value
     */
    public boolean isStandardModule()
    {
        return (getAbsolutePath().indexOf(RCPNameToFileIStream.STANDARD_MODULES) != -1);
    }

    
    public boolean isRoot()
    {
        return isRoot;
    }
    
    public void setRoot(boolean isRoot)
    {
        this.isRoot = isRoot;
    }
}
