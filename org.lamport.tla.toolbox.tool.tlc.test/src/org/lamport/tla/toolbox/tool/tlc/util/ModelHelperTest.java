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
package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchDelegate;
import org.junit.Assert;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;

import junit.framework.TestCase;

/**
 * Test for toolkit methods
 */
public class ModelHelperTest extends TestCase
{

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    protected void setUp() throws Exception
    {
        super.setUp();
    }

    /**
     * Test method for {@link org.lamport.tla.toolbox.tool.tlc.util.ModelHelper#getCheckpoints(org.eclipse.debug.core.ILaunchConfiguration)}.
     */
    public void testRegexGetCheckpoints()
    {
        String input = "09-08-13-15-07-32";
        String input2 = "hello dolly";
        
        Pattern pattern = Pattern.compile("[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}");
        
        Matcher matcher = pattern.matcher(input);
        Assert.assertTrue(matcher.matches());

        Matcher matcher2 = pattern.matcher(input2);
        Assert.assertFalse(matcher2.matches());
    }
    
    public void testStripSymmetry() {
    	final List<String> serializedList = new ArrayList<String>();
    	serializedList.add("Procs;;{A, B};1;1");
    	
    	// Symmetry not stripped
    	List<Assignment> deserializeAssignmentList = ModelHelper.deserializeAssignmentList(serializedList);
    	assertEquals(1, deserializeAssignmentList.size());
    	assertTrue(deserializeAssignmentList.get(0).isSymmetricalSet());
    	
    	// Symmetry stripped
    	deserializeAssignmentList = ModelHelper.deserializeAssignmentList(serializedList, true);
    	assertEquals(1, deserializeAssignmentList.size());
    	assertFalse(deserializeAssignmentList.get(0).isSymmetricalSet());
    }
    
    public void testPrettyPrintConstants2() throws CoreException {
		final List<String> values = new ArrayList<String>();
		values.add("X;;X;1;0");
		values.add("Y;;{a1, b1};1;0");
		values.add("Z;;{s1, s2};1;1");
		values.add("W;;1;0;0");
		values.add("V;;V;1;0");
		values.add("U;;42;0;0");
		final ILaunchConfiguration config = new DummyLaunchConfig(
				IModelConfigurationConstants.MODEL_PARAMETER_CONSTANTS, values);

		final String constants = ModelHelper.prettyPrintConstants(config, "\n");
    	final String[] split = constants.split("\n");
    	assertEquals(5, split.length);
    	assertEquals("U <- 42", split[0]);
    	assertEquals("W <- 1", split[1]);
    	assertEquals("Y <- {a1, b1}", split[2]);
    	assertEquals("Z <- sym{s1, s2}", split[3]);
    	assertEquals("Model values: V, X", split[4]);
    }
    
    private class DummyLaunchConfig implements ILaunchConfiguration {

    	private final Map<String, List<String>> attributes = new HashMap<String, List<String>>();
    	
    	public DummyLaunchConfig(String key, List<String> value) {
    		this.attributes.put(key, value);
    	}
    	
		public <T> T getAdapter(Class<T> adapter) {
			return null;
		}

		public boolean contentsEqual(ILaunchConfiguration configuration) {
			return false;
		}

		public ILaunchConfigurationWorkingCopy copy(String name) throws CoreException {
			return null;
		}

		public void delete() throws CoreException {
		}

		public boolean exists() {
			return false;
		}

		public boolean getAttribute(String attributeName, boolean defaultValue) throws CoreException {
			return false;
		}

		public int getAttribute(String attributeName, int defaultValue) throws CoreException {
			return 0;
		}

		public List<String> getAttribute(String attributeName, List<String> defaultValue) throws CoreException {
			return this.attributes.get(attributeName);
		}

		public Set<String> getAttribute(String attributeName, Set<String> defaultValue) throws CoreException {
			return null;
		}

		public Map<String, String> getAttribute(String attributeName, Map<String, String> defaultValue)
				throws CoreException {
			return null;
		}

		public String getAttribute(String attributeName, String defaultValue) throws CoreException {
			return null;
		}

		public Map<String, Object> getAttributes() throws CoreException {
			return null;
		}

		public String getCategory() throws CoreException {
			return null;
		}

		public IFile getFile() {
			return null;
		}

		public IPath getLocation() {
			return null;
		}

		public IResource[] getMappedResources() throws CoreException {
			return null;
		}

		public String getMemento() throws CoreException {
			return null;
		}

		public String getName() {
			return null;
		}

		public Set<String> getModes() throws CoreException {
			return null;
		}

		public ILaunchDelegate getPreferredDelegate(Set<String> modes) throws CoreException {
			return null;
		}

		public ILaunchConfigurationType getType() throws CoreException {
			return null;
		}

		public ILaunchConfigurationWorkingCopy getWorkingCopy() throws CoreException {
			return null;
		}

		public boolean hasAttribute(String attributeName) throws CoreException {
			return false;
		}

		public boolean isLocal() {
			return false;
		}

		public boolean isMigrationCandidate() throws CoreException {
			return false;
		}

		public boolean isWorkingCopy() {
			return false;
		}

		public ILaunch launch(String mode, IProgressMonitor monitor) throws CoreException {
			return null;
		}

		public ILaunch launch(String mode, IProgressMonitor monitor, boolean build) throws CoreException {
			return null;
		}

		public ILaunch launch(String mode, IProgressMonitor monitor, boolean build, boolean register)
				throws CoreException {
			return null;
		}

		public void migrate() throws CoreException {
		}

		public boolean supportsMode(String mode) throws CoreException {
			return false;
		}

		public boolean isReadOnly() {
			return false;
		}
    }
}
