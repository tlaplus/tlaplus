package org.lamport.tla.toolbox.tool.tlc.ui.test;

import java.io.File;

import junit.framework.Assert;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.junit.Before;
import org.lamport.tla.toolbox.test.RCPTestSetupHelper;

public abstract class AbstractTest {
	
	/**
	 * workbench handle used by tests to access UI elements 
	 */
	protected SWTWorkbenchBot bot;

	/**
	 * Full qualified spec name
	 */
	protected static final String specA = System
			.getProperty("org.lamport.tla.toolbox.tool.tlc.ui.test.PathToSpecA");

	/**
	 * Pre flight checks (run once for each test _class_)
	 */
	public static void beforeClass() {
		// check to make sure the given spec files exist
		Assert.assertTrue("Given spec file does not exist: " + specA, new File(
				specA).exists());

		// Reset the workbench
		RCPTestSetupHelper.beforeClass();
	}
	
	/**
	 * Pre flight initialization (run once for each test _case_)
	 */
	@Before
	public void setUp() throws Exception {
		bot = new SWTWorkbenchBot();
	}

	/**
	 * @param aFile 
	 * @return The file name without path or suffix/extension
	 */
	protected String getSpecName(final File aFile) {
		final String name = aFile.getName();
		return name.substring(0, name.lastIndexOf("."));
	}
}
