package org.lamport.tla.toolbox.tool.tlc.ui.test;

import static org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory.withText;

import java.io.File;

import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.swt.finder.matchers.WithText;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.waits.WaitForObjectCondition;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.ui.PlatformUI;
import org.hamcrest.Matcher;
import org.junit.Assert;
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
		// Force shell activation to counter, no active Shell when running SWTBot tests in Xvfb/Xvnc
		// see https://wiki.eclipse.org/SWTBot/Troubleshooting#No_active_Shell_when_running_SWTBot_tests_in_Xvfb
		Display.getDefault().syncExec(new Runnable() {
			public void run() {
				PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell().forceActive();
			}
		});
		
		bot = new SWTWorkbenchBot();

		// Wait for the Toolbox shell to be available
		final Matcher<Shell> withText = withText("TLA+ Toolbox");
		bot.waitUntil(Conditions.waitForShell(withText), 30000);
		
		// Wait for the Toolbox UI to be fully started.
		final Matcher<MenuItem> withMnemonic = WidgetMatcherFactory.withMnemonic("File");
		final Matcher<MenuItem> matcher = WidgetMatcherFactory.allOf(WidgetMatcherFactory.widgetOfType(MenuItem.class),
				withMnemonic);
		bot.waitUntil(Conditions.waitForMenu(bot.shell("TLA+ Toolbox"), matcher), 30000);
	}

	/**
	 * @param aFile 
	 * @return The file name without path or suffix/extension
	 */
	protected String getSpecName(final File aFile) {
		final String name = aFile.getName();
		return name.substring(0, name.lastIndexOf("."));
	}
	
	/**
	 * @return waits for the TLA+ Toolbox shell to come available
	 */
	protected SWTBotShell waitForToolboxShell() {
		final WaitForObjectCondition<Shell> waitForShell = Conditions.waitForShell(WithText
				.<Shell> withText("TLA+ Toolbox"));
		bot.waitUntil(waitForShell);
		return new SWTBotShell(waitForShell.get(0));
	}
}
