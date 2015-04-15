package org.lamport.tla.toolbox.ui.wizard;

import static org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory.withText;

import java.io.File;

import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.hamcrest.Matcher;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.lamport.tla.toolbox.test.RCPTestSetupHelper;

import junit.framework.Assert;

@RunWith(SWTBotJunit4ClassRunner.class)
public class AddSpecWizardTest {

	private static SWTWorkbenchBot bot;

	@BeforeClass
	public static void beforeClass() throws Exception {
		RCPTestSetupHelper.beforeClass();
		
		bot = new SWTWorkbenchBot();

		// Wait for the Toolbox shell to be available
		final Matcher<Shell> withText = withText("TLA+ Toolbox");
		bot.waitUntil(Conditions.waitForShell(withText), 30000);
		
		// Wait for the Toolbox UI to be fully started.
		final Matcher<MenuItem> withMnemonic = WidgetMatcherFactory.withMnemonic("File");
		final Matcher<MenuItem> matcher = WidgetMatcherFactory.allOf(WidgetMatcherFactory.widgetOfType(MenuItem.class),
				withMnemonic);
		bot.waitUntil(Conditions.waitForMenu(bot.activeShell(), matcher), 30000);
	}
	
	/**
	 * Test to make sure the "Add Spec" wizard does not accept invalid spec names
	 */
	@Test
	public void doNotAcceptInvalidSpecNames() {
		
		// Open specA 
		SWTBotMenu fileMenu = bot.menu("File");
		SWTBotMenu openSpecMenu = fileMenu.menu("Open Spec");
		SWTBotMenu addNewSpecMenu = openSpecMenu.menu("Add New Spec...");
		addNewSpecMenu.click();

		// get a handle for the button before invoking the UI (widget not found exception otherwise)
		SWTBotButton button = bot.button("Finish");
		
		// create a valid path
		String path = System.getProperty("java.io.tmpdir");
		path += File.separator + "Invalid-Name.tla";
		
		// set an invalid spec name
		bot.textWithLabel("Root-module file:").setText(path);
		
		// check if the wizard can finish
		Assert.assertTrue(
				"Finish button must not be enabled with invalid spec name",
				!button.isEnabled());
		
		//TODO could change the wizard marker/error area for the correct string too
	}

	@AfterClass
	public static void sleep() {
		bot.sleep(2000);
	}
}
