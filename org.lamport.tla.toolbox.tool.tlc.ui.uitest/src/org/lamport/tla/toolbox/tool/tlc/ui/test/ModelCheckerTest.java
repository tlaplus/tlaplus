package org.lamport.tla.toolbox.tool.tlc.ui.test;

import java.io.File;

import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.matchers.WithText;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;

@RunWith(SWTBotJunit4ClassRunner.class)
public class ModelCheckerTest extends AbstractTest {

	@BeforeClass
	public static void beforeClass() {
		// mimic super
		AbstractTest.beforeClass();
	}
	 
	@Test
	public void test() {
		// Open specA 
		SWTBotMenu fileMenu = bot.menu("File");
		SWTBotMenu openSpecMenu = fileMenu.menu("Open Spec");
		SWTBotMenu addNewSpecMenu = openSpecMenu.menu("Add New Spec...");
		addNewSpecMenu.click();

		bot.textWithLabel("Root-module file:").setText(specA);
		bot.button("Finish").click();

		final String specName = getSpecName(new File(specA));
		
		// specs are created in non-UI thread asynchronously which causes a
		// delay before the menu entry becomes available
		bot.waitUntil(Conditions.waitForMenu(bot.activeShell(),
				WithText.<MenuItem> withText(specName)));

		// Go back to previous spec
		openSpecMenu.menu(specName);
	}
}
