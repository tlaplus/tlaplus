package org.lamport.tla.toolbox.ui.handler;

import java.io.File;

import junit.framework.Assert;

import org.eclipse.core.runtime.AssertionFailedException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.matchers.WithText;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.tlc.ui.test.AbstractTest;
import org.lamport.tla.toolbox.tool.tlc.ui.test.ModelEditorOpenCondition;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * This test is placed in bundle ...tlc.ui.uitest because it renaming a spec
 * internally requires renaming all its models too.
 */
@RunWith(SWTBotJunit4ClassRunner.class)
public class RenameSpecHandlerTest extends AbstractTest {

	private static final String SPEC_EXPLORER = "Spec Explorer";
	private static final String TLA_SUFFIX = ".tla";
	private static final String TEST_SPEC = "ToBeRenamedSpec";
	private static final String TEST_MODEL = "Model_1";

	@BeforeClass
	public static void beforeClass() {
		// mimic super
		AbstractTest.beforeClass();
	}

	@Before
	public void setUp() throws Exception {
		super.setUp();
		
		// create a dummy spec "ToBeRenamedSpec"
		SWTBotMenu fileMenu = bot.menu("File");
		SWTBotMenu openSpecMenu = fileMenu.menu("Open Spec");
		SWTBotMenu addNewSpecMenu = openSpecMenu.menu("Add New Spec...");
		addNewSpecMenu.click();
		
		String path = System.getProperty("java.io.tmpdir") + File.separator + "RSHTest"
				+ System.currentTimeMillis();
		path += File.separator + TEST_SPEC + TLA_SUFFIX;

		bot.textWithLabel("Root-module file:").setText(path);
		bot.button("Finish").click();

		final String specName = getSpecName(new File(path));
		bot.waitUntil(Conditions.waitForMenu(bot.activeShell(), WithText.<MenuItem> withText(specName)));
		
		// create a new dummy model
		final SWTBotMenu modelMenu = bot.menu("TLC Model Checker");
		final SWTBotMenu newModelMenu = modelMenu.menu("New Model...");
		newModelMenu.click();
		bot.button("OK").click();
		bot.waitUntil(new ModelEditorOpenCondition(TEST_MODEL));
		
		// save and close model editor
		SWTBotEditor activeEditor = bot.activeEditor();
		activeEditor.saveAndClose();
		
		checkSpecAndModelExistenceAPI(TEST_SPEC);
	}
	
	/**
	 * @see http://bugzilla.tlaplus.net/show_bug.cgi?id=58
	 */
	@Test
	public void renameSpec() throws InterruptedException {
		openSpecExplorer();

		SWTBotTreeItem treeItem = bot.tree().getTreeItem(TEST_SPEC + " [ " + TEST_SPEC + TLA_SUFFIX + " ]");
		checkForModelExistenceUI(treeItem);

		SWTBotMenu contextMenu = treeItem.contextMenu("Rename");
		contextMenu.click();
		
		// rename to ..._Copy
		bot.button("OK").click();
		
		// wait for rename to be done
		bot.waitUntil(new SpecEditorOpenCondition(TEST_SPEC));

		// verify (via API)
		checkSpecAndModelExistenceAPI(TEST_SPEC + "_Copy");
		
		// try to find the renamed file (via UI)
		openSpecExplorer();
		treeItem = bot.tree().getTreeItem(TEST_SPEC + "_Copy [ " + TEST_SPEC + TLA_SUFFIX + " ]");
		
		checkForModelExistenceUI(treeItem);
	}

	// Verify spec and model show expected state (via API!!!)
	private void checkSpecAndModelExistenceAPI(final String specExpected) {
		final Spec spec = Activator.getSpecManager().getSpecLoaded();
		Assert.assertEquals(specExpected, spec.getName());
		
		final ILaunchConfiguration model = ModelHelper.getModelByName(spec.getProject(), TEST_MODEL);
		Assert.assertNotNull("Model could not be found", model);
	}
	
	// check if the models have been renamed correctly too (via UI!!!)
	private void checkForModelExistenceUI(final SWTBotTreeItem treeItem) {
		try {
			treeItem.expand();
			treeItem.select(TEST_MODEL);
		} catch(AssertionFailedException e) {
			Assert.fail(e.getMessage());
		}
	}

	// Open spec explorer which is the only place to reach the rename action
	private void openSpecExplorer() {
		SWTBotMenu windowMenu = bot.menu("Window");
		SWTBotMenu specExplorerMenu = windowMenu.menu(SPEC_EXPLORER);
		specExplorerMenu.click();
		
		// spec context menu
		SWTBotView packageExplorerView = bot.viewByTitle(SPEC_EXPLORER);
		packageExplorerView.setFocus();
	}
}
