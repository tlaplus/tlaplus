package org.lamport.tla.toolbox.ui.handler;

import java.io.File;

import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.matchers.WithText;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.junit.Assert;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.tlc.ui.test.AbstractTest;
import org.lamport.tla.toolbox.tool.tlc.ui.test.ModelEditorOpenCondition;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

@RunWith(SWTBotJunit4ClassRunner.class)
public class CloneModelTest extends AbstractTest {

	private static final String TLA_SUFFIX = ".tla";
	private static final String TEST_SPEC = "ToBeClonedSpec";
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

	@Test
	public void cloneModelMainMenu() {
		final SWTBotMenu modelMenu = bot.menu("TLC Model Checker");
		final SWTBotMenu cloneModelMenu = modelMenu.menu("Clone Model");
		final SWTBotMenu cloneModelSubMenu = cloneModelMenu.click();
		cloneModelSubMenu.menu(TEST_MODEL).click();

		bot.button("OK").click();
		bot.waitUntil(new ModelEditorOpenCondition(TEST_MODEL + "_Copy"));
	}

	// Verify spec and model show expected state (via API!!!)
	private void checkSpecAndModelExistenceAPI(final String specExpected) {
		final Spec spec = Activator.getSpecManager().getSpecLoaded();
		Assert.assertEquals(specExpected, spec.getName());
		
		final ILaunchConfiguration model = ModelHelper.getModelByName(spec.getProject(), TEST_MODEL);
		Assert.assertNotNull("Model could not be found", model);
	}
}
