package org.lamport.tla.toolbox.ui.handler;

import java.io.File;

import org.eclipse.core.runtime.AssertionFailedException;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.matchers.WithText;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IEditorPart;
import org.junit.Assert;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.TLCSpec;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.test.AbstractTest;
import org.lamport.tla.toolbox.tool.tlc.ui.test.DummyJobChangeListener;
import org.lamport.tla.toolbox.tool.tlc.ui.test.ModelEditorOpenCondition;
import org.lamport.tla.toolbox.util.UIHelper;


/**
 * This test is placed in bundle ...tlc.ui.uitest because it renaming a spec
 * internally requires renaming all its models too.
 */
@RunWith(SWTBotJunit4ClassRunner.class)
public class RenameSpecHandlerTest extends AbstractTest {
	
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
		
		checkSpecAndModelExistenceAPI(TEST_SPEC, TEST_MODEL);
	}
	
	/**
	 * @see Bug #58 in general/bugzilla/index.html
	 */
	@Test
	public void renameSpec() throws InterruptedException {
		openSpecExplorer();

		SWTBotTreeItem treeItem = bot.tree().getTreeItem(TEST_SPEC);
		checkForModelExistenceUI(treeItem);

		SWTBotMenu contextMenu = treeItem.contextMenu("Rename");
		contextMenu.click();
		
		// rename to ..._Copy
		bot.button("OK").click();
		
		// wait for rename to be done
		bot.waitUntil(new SpecEditorOpenCondition(TEST_SPEC));

		// verify (via API)
		checkSpecAndModelExistenceAPI((TEST_SPEC + "_Copy"), TEST_MODEL);
		
		// try to find the renamed file (via UI)
		openSpecExplorer();
		treeItem = bot.tree().getTreeItem(TEST_SPEC + "_Copy [ " + TEST_SPEC + TLA_SUFFIX + " ]");
		
		/*
		 * try to launch the model
		 */
		SWTBotTreeItem modelTreeItem = checkForModelExistenceUI(treeItem);
		modelTreeItem.contextMenu("Open").click();
		Assert.assertNotNull("UI tree item (model) could not be found", modelTreeItem);
		
		// register job listener who listens for the model checker job
		final String modelName = UIHelper.getActiveEditor().getTitle();
		final Model model = ToolboxHandle.getCurrentSpec().getAdapter(TLCSpec.class).getModel(modelName);
		final IJobChangeListener listener = new DummyJobChangeListener(model);
		Job.getJobManager().addJobChangeListener(listener);
		
		// start model checking by clicking the menu. This is more robust
		// compared to the f11 keystroke which can get lost when fired during
		// initialization of the model editor.
		bot.menu("TLC Model Checker").menu("Run model").click();

		// make unit test wait for model checker job to finish
		bot.waitUntil((ICondition) listener, SWTBotPreferences.TIMEOUT * 3);

		// Do some unregistration prior to model deletion:
		Job.getJobManager().removeJobChangeListener(listener);
		
		// close corresponding editor if open
		final IEditorPart editorWithModelOpened = model.getAdapter(ModelEditor.class);
		if (editorWithModelOpened != null) {
			UIHelper.runUISync(new Runnable() {
				public void run() {
					UIHelper.getActivePage().closeEditor(editorWithModelOpened,
							false);
				}
			});
		}
	}
	
	// check if the models have been renamed correctly too (via UI!!!)
	private SWTBotTreeItem checkForModelExistenceUI(final SWTBotTreeItem treeItem) {
		try {
			treeItem.expand();
			SWTBotTreeItem models = treeItem.getNode("models");
			models.expand();
			return models.getNode(TEST_MODEL).select();
		} catch(AssertionFailedException e) {
			Assert.fail(e.getMessage());
		}
		return null;
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
