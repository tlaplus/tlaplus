package org.lamport.tla.toolbox.tool.tlc.ui.test;

import java.io.File;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.matchers.WithText;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

@RunWith(SWTBotJunit4ClassRunner.class)
public class ModelCheckerTest extends AbstractTest {

	@BeforeClass
	public static void beforeClass() {
		// mimic super
		AbstractTest.beforeClass();
	}

	@Test
	public void testNewModel() {
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
		bot.waitUntil(Conditions.waitForMenu(bot.activeShell(), WithText.<MenuItem> withText(specName)));
		
		// create a new model
		final SWTBotMenu modelMenu = bot.menu("TLC Model Checker");
		final SWTBotMenu newModelMenu = modelMenu.menu("New Model...");
		newModelMenu.click();
		bot.button("OK").click();

		// wait for model editor to show up and parse
		bot.waitUntil(new ModelEditorOpenCondition("Model_"));
		
		// register job listener who listens for the model checker job
		final String modelName = UIHelper.getActiveEditor().getTitle();
		final IJobChangeListener listener = new DummyJobChangeListener(modelName);
		Job.getJobManager().addJobChangeListener(listener);
		
		// start model checking by clicking the menu. This is more robust
		// compared to the f11 keystroke which can get lost when fired during
		// initialization of the model editor.
		bot.menu("TLC Model Checker").menu("Run model").click();

		// make unit test wait for model checker job to finish
		bot.waitUntil((ICondition) listener, SWTBotPreferences.TIMEOUT * 3);
		
		// Delete the newly created model again. It does not use the UI because
		// SWTBot cannot handle the modal confirmation dialog do delete the
		// model.
		// Deleting the model is necessary because repeated test execution would
		// leave huge numbers of model leftovers contributing to slowed down test
		// execution (see SizeControlContribution for reason why). 
		try {
			final ILaunchConfiguration ilc = ModelHelper.getModelByName(modelName);
			ModelHelper.deleteModel(ilc, new NullProgressMonitor());
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}
}
