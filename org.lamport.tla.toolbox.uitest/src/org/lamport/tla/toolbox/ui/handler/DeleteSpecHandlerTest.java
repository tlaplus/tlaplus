package org.lamport.tla.toolbox.ui.handler;

import static org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory.withText;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.PlatformUI;
import org.hamcrest.Matcher;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.test.RCPTestSetupHelper;
import org.lamport.tla.toolbox.ui.navigator.ToolboxExplorer;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

@RunWith(SWTBotJunit4ClassRunner.class)
public class DeleteSpecHandlerTest {

	private static SWTWorkbenchBot bot;

	@BeforeClass
	public static void beforeClass() throws Exception {
		RCPTestSetupHelper.beforeClass();
		
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
	
	@Test
	public void deleteMultipleSpecs() throws CoreException, IOException {
		// Make sure there are no specs at first
		assertEquals(0, Activator.getSpecManager().getSpecs().size());
		
		// create a valid path
		File fileA = File.createTempFile("DeleteMultiSpecA", ".tla");
		fileA.delete();
		// Create the spec file
		ResourcesPlugin.getWorkspace().run(ResourceHelper.createTLAModuleCreationOperation(new Path(fileA.getAbsolutePath())),
				new NullProgressMonitor());
		// Create the spec
		final Spec spec = Spec.createNewSpec("SpecA", fileA.getAbsolutePath(), false, new NullProgressMonitor());
		// Register the spec
		Activator.getSpecManager().addSpec(spec);

		// create a second valid path
		File fileB = File.createTempFile("DeleteMultiSpecB", ".tla");
		fileB.delete();
		// Create the spec file
		ResourcesPlugin.getWorkspace().run(ResourceHelper.createTLAModuleCreationOperation(new Path(fileB.getAbsolutePath())),
				new NullProgressMonitor());
		// Create the spec
		Spec specB = Spec.createNewSpec("SpecB", fileB.getAbsolutePath(), false, new NullProgressMonitor());
		// Register the spec
		Activator.getSpecManager().addSpec(specB);

		// Make sure there are no specs at first
		assertEquals(2, Activator.getSpecManager().getSpecs().size());
		
		Activator.getSpecManager().setSpecLoaded(spec);
		
		// Trigger update so that both specs show up in the explorer
		UIHelper.runUISync(new Runnable() {
			public void run() {
				ToolboxExplorer.refresh();
	            final HashMap<String, String> parameters = new HashMap<String, String>();
	            parameters.put(OpenSpecHandler.PARAM_SPEC, spec.getName());

	            // runs the command
	            UIHelper.runCommand(OpenSpecHandler.COMMAND_ID, parameters);
			}
		});
		
		bot.waitUntil(new SpecEditorOpenCondition(fileA.getName()));
		
		// Make sure one spec is open and has an editor
		assertEquals(1, UIHelper.getActivePage().getEditorReferences().length);
		assertNotNull(Activator.getSpecManager().getSpecLoaded());

		// Select tree
		SWTBotView specExplorer = bot.viewById(ToolboxExplorer.VIEW_ID);
		specExplorer.setFocus();

		// select tree items
		final SWTBotTree specExplorerTree = specExplorer.bot().tree();
		specExplorerTree.select(bot.tree().getTreeItem("SpecA [ " + fileA.getName() + " ]"),
				bot.tree().getTreeItem("SpecB [ " + fileB.getName() + " ]"));
		
		// main menu delete
		bot.menu("Edit").menu("Delete").click();

		// click the two dialogs that confirm deletion
		bot.shell("Delete specification?").activate();
		bot.button("Yes").click();
		bot.shell("Delete specification?").activate();
		bot.button("Yes").click();
		
		// Make sure all specs are gone
		assertEquals(0, Activator.getSpecManager().getSpecs().size());
		
		// Make sure no editor remained open
		assertEquals(0, UIHelper.getActivePage().getEditorReferences().length);
	}

	@AfterClass
	public static void sleep() {
		bot.sleep(2000);
	}
}
