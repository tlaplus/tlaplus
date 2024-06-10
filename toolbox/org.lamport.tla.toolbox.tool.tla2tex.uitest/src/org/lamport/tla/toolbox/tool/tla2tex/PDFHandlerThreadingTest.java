package org.lamport.tla.toolbox.tool.tla2tex;

import java.io.File;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.lamport.tla.toolbox.test.RCPTestSetupHelper;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;

@RunWith(SWTBotJunit4ClassRunner.class)
public class PDFHandlerThreadingTest {
	
	private static SWTWorkbenchBot bot;

	private static final String specA = System.getProperty("org.lamport.tla.toolbox.tool.tlc.ui.test.PathToSpecA",
			RCPTestSetupHelper.getAbsolutePath("org.lamport.tla.toolbox.uitest",
					"farsite/DistributedSystemModule.tla"));
	private static final String specB = System.getProperty("org.lamport.tla.toolbox.tool.tlc.ui.test.PathToSpecB",
			RCPTestSetupHelper.getAbsolutePath("org.lamport.tla.toolbox.uitest", "DieHard/DieHard.tla"));
	
	@BeforeClass
	public static void beforeClass() throws Exception {
		
		// If this assert fails see http://wiki.eclipse.org/JDT_weaving_features
		final String osgiFrameworkExtensions = System.getProperty("osgi.framework.extensions");
		Assert.assertNotNull(
				"Test requires Aspectj weaving hook property to be present as an indicator for active weaving support",
				osgiFrameworkExtensions);
		
		// Reset the workbench
		RCPTestSetupHelper.beforeClass();
		
		// check to make sure the given spec files exist
		Assert.assertTrue("Given spec file does not exist: " + specA, new File(
				specA).exists());
		Assert.assertTrue("Given spec file does not exist: " + specA, new File(
				specB).exists());
		
		bot = new SWTWorkbenchBot();
	}
	
	@Test @Ignore("not ready yet")
	public void producePDFInNonUIThread() throws InterruptedException {
		
		// Open specA 
		SWTBotMenu fileMenu = bot.menu("File");
		SWTBotMenu openSpecMenu = fileMenu.menu("Open Spec");
		SWTBotMenu addNewSpecMenu = openSpecMenu.menu("Add New Spec...");
		addNewSpecMenu.click();

		bot.textWithLabel("Root-module file:").setText(specA);
		bot.button("Finish").click();
		
		// generate PDF
		SWTBotMenu pdfMenu = fileMenu.menu("Produce PDF Version");
		pdfMenu.click();
		
		// wait for the browser to show up with the generated PDF
		SWTBotEditor swtBotEditor = bot.editorById(OpenSpecHandler.TLA_EDITOR);
		Assert.assertNotNull(swtBotEditor);
	}
}
