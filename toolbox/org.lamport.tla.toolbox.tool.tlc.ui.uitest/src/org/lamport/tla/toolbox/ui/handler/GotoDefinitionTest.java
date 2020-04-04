package org.lamport.tla.toolbox.ui.handler;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.TimeUnit;

import org.apache.commons.io.IOUtils;
import org.eclipse.jface.text.Region;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.matchers.WithText;
import org.eclipse.swtbot.swt.finder.utils.FileUtils;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.junit.Assert;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.lamport.tla.toolbox.editor.basic.tla.TokenSpec;
import org.lamport.tla.toolbox.test.RCPTestSetupHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.test.AbstractTest;
import org.lamport.tla.toolbox.util.UIHelper;


/**
 * This test started life to provide test cases related to GitHub issue #106.
 */
@RunWith(SWTBotJunit4ClassRunner.class)
public class GotoDefinitionTest extends AbstractTest {
	
	private static final String TEST_SPEC_NAME = "GotoDefinition";
	private static final String REPOSITORY_SPEC_PATH = System.getProperty("org.lamport.tla.toolbox.tool.tlc.ui.test.PathToSpec",
	                                                                      RCPTestSetupHelper.getAbsolutePath("org.lamport.tla.toolbox.uitest",
	                                                                                                         "farsite/GotoDefinition.tla"));

	@BeforeClass
	public static void beforeClass () {
		// mimic super
		AbstractTest.beforeClass();
	}

	@Before
	public void setUp () throws Exception {
		super.setUp();

		// load our known spec
		SWTBotMenu fileMenu = bot.menu("File");
		SWTBotMenu openSpecMenu = fileMenu.menu("Open Spec");
		SWTBotMenu addNewSpecMenu = openSpecMenu.menu("Add New Spec...");
		addNewSpecMenu.click();
		
		String path = System.getProperty("java.io.tmpdir") + File.separator + "GDTest" + System.currentTimeMillis();
		FileUtils.mkdirs(path);
		
		// Put a copy of the spec into our temporary working directory
		path += File.separator + TEST_SPEC_NAME + TLA_SUFFIX;
		FileInputStream fis = null;
		FileOutputStream fos = null;
		try {
		    fis = new FileInputStream(REPOSITORY_SPEC_PATH);
		    fos = new FileOutputStream(path);
		    
		    IOUtils.copy(fis, fos);
		}
		finally {
		    IOUtils.closeQuietly(fis);
		    IOUtils.closeQuietly(fos);
		}

		bot.textWithLabel("Root-module file:").setText(path);
		bot.button("Finish").click();

		bot.waitUntil(Conditions.waitForMenu(bot.activeShell(), WithText.<MenuItem> withText(TEST_SPEC_NAME)));
		
		checkSpecAndModelExistenceAPI(TEST_SPEC_NAME, null);
	}
	
	/**
	 * See first issue mentioned in https://github.com/tlaplus/tlaplus/issues/106
	 * 
	 * We don't need to test the hyperlink jump, we only need to test that the TokenSpec instance returned by
	 *     TokenSpec.findCurrentTokenSpec(IRegion) has a non-null resolvedSymbol attribute.
	 * @throws InterruptedException 
	 */
	@Test
	public void verifyTokenSpecSymbolResolution () throws InterruptedException {
		final BlockingQueue<TokenSpec> queue = new ArrayBlockingQueue<TokenSpec>(1);
		final Region r = new Region(193, 0);
	    // This region is expected to place the cursor just prior to the subscripted identifier, the 's' in "..._s" in:
	    //             Spec == s = "" /\ [][Next(s)]_s
	    UIHelper.runUIAsync(new Runnable() {
			@Override
			public void run() {
				queue.add(TokenSpec.findCurrentTokenSpec(r));
			}
		});
		
		final TokenSpec ts = queue.poll(15, TimeUnit.SECONDS);

		Assert.assertNotNull("TokenSpec was unable to find any token at " + r.toString(), ts);

		Assert.assertEquals("TokenSpec was not for the expected token, perhaps someone has changed GotoDefinition.tla?",
				"_s", ts.token);

		Assert.assertNotNull(
				"TokenSpec was unable to resolve the symbol for the token [" + ts.token + "] at " + r.toString(),
				ts.resolvedSymbol);
	    
	    // No real reason this need be done from a test functionality perspective
        SWTBotEditor activeEditor = bot.activeEditor();
        activeEditor.close();
	}

}
