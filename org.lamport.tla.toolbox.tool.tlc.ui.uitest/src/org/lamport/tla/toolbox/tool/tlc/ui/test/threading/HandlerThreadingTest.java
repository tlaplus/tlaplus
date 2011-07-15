package org.lamport.tla.toolbox.tool.tlc.ui.test.threading;

import java.io.File;
import java.util.Set;

import junit.framework.Assert;

import org.aspectj.lang.JoinPoint;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.matchers.WithText;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.lamport.tla.toolbox.test.threading.MonitorAdaptor;
import org.lamport.tla.toolbox.tool.tlc.ui.test.AbstractTest;

/**
 * Test suite requirements:
 * - vncserver on localhost:1
 * -- on Linux you have to start a window manager explicitly like fluxbox (.vnc/xstartup)
 * - osgi.framework.extensions set to org.eclipse.equinox.weaving.hook
 * - Bundle org.eclipse.equinox.weaving.aspectj explicitly started on runlevel (default - 1) => e.g. 3 
 */
@RunWith(SWTBotJunit4ClassRunner.class)
public class HandlerThreadingTest extends AbstractTest {

	private static final String specB = System
			.getProperty("org.lamport.tla.toolbox.tool.tlc.ui.test.PathToSpecB");
	
	@BeforeClass
	public static void beforeClass() {
		// mimic super
		AbstractTest.beforeClass();

		// If this assert fails see http://wiki.eclipse.org/JDT_weaving_features
		final String osgiFrameworkExtensions = System.getProperty("osgi.framework.extensions");
		Assert.assertNotNull(
				"Test requires Aspectj weaving hook property to be present as an indicator for active weaving support",
				osgiFrameworkExtensions);
		
		// check to make sure the given spec files exist
		Assert.assertTrue("Given spec file does not exist: " + specA, new File(
				specB).exists());

	}

	@Before
	public void setUp() throws Exception {
		super.setUp();
		MonitorAdaptor.reset();
	}
	
	/**
	 * Adds a new spec to the toolbox, opens it
	 * and tests if parsing is done on a non-UI thread
	 * 
	 * @see http://bugzilla.tlaplus.net/show_bug.cgi?id=103
	 */
	@Test
	public void parseSpecInNonUIThread() {
		
		// Open specA 
		SWTBotMenu fileMenu = bot.menu("File");
		SWTBotMenu openSpecMenu = fileMenu.menu("Open Spec");
		SWTBotMenu addNewSpecMenu = openSpecMenu.menu("Add New Spec...");
		addNewSpecMenu.click();

		bot.textWithLabel("Root-module file:").setText(specA);
		bot.button("Finish").click();
		
		assertNoBackendCodeInUIThread();

		// Open specB
		addNewSpecMenu.click();

		bot.textWithLabel("Root-module file:").setText(specB);
		bot.button("Finish").click();
		
		assertNoBackendCodeInUIThread();
		
		final String specName = getSpecName(new File(specA));

		// increase timeout since farsite spec takes a long time to parse
		final long timeout = SWTBotPreferences.TIMEOUT * 3;
		
		// specs are created in non-UI thread asynchronously which causes a
		// delay before the menu entry becomes available
		bot.waitUntil(Conditions.waitForMenu(bot.activeShell(),
				WithText.<MenuItem> withText(specName)), timeout);

		// Go back to previous spec
		openSpecMenu.menu(specName);

		assertNoBackendCodeInUIThread();
	}

	/**
	 * Checks how many invocations of backend code have happend inside the UI thread
	 */
	private void assertNoBackendCodeInUIThread() {
		
		// Check if MonitorAspect has been enabled
		Assert.assertTrue("Test requires active MonitorAspect aspect!", MonitorAdaptor.aspectIsActive());

		if(MonitorAdaptor.hasTriggeredBackendCode()) {
			Set<JoinPoint> joinPoints = MonitorAdaptor.getTriggeredJoinPoints();
			for (JoinPoint joinPoint : joinPoints) {
				System.err.println(joinPoint);
			}
		}
		
		Assert.assertFalse(
				"Backend code (e.g. parsing must not be executed in UI thread) times executed: "
						+ MonitorAdaptor.getTriggeredJoinPoints().size(),
				MonitorAdaptor.hasTriggeredBackendCode());
		// Resets the counting adapter for UI thread backend invocations
		MonitorAdaptor.reset();
	}
}
