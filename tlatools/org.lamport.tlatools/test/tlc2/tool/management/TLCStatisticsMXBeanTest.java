package tlc2.tool.management;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.lang.management.ManagementFactory;
import java.util.Arrays;
import java.util.Set;
import java.util.stream.Collectors;

import javax.management.MBeanAttributeInfo;
import javax.management.ObjectName;

import org.junit.Test;

import tlc2.tool.distributed.management.TLCServerMXWrapper;

public class TLCStatisticsMXBeanTest {

	@Test
	public void localCheckerExposesProgressWithoutCurrentState() throws Exception {
		assertProgressAttributes(new ModelCheckerMXWrapper(null, null));
	}

	@Test
	public void distributedCheckerExposesProgressWithoutCurrentState() throws Exception {
		assertProgressAttributes(new TLCServerMXWrapper(null));
	}

	private static void assertProgressAttributes(final TLCStandardMBean wrapper) throws Exception {
		try {
			final MBeanAttributeInfo[] attributes = ManagementFactory.getPlatformMBeanServer()
					.getMBeanInfo(new ObjectName(ModelCheckerMXWrapper.OBJ_NAME)).getAttributes();
			final Set<String> names = Arrays.stream(attributes)
					.map(MBeanAttributeInfo::getName).collect(Collectors.toSet());

			assertFalse("CurrentState polling must not be exposed over JMX", names.contains("CurrentState"));
			assertTrue(names.containsAll(Arrays.asList("StatesGenerated", "StateQueueSize", "Progress")));
		} finally {
			wrapper.unregister();
		}
	}
}
