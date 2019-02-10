/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool.management;

import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Date;

import javax.management.MBeanServerConnection;
import javax.management.MBeanServerInvocationHandler;
import javax.management.MalformedObjectNameException;
import javax.management.ObjectName;
import javax.management.remote.JMXConnector;
import javax.management.remote.JMXConnectorFactory;
import javax.management.remote.JMXServiceURL;

import tlc2.tool.distributed.management.TLCStatisticsMXBean;

public class StateMonitor {

	private static final SimpleDateFormat SDF = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss"); //$NON-NLS-1$ 

	public static void main(String[] args) throws IOException, MalformedObjectNameException, InterruptedException {
		int interval = 10; // 10sec interval by default
		if (args.length == 2) {
			interval = Integer.valueOf(args[1]);
		}
		
		JMXServiceURL url = null;
		try {
			final Integer pid = Integer.valueOf(args[0]);
			//TODO the strong encapsulation is forbidding us from compiling the following line:
			final String address = "broken"; //jdk.internal.agent.ConnectorAddressLink.importFrom(pid);
			url = new JMXServiceURL(address);
			System.out.printf("Connecting to TLC with pid %s running at %s.\n(Hit Ctrl+c to terminate)\n", pid, url);
		} catch (NumberFormatException nfe) {
			// If monitored VM has been launched with explicit port, use service url instead
			// of CAL:
			// -Dcom.sun.management.jmxremote
			// -Dcom.sun.management.jmxremote.port=10995
			// -Dcom.sun.management.jmxremote.ssl=false
			// -Dcom.sun.management.jmxremote.authenticate=false
			// => "service:jmx:rmi:///jndi/rmi://localhost:10995/jmxrmi".
			url = new JMXServiceURL("service:jmx:rmi:///jndi/rmi://" + args[0] + "/jmxrmi");
			System.out.printf("Connecting to TLC running at %s.\n(Hit Ctrl+c to terminate)\n", url);
		}
		
		final JMXConnector jmxConnector = JMXConnectorFactory.connect(url);
		final MBeanServerConnection mbeanServerConnection = jmxConnector.getMBeanServerConnection();
		// ObjectName should be same as your MBean name
		final ObjectName mbeanName = new ObjectName(ModelCheckerMXWrapper.OBJ_NAME);

		// Get MBean proxy instance that will be used to make calls to registered MBean
		final TLCStatisticsMXBean mbeanProxy = (TLCStatisticsMXBean) MBeanServerInvocationHandler
				.newProxyInstance(mbeanServerConnection, mbeanName, TLCStatisticsMXBean.class, true);

		while (true) {
			System.out.printf("############ %s ############\n%s", SDF.format(new Date()), mbeanProxy.getCurrentState());
			Thread.sleep(interval * 1000L);
		}
		
		// No need to close the connection because JVM itself terminates.
		//jmxConnector.close();
	}
}
