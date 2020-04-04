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
import java.util.Comparator;
import java.util.Date;
import java.util.List;
import java.util.Scanner;

import javax.management.MBeanServerConnection;
import javax.management.MBeanServerInvocationHandler;
import javax.management.MalformedObjectNameException;
import javax.management.ObjectName;
import javax.management.remote.JMXConnector;
import javax.management.remote.JMXConnectorFactory;
import javax.management.remote.JMXServiceURL;

import com.sun.tools.attach.AttachNotSupportedException;
import com.sun.tools.attach.VirtualMachine;
import com.sun.tools.attach.VirtualMachineDescriptor;

import tlc2.tool.distributed.management.TLCStatisticsMXBean;

/*
 * This class does not compile in the Eclipse IDE on Ubuntu 18.04 with JaveSE1.8 linked to the
 * 8u201-1~webupd8~1 JVM installed from webupd8 and probably fails to compile elsewhere too,
 * because Eclipse fails to find the com.sun.tools.attach classes.  The fix is to add the JDK's
 * tools.jar to the Java installation.  On Java 11 this doesn't seem to be an issue.
 */
public class StateMonitor {

	private static final SimpleDateFormat SDF = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss"); //$NON-NLS-1$ 

	public static void main(String[] args) throws IOException, MalformedObjectNameException, InterruptedException, AttachNotSupportedException {
		int interval = 10; // 10sec interval by default
		if (args.length == 1) {
			interval = Integer.valueOf(args[0]);
		}
		
		JMXServiceURL url = null;
		try {
			final List<VirtualMachineDescriptor> vmds = com.sun.tools.attach.VirtualMachine.list();
			vmds.sort(new Comparator<VirtualMachineDescriptor>() {
				@Override
				public int compare(VirtualMachineDescriptor o1, VirtualMachineDescriptor o2) {
					// Sort those vms higher whose display name contains TLC.
					final boolean c1 = o1.displayName().contains("TLC");
					final boolean c2 = o2.displayName().contains("TLC");
					if (c1 ^ c2) {
						if (c1) {
							return -1;
						}
						return 1;
					}
					return 0;
				}
			});
			
			int index = 1;
			try (Scanner scanner = new Scanner(System.in)) {
				rd: while (true) {
					index = 1;
					System.out.printf("============\n");
					for (VirtualMachineDescriptor vmd : vmds) {
						System.out.printf("[%s]: pid=%s, name=%s\n", index++, vmd.id(), vmd.displayName());
					}
					System.out.printf("Please select the number of the Java VM running TLC to connect to:\n");
					if (scanner.hasNextInt()) {
						index = scanner.nextInt();
						
						// Check index is within bounds.
						if (index >= 1 && index <= vmds.size()) {
							break rd;
						}
					}
					System.err.printf("Invalid selection %s\n", index);
				}
			}
			final VirtualMachineDescriptor tlcVMD = vmds.get(index - 1);
			final VirtualMachine vm = tlcVMD.provider().attachVirtualMachine(tlcVMD);
			final String address = vm.startLocalManagementAgent();
			url = new JMXServiceURL(address);
			System.out.printf("Connecting to TLC running at %s.\n(Hit Ctrl+c to terminate)\n", url);
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
