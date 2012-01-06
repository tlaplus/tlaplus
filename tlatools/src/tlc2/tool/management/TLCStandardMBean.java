// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.management;

import java.lang.management.ManagementFactory;

import javax.management.InstanceAlreadyExistsException;
import javax.management.MBeanRegistrationException;
import javax.management.MBeanServer;
import javax.management.MalformedObjectNameException;
import javax.management.NotCompliantMBeanException;
import javax.management.ObjectName;
import javax.management.StandardMBean;

/**
 * @author Markus Alexander Kuppe
 */
public abstract class TLCStandardMBean extends StandardMBean {

	protected TLCStandardMBean(@SuppressWarnings("rawtypes") final Class mbeanInterface)
			throws NotCompliantMBeanException {
		super(mbeanInterface);
	}

	/**
	 * Registers a new MBean with the platform's MBean server after which this MBean will be visible in JMX.
	 * 
	 * 
	 * @param objectName The name under which to register this mbean
	 * @return true iff successfully registered
	 * 
	 * @see MBeanServer#registerMBean(Object, ObjectName)
	 */
	protected boolean registerMBean(final String objectName){
		// register monitoring mx bean
		MBeanServer mbs = ManagementFactory.getPlatformMBeanServer(); 
        ObjectName mxbeanName;
		try {
			mxbeanName = new ObjectName(objectName);
			mbs.registerMBean(this, mxbeanName);
		} catch (MalformedObjectNameException e1) {
			e1.printStackTrace();
			return false;
		} catch (NullPointerException e1) {
			e1.printStackTrace();
			return false;
		} catch (InstanceAlreadyExistsException e) {
			e.printStackTrace();
			return false;
		} catch (MBeanRegistrationException e) {
			e.printStackTrace();
			return false;
		} catch (NotCompliantMBeanException e) {
			e.printStackTrace();
			return false;
		}
		return true;
	}
}
