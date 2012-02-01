// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.management;

import java.lang.management.ManagementFactory;

import javax.management.DynamicMBean;
import javax.management.InstanceAlreadyExistsException;
import javax.management.InstanceNotFoundException;
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

	private ObjectName mxbeanName;

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

	/**
	 * Unregisters the JMX wrapper with the {@link MBeanServer}
	 */
	public boolean unregister() {
		final MBeanServer mbs = ManagementFactory.getPlatformMBeanServer();
		try {
			mbs.unregisterMBean(mxbeanName);
		} catch (MBeanRegistrationException e) {
			e.printStackTrace();
			return false;
		} catch (InstanceNotFoundException e) {
			e.printStackTrace();
			return false;
		}
		return true;
	}
	
	/**
	 * @return A null bean that makes NPE checks obsolete
	 */
	public static TLCStandardMBean getNullTLCStandardMBean() {
		NullTLCStandardMBean nullTLCStandardMBean = null;
		try {
			nullTLCStandardMBean = new NullTLCStandardMBean();
		} catch (NotCompliantMBeanException e) {
			e.printStackTrace();
		}
		return nullTLCStandardMBean;
	}
	
	private static class NullTLCStandardMBean extends TLCStandardMBean implements DynamicMBean {

		public NullTLCStandardMBean() throws NotCompliantMBeanException {
			super(DynamicMBean.class);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.management.TLCStandardMBean#registerMBean(java.lang.String)
		 */
		@Override
		protected boolean registerMBean(String objectName) {
			return true;
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.management.TLCStandardMBean#unregister()
		 */
		@Override
		public boolean unregister() {
			return true;
		}
	}
}
