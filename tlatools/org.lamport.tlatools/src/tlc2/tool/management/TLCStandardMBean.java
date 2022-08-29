// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.management;

import tlc2.TLCGlobals;

import javax.management.*;
import java.lang.management.ManagementFactory;

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
     * @return A null bean that makes NPE checks obsolete
     */
    public static TLCStandardMBean getNullTLCStandardMBean() {
        NullTLCStandardMBean nullTLCStandardMBean = null;
        try {
            nullTLCStandardMBean = new NullTLCStandardMBean();
        } catch (final NotCompliantMBeanException e) {
            e.printStackTrace();
        }
        return nullTLCStandardMBean;
    }

    public String getVersion() {
        return TLCGlobals.versionOfTLC;
    }

    public String getRevision() {
        if (TLCGlobals.getRevision() == null) {
            return "N/A";
        }
        return TLCGlobals.getRevision();
    }

    /**
     * Registers a new MBean with the platform's MBean server after which this MBean will be visible in JMX.
     *
     * @param objectName The name under which to register this mbean
     * @return true iff successfully registered
     * @see MBeanServer#registerMBean(Object, ObjectName)
     */
    protected boolean registerMBean(final String objectName) {
        // register monitoring mx bean
        final MBeanServer mbs = ManagementFactory.getPlatformMBeanServer();
        try {
            mxbeanName = new ObjectName(objectName);
            mbs.registerMBean(this, mxbeanName);
        } catch (final MalformedObjectNameException | NotCompliantMBeanException | MBeanRegistrationException |
                       InstanceAlreadyExistsException | NullPointerException e1) {
            e1.printStackTrace();
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
            if (mbs.isRegistered(mxbeanName)) {
                mbs.unregisterMBean(mxbeanName);
            }
        } catch (final MBeanRegistrationException | InstanceNotFoundException e) {
            e.printStackTrace();
            return false;
        }
        return true;
    }

    private static class NullTLCStandardMBean extends TLCStandardMBean implements DynamicMBean {

        public NullTLCStandardMBean() throws NotCompliantMBeanException {
            super(DynamicMBean.class);
        }

        /* (non-Javadoc)
         * @see tlc2.tool.management.TLCStandardMBean#registerMBean(java.lang.String)
         */
        @Override
        protected boolean registerMBean(final String objectName) {
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
