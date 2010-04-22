package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import org.eclipse.core.runtime.IPath;

import tla2sany.st.Location;

/**
 * Contains data about the status of an obligation.
 * 
 * @author drickett
 *
 */
public class ObligationStatus extends TLAPMData
{

    /**
     * Constant for verified status.
     */
    public static final int STATUS_VERIFIED = 0;
    /**
     * Constant for rejected status.
     */
    public static final int STATUS_REJECTED = 1;
    /**
     * Constant for unknown status.
     */
    public static final int STATUS_UNKNOWN = -1;

    private int status;
    /**
     * Location in module of obligation.
     */
    private Location location;

    /**
     * 
     * @param offset
     * @param length
     * @param type
     * @param status see status constants in this class.
     */
    public ObligationStatus(int status, Location location, IPath modulePath)
    {

        super(modulePath);

        this.status = status;
        this.location = location;
    }

    public int getStatus()
    {
        return status;
    }

    public Location getLocation()
    {
        return location;
    }

}
