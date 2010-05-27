package org.lamport.tla.toolbox.tool.prover.ui.status;

import tla2sany.st.Location;

/**
 * Class representing the status of a proof step.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProofStepStatus
{

    /**
     * Status indicating that for a step, all obligations have proofs that are checked
     */
    public static final String FULLY_CHECKED = "fullyChecked";
    /**
     * Status indicating that for a step, all obligations have proofs or proof omitted that are checked.
     */
    public static final String CHECK_OR_EXPL_OMIT = "checkedOrExplicitOmitStep";
    /**
     * Status indicating that for a step, all written proofs are checked.
     */
    public static final String WRITTEN_PROOFS_CHECKED = "writtenProofsCheckedStep";
    /**
     * Status indicating that for a step, there exists an obligation that was rejected.
     */
    public static final String FAILED_OBS_FOR_STEP = "obligationFailedForStep";

    private String status;
    private Location location;

    /**
     * Status should be one of the constants in this class.
     * 
     * @param status
     * @param location
     */
    public ProofStepStatus(String status, Location location)
    {
        this.status = status;
        this.location = location;
    }

    public String getStatus()
    {
        return status;
    }

    public Location getLocation()
    {
        return location;
    }

}
