package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

import tla2sany.st.Location;

/**
 * A class containing information about a proof step that is
 * needed for updating the status of proof steps.
 * 
 * @author Daniel Ricketts
 *
 */
public class StepTuple implements IStatusProvider
{

    /**
     * The parent of this step. Will be null
     * if the step has no parent.
     */
    private StepTuple parent;
    /**
     * The SANY marker for the step. See
     * {@link ProverHelper#SANY_MARKER} for a description
     * of these markers.
     */
    private IMarker sanyMarker;
    /**
     * A list of {@link IStatusProvider}s that
     * are the children of this step.
     */
    private List children;
    /**
     * The status of the step. This is initially set to
     * unknown. If children are added, the status will
     * then be updated.
     */
    private int status = ProverHelper.STEP_UNKNOWN_INT;

    /**
     * Updates the status of this step. Creates a new status
     * marker if the status has changed. Calls {@link #updateStatus()}
     * on its parent if the parent is not null and the status has changed.
     */
    public void updateStatus()
    {

        int maxStatus = -1;
        for (Iterator it = children.iterator(); it.hasNext();)
        {
            IStatusProvider statusProvider = (IStatusProvider) it.next();
            maxStatus = Math.max(maxStatus, statusProvider.getStatus());
        }

        setStatus(maxStatus);

    }

    /**
     * Sets the step node from which this obligation
     * was generated. Also creates all step tuples
     * for parents.
     * 
     * @param stepNode the stepNode to set
     */
    public StepTuple()
    {
        children = new LinkedList();
    }

    /**
     * Adds a child to this step. Updates the status.
     * 
     * @param obligations the obligations to set
     */
    public void addChild(IStatusProvider statusProvider)
    {
        children.add(statusProvider);
        updateStatus();
    }

    /**
     * Sets the SANY marker for the step. See
     * {@link ProverHelper#SANY_MARKER} for a description
     * of these markers.
     * 
     * @param sanyMarker the sanyMarker to set
     */
    public void setSanyMarker(IMarker sanyMarker)
    {
        this.sanyMarker = sanyMarker;
    }

    /**
     * @param parent the parent to set
     */
    public void setParent(StepTuple parent)
    {
        this.parent = parent;
    }

    /**
     * Returns the current status of this step.
     */
    public int getStatus()
    {
        return status;
    }

    /**
     * Sets the current status of this step. Updates
     * the status marker for this step if the status has changed.
     * Updates the parent if the parent is not null and the status
     * has changed for this step.
     * 
     * @param newStatus
     */
    public void setStatus(int newStatus)
    {
        if (this.status != newStatus)
        {
            // DEBUG
            Location stepLoc = ProverHelper.stringToLoc(sanyMarker.getAttribute(ProverHelper.SANY_LOC_ATR, ""));
            System.out.println("The status of the step located at " + stepLoc + " is now "
                    + ProverHelper.statusIntToStatusString(newStatus));
            // END DEBUG
            
            this.status = newStatus;
            ProverHelper.newStepStatusMarker(sanyMarker, ProverHelper.statusIntToStatusString(newStatus));
            if (parent != null)
            {
                parent.updateStatus();
            }
        }
    }
    
    /**
     * Returns the SANY marker associated with this step.
     * @return
     */
    public IMarker getSanyMarker()
    {
        return sanyMarker;
    }

}
