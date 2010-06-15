package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

import tla2sany.semantic.LevelNode;

/**
 * A class containing information about a proof step that is
 * needed for updating the status of proof steps.
 * 
 * @author Daniel Ricketts
 *
 */
public class StepTuple implements IStatusProvider
{

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
    private int status;

    public void updateStatus()
    {

        int maxStatus = -1;
        for (Iterator it = children.iterator(); it.hasNext();)
        {
            IStatusProvider statusProvider = (IStatusProvider) it.next();
            maxStatus = Math.max(maxStatus, statusProvider.getStatus());
        }

        if (maxStatus != status)
        {
            status = maxStatus;
            parent.updateStatus();
        }

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
     * @param obligations the obligations to set
     */
    public void addChild(IStatusProvider statusProvider)
    {
        children.add(statusProvider);
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
     * Returns the SANY marker for the step. See
     * {@link ProverHelper#SANY_MARKER} for a description
     * of these markers.
     * 
     * @return the sanyMarker
     */
    public IMarker getSanyMarker()
    {
        return sanyMarker;
    }

    /**
     * @param parent the parent to set
     */
    public void setParent(StepTuple parent)
    {
        this.parent = parent;
    }

    public int getStatus()
    {
        return status;
    }

}
