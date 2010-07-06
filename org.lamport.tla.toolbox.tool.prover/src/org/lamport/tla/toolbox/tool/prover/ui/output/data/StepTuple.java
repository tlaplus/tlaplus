package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob;
import org.lamport.tla.toolbox.tool.prover.ui.preference.ProverPreferencePage;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

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
    // /**
    // * The status of the step. This is initially set to
    // * unknown. If children are added, the status will
    // * then be updated.
    // */
    // private int status = ProverHelper.STEP_UNKNOWN_INT;
    /**
     * The ith element of the array gives
     * the value of the (i+1)st color predicate
     * for this step. Color predicates
     * are numbered starting at 1.
     */
    private boolean[] colorPredicateValues;
    /**
     * The job which launched the prover. This step tuple
     * contains the status for that launch of the prover.
     */
    private ProverJob proverJob;

    /**
     * Updates the status of this step. Creates a new status
     * marker if the status has changed. Calls {@link #updateStatus()}
     * on its parent if the parent is not null and the value
     * of one of the color predicates for this step has changed.
     */
    public void updateStatus()
    {

        boolean isLeaf = sanyMarker.getAttribute(ProverHelper.SANY_IS_LEAF_ATR, false);
        ColorPredicate[] colorPredicates = proverJob.getColorPredicates();

        /*
         * Iterate through all color predicates.
         * The value of each color predicate for this step
         * is given by
         * 
         * /\ \/ /\ It is an `every' predicate
                 /\ The predicate is true for every child.
              \/ /\ It is a `some' predicate
                 /\ The predicate is true for some child
           /\ \/ It is not a `leaf' predicate
              \/ This is a leaf step
         */

        /*
         * For each predicate, this will be set to an array of boolean values, one
         * entry per child indicating if the color predicate is true
         * for that child.
         */
        boolean[] childPredicateValues = new boolean[children.size()];
        /*
         * There will be one element in the array for each child giving
         * its state number.
         */
        int[] obligationStateNumbers = new int[children.size()];
        if (isLeaf)
        {
            for (int i = 0; i < obligationStateNumbers.length; i++)
            {
                obligationStateNumbers[i] = ((ObligationStatus) children.get(i)).getObligationState();
            }
        }

        // true if the value of at least one color predicate has changed
        boolean predicateChanged = false;
        for (int i = 0; i < colorPredicateValues.length; i++)
        {

            if (isLeaf)
            {

                boolean newPredicateValue = colorPredicates[i].satisfiedByObligations(obligationStateNumbers);
                predicateChanged = predicateChanged || (colorPredicateValues[i] != newPredicateValue);
                colorPredicateValues[i] = newPredicateValue;
            } else
            {
                int childNum = 0;
                for (Iterator it = children.iterator(); it.hasNext();)
                {
                    childPredicateValues[childNum] = ((StepTuple) it.next()).getColorPredicateValues()[i];
                    childNum++;
                }
                boolean newPredicateValue = colorPredicates[i].satisfiedBasedOnChildren(childPredicateValues);
                predicateChanged = predicateChanged || (colorPredicateValues[i] != newPredicateValue);
                colorPredicateValues[i] = newPredicateValue;
            }
        }

        /*
         * If at least one color predicate has changed then recompute the
         * minimum true color predicate.
         */
        if (predicateChanged)
        {
            int minimum = ProverPreferencePage.NUM_STATUS_COLORS + 1;
            for (int i = 0; i < colorPredicateValues.length; i++)
            {
                if (colorPredicateValues[i])
                {
                    minimum = i + 1;
                    break;
                }
            }

            if (minimum <= ProverPreferencePage.NUM_STATUS_COLORS)
            {
                ProverHelper.newStepStatusMarker(sanyMarker, minimum);
            }

            if (parent != null)
            {
                parent.updateStatus();
            }

        }

    }

    /**
     * Creates the step tuple with initial status
     * {@link ProverHelper#STEP_UNKNOWN_INT}.
     * @param proverJob the job which launched the prover.
     */
    public StepTuple(ProverJob proverJob)
    {
        this.proverJob = proverJob;
        children = new ArrayList();
        colorPredicateValues = new boolean[ProverPreferencePage.NUM_STATUS_COLORS];
    }

    /**
     * Adds a child to this step. Updates the status.
     * Updating the status calls {@link #updateStatus()}.
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
     * Returns the current value of the color predicates for
     * this obligation.
     */
    public boolean[] getColorPredicateValues()
    {
        return colorPredicateValues;
    }

    // /**
    // * Sets the current status of this step. Updates
    // * the status marker for this step if the status has changed.
    // * Updates the parent if the parent is not null and the status
    // * has changed for this step.
    // *
    // * @param newStatus
    // */
    // public void setStatus(int newStatus)
    // {
    // if (this.status != newStatus)
    // {
    // // DEBUG
    // // Location stepLoc = ProverHelper.stringToLoc(sanyMarker.getAttribute(ProverHelper.SANY_LOC_ATR, ""));
    // // System.out.println("The status of the step located at " + stepLoc + " is now "
    // // + ProverHelper.statusIntToStatusString(newStatus) + " from status int " + newStatus);
    // // END DEBUG
    //
    // this.status = newStatus;
    // ProverHelper.newStepStatusMarker(sanyMarker, null);
    // if (parent != null)
    // {
    // parent.updateStatus();
    // }
    // }
    // }

    /**
     * Returns the SANY marker associated with this step.
     * @return
     */
    public IMarker getSanyMarker()
    {
        return sanyMarker;
    }

}
