package org.lamport.tla.toolbox.tool.prover.ui.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.AssertionFailedException;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.prover.job.ITLAPMOptions;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob.ProverJobMatcher;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.dialog.TLAPMErrorDialog;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ColorPredicate;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ErrorMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatus;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepTuple;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.WarningMessage;
import org.lamport.tla.toolbox.tool.prover.ui.preference.ProverPreferencePage;
import org.lamport.tla.toolbox.tool.prover.ui.preference.ProverSecondPreferencePage;
import org.lamport.tla.toolbox.tool.prover.ui.view.ObligationsView;
import org.lamport.tla.toolbox.ui.dialog.InformationDialog;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.LeafProofNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.UseOrHideNode;
import tla2sany.st.Location;
import util.UniqueString;

/**
 * Helper methods for the launching of the prover.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProverHelper
{

    /*********************************************************************
     * Obligation marker and marker attribute constants.                 *
     *********************************************************************/
    /**
     * Type of a marker that contains information about an obligation. 
     */
    public static final String OBLIGATION_MARKER = "org.lamport.tla.toolbox.tool.prover.obligation";
    /**
     * Attribute on an obligation marker giving the integer id of the obligation.
     */
    public static final String OBLIGATION_ID = "org.lamport.tla.toolbox.tool.prover.obId";
    // /**
    // * Attribute on an obligation marker giving the formatted String of the obligation.
    // */
    // public static final String OBLIGATION_STRING = "org.lamport.tla.toolbox.tool.prover.obString";
    // /**
    // * Attribute on an obligation marker giving the current state of the obligation. This is
    // * an int corresponding to a state. Obligation states are explained in {@link ColorPredicate}.
    // */
    // public static final String OBLIGATION_STATE = "org.lamport.tla.toolbox.tool.prover.obState";
    // /**
    // * String attribute on an obligation marker giving the location of the obligation as reported by
    // * tlapm. Note that this location is not necessarily the same as the markers current location
    // * in the editor, nor is it necessarily the same location as reported by the markers
    // * {@link IMarker#CHAR_END} and {@link IMarker#CHAR_START} attributes. These attributes are
    // * somewhat "sticky". They can change with some user editing.
    // *
    // * The string value should be set from a {@link Location}
    // * using {@link #locToString(Location)}. The {@link Location} object
    // * can be retreived using {@link #stringToLoc(String)}.
    // */
    // public static final String OBLIGATION_LOCATION = "org.lamport.tla.toolbox.tool.prover.obLoc";

    /******************************************************************************
     * SANY marker and marker attribute constants.                                *
     ******************************************************************************/
    /**
     * Type of marker that contains SANY information about a proof step.
     * In particular, it contains the location of the proof step as reported
     * by SANY when the prover was last launched for a step status update.
     * This location may not be the same as the marker's location
     * because the marker is sticky and the module may have been edited since
     * the prover was last launch for a status check.
     */
    public static final String SANY_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.sanyMarker";
    /**
     * String attribute on a SANY marker giving the location of the proof
     * step the last time the prover was launched for a proof step
     * status check. The string value should be set from a {@link Location}
     * using {@link #locToString(Location)}. This location
     * is the beginning of the step to the end of the statement
     * of the step.
     */
    public static final String SANY_LOC_ATR = "org.lamport.tla.toolbox.tool.prover.ui.sanyLoc";
    /**
     * Boolean attribute on a SANY marker that should be true iff the step is
     * a step with no children or with only a leaf proof.
     */
    public static final String SANY_IS_LEAF_ATR = "org.lamport.tla.toolbox.tool.prover.ui.isLeafStep";

    /**
     * Delimiter used for representing
     * locations as strings.
     */
    public static final String LOC_DELIM = ":";

    /******************************************************************************
     * Obligation string status constants as returned by the TLAPM                *
     ******************************************************************************/
    /**
     * Obligation status that occurs when
     * zenon or isabelle "takes time" to prove an obligation.
     */
    public static final String BEING_PROVED = "being proved";
    /**
     * Obligation status indicating that the obligation
     * has been proved by the value of the "prover" field.
     */
    public static final String PROVED = "proved";
    /**
     * Obligation status indicating that proving the obligation
     * has failed.
     */
    public static final String FAILED = "failed";
    /**
     * Obligation status indicating that the obligation
     * is considered trivial.
     */
    public static final String TRIVIAL = "trivial";
    // /**
    // * Obligation status indicating that the obligation
    // * has been skipped by the value of the "meth" field.
    // */
    // public static final String SKIPPED = "skipped";
    // /**
    // * Obligation status indicating that the obligation
    // * has been checked.
    // */
    // public static final String CHECKED = "checked";
    // /**
    // * Obligation status indicating that the checking
    // * has failed on the obligation.
    // */
    // public static final String CHECKING_FAILED = "checking failed";
    // /**
    // * Obligation status indicating that checking an obligation
    // * was interrupted.
    // */
    // public static final String CHECKING_INTERUPTED = "checking interrupted";
    /**
     * Obligation status indicating that proving the obligation
     * was interrupted.
     */
    public static final String INTERUPTED = "interrupted";
    // /**
    // * Obligation status indicating that the obligation
    // * has been proved in a prior run of the prover.
    // */
    // public static final String PROVED_ALREADY = "proved (already processed)";
    // /**
    // * Obligation status indicating that the obligation
    // * was determined to be trivial in a prior run of the prover.
    // */
    // public static final String TRIVIAL_ALREADY = "trivial (already processed)";
    // /**
    // * Obligation status indicating that proving the obligation
    // * failed in a prior run of the prover.
    // */
    // public static final String FAILED_ALREADY = "failed (already processed)";
    // /**
    // * Obligation status indicating that the obligation
    // * has been checked in a prior run of the prover.
    // */
    // public static final String CHECKED_ALREADY = "checked (already processed)";
    /**
     * Obligation status indicating that the obligation
     * has not yet been sent anywhere to be proved.
     */
    public static final String TO_BE_PROVED = "to be proved";

    /***********************************************************************************
     * Step status marker types.                                                       *
     ***********************************************************************************/
    /**
     * Marker type corresponding to the status {@link StepStatusMessage#PROVING_FAILED} for non-leaf
     * steps (steps with children).
     */
    public static final String STEP_PROVING_FAILED_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.stepProvingFailed";
    /**
     * Marker type corresponding to the status {@link StepStatusMessage#CHECKING_FAILED}
     */
    public static final String STEP_CHECKING_FAILED_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.stepCheckingFailed";
    /**
     * Marker type corresponding to the status {@link StepStatusMessage#MISSING_PROOFS}
     */
    public static final String STEP_MISSING_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.stepMissing";
    /**
     * Marker type corresponding to the status {@link StepStatusMessage#OMITTED}
     */
    public static final String STEP_OMITTED_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.stepOmitted";
    /**
     * Marker type corresponding to the status {@link StepStatusMessage#CHECKED}
     */
    public static final String STEP_CHECKED_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.stepChecked";
    /**
     * Marker type corresponding to the status {@link StepStatusMessage#PROVED}
     */
    public static final String STEP_PROVED_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.stepProved";
    /**
     * Marker type corresponding to the status {@link StepStatusMessage#BEING_PROVED}.
     */
    public static final String STEP_BEING_PROVED_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.stepBeingProved";
    /**
     * Marker type corresponding to the status {@link StepStatusMessage#PROVING_FAILED} for leaf
     * steps (steps with a leaf proof or with no children.
     */
    public static final String STEP_LEAF_FAILED = "org.lamport.tla.toolbox.tool.prover.ui.leafFailed";
    /**
     * Super type for the following four marker types for step status.
     */
    public static final String STEP_STATUS_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.proofStepStatus";

    /**************************************************************************************
     * Step status integers. Used for easy computation of max status.                     *
     **************************************************************************************/
    public static final int STEP_CHECKED_INT = 0;
    public static final int STEP_PROVED_INT = 1;
    public static final int STEP_TO_BE_PROVED_INT = 2;
    public static final int STEP_BEING_PROVED_INT = 3;
    public static final int STEP_PROOF_OMITTED_INT = 4;
    public static final int STEP_PROOF_MISSING_INT = 5;
    public static final int STEP_PROVING_FAILED_INT = 6;
    public static final int STEP_CHECKING_FAILED_INT = 100;
    public static final int STEP_UNKNOWN_INT = -1;

    /**
     * Removes all markers indicating obligation information on  a resource. Does
     * nothing if the resource does not exist. It deletes these markers only at one level
     * under the resource. That is, if the resource is a directory, it deletes markers
     * on its children.
     * 
     * @param resource
     * @throws CoreException 
     */
    public static void clearObligationMarkers(IResource resource) throws CoreException
    {
        if (resource.exists())
        {
            /*
             * Obligation markers should only be on files directly in the project folder, so we
             * only need to delete markers to depth one. Depth infinite would search any
             * checkpoint folders, which can be slow if there are many files.
             */
            resource.deleteMarkers(OBLIGATION_MARKER, false, IResource.DEPTH_ONE);
        }
    }

    /**
     * Returns true iff the status represents
     * an obligation that is in an "interesting" state.
     * 
     * An obligation is interesting if
     * 
     * \/ At least one backend is trying to prove it.
     * \/ /\ No backends have succeeded.
     *    /\ \/ At least one backend has failed.
     *       \/ At least one backend has been stopped.
     * 
     * @param marker
     * @return
     * @throws CoreException 
     */
    public static boolean isInterestingObligation(ObligationStatus status)
    {
        int obState = status.getObligationState();
        String[] proverStatuses = ColorPredicate.proverStatuses(obState);

        // will be set to true if at least one backend has succeeded
        boolean oneSucceeded = false;
        // will be set to true if at least one backend has failed
        boolean oneFailed = false;
        // will be set to true if at least one backend has been stopped
        boolean oneStopped = false;

        for (int i = 0; i < proverStatuses.length; i++)
        {
            if (proverStatuses[i].equals(ColorPredicate.PROVING_STATUS))
            {
                // At least one backend is trying to prove it.
                return true;
            } else if (proverStatuses[i].equals(ColorPredicate.FAILED_STATUS))
            {
                oneFailed = true;
            } else if (proverStatuses[i].equals(ColorPredicate.STOPPED_STATUS))
            {
                oneStopped = true;
            } else if (proverStatuses[i].equals(ColorPredicate.PROVED_STATUS))
            {
                oneSucceeded = true;
            }
        }

        /*
         * The condition "At least one backend is trying to prove it." is false.
         * Return the value of
         * 
         * /\ No backends have succeeded.
         * /\ \/ At least one backend has failed.
         *    \/ At least one backend has been stopped.
         */
        return !oneSucceeded && (oneFailed || oneStopped);

    }

    /**
     * Returns true iff the status represents
     * an obligation that is currently being proved.
     * 
     * @param status the current obligation status
     * @return
     * @throws CoreException 
     */
    public static boolean isBeingProvedObligation(ObligationStatus status)
    {
        int obState = status.getObligationState();
        String[] proverStatuses = ColorPredicate.proverStatuses(obState);
        for (int i = 0; i < proverStatuses.length; i++)
        {
            if (proverStatuses[i].equals(ColorPredicate.PROVING_STATUS))
            {
                return true;
            }
        }

        return false;
    }

    /**
     * Returns true iff the marker represents an obligation that is
     * finished being processed in any way (proving or checking).
     * 
     * The proverJob gives information about the parameters used to launch
     * the prover.
     * 
     * @param message
     * @param proverJob
     * @return
     * @throws CoreException 
     */
    public static boolean isObligationFinished(ObligationStatusMessage message, ProverJob proverJob)
    {

        String status = message.getStatus();

        boolean isTrivial = status.equals(TRIVIAL);

        return isTrivial || status.equals(PROVED);

    }

    /**
     * Returns all {@link IMarker} of type {@link ProverHelper#OBLIGATION_MARKER}
     * for the currently opened spec. These markers contain information about obligations.
     * 
     * If there is no spec currently open in the toolbox, this returns null.
     * 
     * @return
     * @throws CoreException 
     */
    public static IMarker[] getObMarkersCurSpec() throws CoreException
    {

        if (ToolboxHandle.getCurrentSpec() != null)
        {
            return ToolboxHandle.getCurrentSpec().getProject().findMarkers(OBLIGATION_MARKER, false,
                    IResource.DEPTH_ONE);
        }

        return null;

    }

    /**
     * Returns the {@link Collection} of {@link ObligationStatus}s
     * from the most recent run of the prover if the most recent run
     * of the prover is on the current spec. Returns null if the
     * prover has not yet been launched during this instance of the
     * toolbox or if the most recent run of the prover is not
     * on the current spec.
     * 
     * @return
     */
    public static ObligationStatus[] getObligationStatuses()
    {
        if (ProverJob.getLastJob() == null)
        {
            return null;
        }
        ProverJob lastJob = ProverJob.getLastJob();
        if (ToolboxHandle.getCurrentSpec() == null
                || !lastJob.getModule().getProject().equals(ToolboxHandle.getCurrentSpec().getProject()))
        {
            // most recent prover job not from the current spec
            return null;
        }
        Collection statuses = lastJob.getObsMap().values();
        return (ObligationStatus[]) statuses.toArray(new ObligationStatus[statuses.size()]);
    }

    /**
     * Removes all SANY step markers on the module.
     * See {@link ProverHelper#SANY_MARKER} for a description of
     * these markers.
     * 
     * @param module
     * @throws CoreException 
     */
    public static void removeSANYStepMarkers(IResource module) throws CoreException
    {
        module.deleteMarkers(SANY_MARKER, false, IResource.DEPTH_ZERO);
    }

    /**
     * This method prepares the module for the launch of the prover.
     * In the following, levelNode is the levelNode in proverJob.
     * If levelNode or module, it prints debugging info and returns.
     * If not, it takes the following steps:
     * 
     * 1.) Call {@link #removeSANYStepMarkers(IResource)} on the module.
     * 2.) If level node is not an instance of {@link ModuleNode},
     *     call {@link #removeStatusFromTree(IFile, LevelNode)}. Else
     *     call {@link #removeStatusFromModule(IResource)}.
     * 3.) If levelNode is an instance of {@link ModuleNode}, then the following
     *     is done for the entire module. If it is not an instance, the following is
     *     only done for the tree rooted at levelNode:
     * 
     * Create SANY markers on all nodes for which there can be
     * a prover status. A SANY marker stores the location of the node as returned
     * by SANY when the marker is created. Since markers are "sticky", SANY markers
     * can be used to map from locations returned by the prover to the current
     * location of a node. A location returned by the prover should equal
     * the SANY location of a SANY marker.
     * 
     * This currently puts SANY markers on all step or top level
     * USE nodes. If levelNode is null and there is no valid parse result for the module,
     * this method does nothing.
     * 
     * See {@link ProverHelper#SANY_MARKER} for a description of
     * these markers.
     * 
     * This method also creates the tree of {@link StepTuple}s for
     * this module or LevelNode.
     * 
     * The proverJob is the instance of {@link ProverJob} used to launch the prover
     * and passed to listeners of TLAPM output for that launch. It provides access
     * to information about launch parameters and other useful data structures.
     * 
     * @param module
     * @throws CoreException 
     */
    public static void prepareModuleForProverLaunch(final IFile module, final ProverJob proverJob) throws CoreException
    {
        /*
         * This does a lot of stuff creating, deleting, and modifying
         * markers. Each of these operations results in a separate resource change
         * notification sent to all listeners unless the operations are wrapped
         * in an IWorkspaceRunnable(). If they are wrapped in an IWorkspaceRunnable
         * and the flag IWorkspace.AVOID_UPDATE is specified when running the runnable,
         * the resource change notifications will be delayed until after the runnables run method
         * has completed. The notification will then be batched as a single notification. This
         * seems to be more efficient.
         */
        IWorkspaceRunnable runnable = new IWorkspaceRunnable() {

            public void run(IProgressMonitor monitor) throws CoreException
            {
                if (module == null)
                {
                    ProverUIActivator.logDebug("Module is null in method prepareModuleForProverLaunch. This is a bug.");
                    return;
                }

                if (proverJob.getLevelNode() == null)
                {
                    ProverUIActivator.logDebug("Module is null in method prepareModuleForProverLaunch. This is a bug.");
                    return;
                }

                /*
                 * Remove existing sany markers and step status markers.
                 */
                removeSANYStepMarkers(module);
                if (proverJob.getLevelNode() instanceof ModuleNode)
                {
                    removeStatusFromModule(module);
                } else
                {
                    removeStatusFromTree(module, proverJob.getLevelNode());
                }
                /*
                 * Clear the maps that hold information about obligations
                 * and steps.
                 */
                proverJob.getObsMap().clear();
                proverJob.getLeafStepMap().clear();
                proverJob.getStepMessageMap().clear();

                /*
                 * Create new SANY markers and prepare the data structures for computing step statuses.
                 */
                if (proverJob.getLevelNode() instanceof ModuleNode)
                {
                    ParseResult parseResult = ResourceHelper.getValidParseResult(module);
                    if (parseResult == null)
                    {
                        return;
                    }

                    String moduleName = ResourceHelper.getModuleName(module);

                    ModuleNode moduleNode = parseResult.getSpecObj().getExternalModuleTable().getModuleNode(
                            UniqueString.uniqueStringOf(moduleName));
                    if (module == null)
                    {
                        return;
                    }
                    LevelNode[] topLevelNodes = moduleNode.getTopLevel();

                    for (int i = 0; i < topLevelNodes.length; i++)
                    {

                        if (topLevelNodes[i].getLocation().source().equals(moduleName))
                        {
                            // found a theorem in the module
                            prepareTreeForProverLaunch(topLevelNodes[i], module, proverJob);
                        }
                    }
                } else
                {
                    prepareTreeForProverLaunch(proverJob.getLevelNode(), module, proverJob);
                    return;
                }
            }
        };

        module.getWorkspace().run(runnable, null, IWorkspace.AVOID_UPDATE, null);
    }

    /**
     * Creates a SANY marker for levelNode if it is a {@link TheoremNode} or a {@link UseOrHideNode}.
     * If it has a proof, this method recursively calls it self on all children. The SANY location
     * attribute for these markers is a string representation of the location of the node
     * if it is a {@link UseOrHideNode} and the string representation of the location of the node
     * {@link TheoremNode#getTheorem()} if it is a {@link TheoremNode}.
     * 
     * The methods {@link #locToString(Location)} and {@link #stringToLoc(String)} convert from
     * {@link Location} to Strings and back.
     * 
     * See {@link ProverHelper#SANY_MARKER} for a description of
     * these markers.
     * 
     * Creates and returns the {@link StepTuple} for levelNode if levelNode is an instance of
     * {@link UseOrHideNode} or {@link TheoremNode}. Sets the marker for this tuple.
     * Returns null otherwise. If levelNode is a {@link TheoremNode} then it sets levelNode
     * as the parent of all non-null {@link StepTuple}s returned by calling this method on its children.
     * 
     * The proverJob is the instance of {@link ProverJob} used to launch the prover
     * and passed to listeners of TLAPM output for that launch. It provides access
     * to information about launch parameters and other useful data structures.
     * 
     * @param theoremNode
     * @throws CoreException 
     */
    public static StepTuple prepareTreeForProverLaunch(LevelNode levelNode, IResource module, ProverJob proverJob)
            throws CoreException
    {
        if (levelNode == null)
        {
            return null;
        }

        if (levelNode instanceof UseOrHideNode || levelNode instanceof TheoremNode)
        {
            IMarker marker = module.createMarker(SANY_MARKER);
            // the location to be used for setting the sany location attribute on the marker
            Location locForAttr;
            if (levelNode instanceof UseOrHideNode)
            {
                locForAttr = levelNode.getLocation();
            } else
            {
                TheoremNode theoremNode = (TheoremNode) levelNode;
                /*
                 * The location of a theorem node is the location beginning at the
                 * step number or keyword THEOREM and ending at the end of the statement
                 * of the step or theorem.
                 */
                Location beginLoc = theoremNode.getLocation();
                Location statementLoc = theoremNode.getTheorem().getLocation();
                locForAttr = new Location(UniqueString.uniqueStringOf(statementLoc.source()), beginLoc.beginLine(),
                        beginLoc.beginColumn(), statementLoc.endLine(), statementLoc.endColumn());
            }
            marker.setAttribute(SANY_LOC_ATR, locToString(locForAttr));
            IRegion locRegion = AdapterFactory.locationToRegion(locForAttr);
            marker.setAttribute(IMarker.CHAR_START, locRegion.getOffset());
            /*
             * For marking a region that starts at offset o and has length l, the
             * start character is o and the end character is o+l.
             */
            marker.setAttribute(IMarker.CHAR_END, locRegion.getOffset() + locRegion.getLength());

            /*
             * Create the tuple. Eventually return this tuple.
             * 
             * For step tuples with PROOF OMITTED, we add a dummy child obligation
             * indicating that the proof is explicitly omitted. For all other
             * steps that have something to prove, the tlapm will send either
             * a "to be proved" message for each obligation that it will try to
             * prove for that step.  If the step can take a user-provide proof, but
             * the user does not provide it, then tlapm will send a "missing" message
             * and will not try to prove any obligations for that step.
             * 
             * See the method processObligationMessage() for information
             * on how information about the status of obligations
             * is used to update the status of steps.
             */
            StepTuple stepTuple = new StepTuple(proverJob);
            stepTuple.setSanyMarker(marker);

            if (levelNode instanceof TheoremNode)
            {

                TheoremNode theoremNode = (TheoremNode) levelNode;
                ProofNode proof = theoremNode.getProof();
                if (proof != null)
                {
                    if (proof instanceof NonLeafProofNode)
                    {
                        NonLeafProofNode nonLeafProof = (NonLeafProofNode) proof;
                        LevelNode[] steps = nonLeafProof.getSteps();
                        // the step is not a leaf iff it has at least 1 step
                        marker.setAttribute(SANY_IS_LEAF_ATR, steps.length == 0);

                        /*
                         * Recursively put markers on each child node.
                         */
                        for (int i = 0; i < steps.length; i++)
                        {
                            StepTuple childTuple = prepareTreeForProverLaunch(steps[i], module, proverJob);
                            // child tuple will be null if the step
                            // is not a TheoremNode or UseOrHideNode
                            if (childTuple != null)
                            {
                                childTuple.setParent(stepTuple);
                                stepTuple.addChild(childTuple);
                            }
                        }
                    } else
                    {
                        marker.setAttribute(SANY_IS_LEAF_ATR, true);

                        // leaf proof
                        LeafProofNode leafProof = (LeafProofNode) proof;
                        if (leafProof.getOmitted())
                        {
                            // We create a dummy marker for this dummy obligation
                            // because ObligationStatus stores information
                            // about the obligation in a marker.
                            // The marker can have id -1 because the id
                            // is meaningless for a dummy marker. The location
                            // simply must be in the correct module so that the marker
                            // is put on the correct resource. The exact start
                            // and end positions don't matter.
                            stepTuple.addChild(new ObligationStatus(stepTuple, createObligationMarker(-1, theoremNode
                                    .getLocation()), ColorPredicate.NUMBER_OF_OMITTED_STATE, theoremNode.getLocation(),
                                    -1));
                        }

                    }
                } else
                {
                    marker.setAttribute(SANY_IS_LEAF_ATR, true);

                    // Add a missing dummy obligation unless this is a Have, Take, or Witness step
                    LevelNode assertion = theoremNode.getTheorem();
                    boolean shouldHaveProof = true;
                    if (assertion instanceof OpApplNode)
                    {
                        OpApplNode opApplAss = (OpApplNode) assertion;
                        String name = opApplAss.getOperator().getName().toString();
                        if (name.equals("$Have") || name.equals("$Take") || name.equals("$Witness"))
                            shouldHaveProof = false;
                    }

                    if (shouldHaveProof)
                    {
                        // We create a dummy marker for this dummy obligation
                        // because ObligationStatus stores information
                        // about the obligation in a marker.
                        // The marker can have id -1 because the id
                        // is meaningless for a dummy marker. The location
                        // simply must be in the correct module so that the marker
                        // is put on the correct resource. The exact start
                        // and end positions don't matter.
                        stepTuple
                                .addChild(new ObligationStatus(stepTuple, createObligationMarker(-1, theoremNode
                                        .getLocation()), ColorPredicate.NUMBER_OF_MISSING_STATE, theoremNode
                                        .getLocation(), -1));
                    }

                }

            } else
            {
                marker.setAttribute(SANY_IS_LEAF_ATR, true);
            }

            if (marker.getAttribute(SANY_IS_LEAF_ATR, false))
            {
                proverJob.getLeafStepMap().put(new Integer(locForAttr.beginLine()), stepTuple);
            }

            return stepTuple;
        }

        return null;

    }

    /**
     * Turns a {@link Location} into a String that can
     * be parsed back to a location using {@link ProverHelper#stringToLoc(String)}.
     * @param location
     * @return
     */
    public static String locToString(Location location)
    {
        /*
         * moduleName:bl:bc:el:ec
         */
        StringBuilder sb = new StringBuilder();
        sb.append(location.source()).append(LOC_DELIM).append(location.beginLine()).append(LOC_DELIM).append(
                location.beginColumn()).append(LOC_DELIM).append(location.endLine()).append(LOC_DELIM).append(
                location.endColumn());
        return sb.toString();
    }

    /**
     * Takes a string produced by {@link #locToString(Location)}
     * and produces a {@link Location}. Will throw a number format exception if
     * the string was not produced by {@link #locToString(Location)}.
     * 
     * @param locString
     * @return
     */
    public static Location stringToLoc(String locString)
    {
        /*
         * moduleName:bl:bc:el:ec
         */
        String[] segments = locString.split(LOC_DELIM);
        return new Location(UniqueString.uniqueStringOf(segments[0]), Integer.parseInt(segments[1]), Integer
                .parseInt(segments[2]), Integer.parseInt(segments[3]), Integer.parseInt(segments[4]));
    }

    /**
     * Returns the SANY step marker on the module whose SANY location
     * has the same begin and end line as the location passed to this method.
     * Returns null if such a marker is not found.
     * 
     * See {@link ProverHelper#SANY_MARKER} for a description of
     * these markers.
     * 
     * @param location
     * @param module
     * @return
     */
    public static IMarker findSANYMarker(IResource module, Location location)
    {
        try
        {
            IMarker[] sanyMarkers = module.findMarkers(SANY_MARKER, false, IResource.DEPTH_ZERO);
            /*
             * Iterate through all markers. For each marker, retrieve
             * the SANY location. Return the marker if its SANY location
             * equals location.
             */
            for (int i = 0; i < sanyMarkers.length; i++)
            {
                String sanyLocString = sanyMarkers[i].getAttribute(SANY_LOC_ATR, "");
                if (!sanyLocString.isEmpty())
                {
                    Location sanyLoc = stringToLoc(sanyLocString);
                    if (sanyLoc.beginLine() == location.beginLine()/* && sanyLoc.endLine() == location.endLine()*/)
                    {
                        return sanyMarkers[i];
                    }
                }
            }
        } catch (CoreException e)
        {
            ProverUIActivator.logError("Error finding existing SANY marker for location " + location, e);
        }
        return null;
    }

    /**
     * Converts the status string to the correct marker type.
     * The status string should be one of : 
     * 
     * {@link StepStatusMessage#CHECKED}
     * {@link StepStatusMessage#CHECKING_FAILED}
     * {@link StepStatusMessage.MISSING_PROOFS}
     * {@link StepStatusMessage.OMITTED}
     * {@link StepStatusMessage.PROVED}
     * {@link StepStatusMessage.PROVING_FAILED}
     * {@link StepStatusMessage.BEING_PROVED}
     * 
     * If status is not one of these, this
     * method will return null.
     * 
     * If status is null, this method returns null.
     * 
     * The marker type for proving failed steps is different depending
     * on whether it is a leaf step or not.
     * 
     * @param status
     * @param isLeafStep true iff the status is for a leaf step (a step with no
     * children or with a leaf proof).
     * @return
     */
    public static String statusStringToMarkerType(String status, boolean isLeafStep)
    {
        if (status == null)
        {
            return null;
        }

        if (status.equals(StepStatusMessage.CHECKED))
        {
            return STEP_CHECKED_MARKER;
        } else if (status.equals(StepStatusMessage.CHECKING_FAILED))
        {
            return STEP_CHECKING_FAILED_MARKER;
        } else if (status.equals(StepStatusMessage.MISSING_PROOFS))
        {
            return STEP_MISSING_MARKER;
        } else if (status.equals(StepStatusMessage.OMITTED))
        {
            return STEP_OMITTED_MARKER;
        } else if (status.equals(StepStatusMessage.PROVED))
        {
            return STEP_PROVED_MARKER;
        } else if (status.equals(StepStatusMessage.PROVING_FAILED))
        {
            if (isLeafStep)
            {
                return STEP_LEAF_FAILED;
            } else
            {
                return STEP_PROVING_FAILED_MARKER;
            }
        } else if (status.equals(StepStatusMessage.BEING_PROVED))
        {
            return STEP_BEING_PROVED_MARKER;
        }
        return null;
    }

    /**
     * Returns the marker type corresponding to the predicate given
     * by predNum. The marker type depends on whether the marker
     * is for a leaf step or not.
     * 
     * Color predicate numbers begin at 1 and end at
     * {@link ProverPreferencePage#NUM_STATUS_COLORS}.
     * 
     * @param predNum
     * @return
     */
    public static String colorPredNumToMarkerType(int predNum, boolean isLeaf)
    {
        return "org.lamport.tla.toolbox.tool.prover.ui.stepColor" + predNum + (isLeaf ? "B" : "A");
    }

    /**
     * Converts from an integer status of a step to
     * the marker type. The int should be one of
     * 
     * {@link #STEP_CHECKED_INT}
     * {@link #STEP_CHECKING_FAILED_INT}
     * {@link #STEP_PROOF_MISSING_INT}
     * {@link #STEP_PROOF_OMITTED_INT}
     * {@link #STEP_PROVED_INT}
     * {@link #STEP_PROVING_FAILED_INT}
     * {@link #STEP_BEING_PROVED_INT}
     * 
     * Else, this method returns null.
     * 
     * @param status
     * @return
     */
    public static String statusIntToStatusString(int status)
    {
        switch (status) {
        case STEP_CHECKED_INT:
            return StepStatusMessage.CHECKED;
        case STEP_CHECKING_FAILED_INT:
            return StepStatusMessage.CHECKING_FAILED;
        case STEP_PROOF_MISSING_INT:
            return StepStatusMessage.MISSING_PROOFS;
        case STEP_PROOF_OMITTED_INT:
            return StepStatusMessage.OMITTED;
        case STEP_PROVED_INT:
            return StepStatusMessage.PROVED;
        case STEP_PROVING_FAILED_INT:
            return StepStatusMessage.PROVING_FAILED;
        case STEP_BEING_PROVED_INT:
            return StepStatusMessage.BEING_PROVED;
        case STEP_TO_BE_PROVED_INT:
            return StepStatusMessage.TO_BE_PROVED;
        default:
            return null;
        }
    }

    /**
     * Process the obligation message. If the status of the message is not
     * {@link #TO_BE_PROVED} then it creates a marker for that obligation
     * by calling {@link #createObligationMarker(ObligationStatusMessage)}. Else, it prepares
     * the necessary data structure for computing proof step statuses.
     * 
     * The proverJob is the instance of {@link ProverJob} used to launch the prover
     * and passed to listeners of TLAPM output for that launch. It provides access
     * to information about launch parameters and other useful data structures.
     * 
     * @param message
     * @param nodeToProve the step or module on which the prover was launched
     */
    public static void processObligationMessage(ObligationStatusMessage message, final ProverJob proverJob)
    {
        if (message.getStatus().equals(TO_BE_PROVED))
        {
            if (proverJob.noToBeProved)
            {
                System.out.println("First to be proved " + proverJob.getCurRelTime());
                proverJob.noToBeProved = false;
            }

            /*
             * Simply add all to be proved messages to a list.
             * They will be processed later. This is done once
             * the first non "to be proved" message is sent. See below.
             */
            proverJob.getObMessageList().add(message);

            /*
             * Create a new ObligationStatus with null as the initial status and
             * to be proved as the initial state.
             * 
             * The parent is initially null because we set it later. We set the parent
             * of all non-dummy obligations when the first obligation message arrives that
             * does not have status "to be proved". This condition is captured below in the
             * if block with condition obStatus.getParent() == null. This condition should
             * only be true once, because the code in that if block sets the parent
             * for every obligation.
             */
            // IMarker obMarker = createObligationMarker(message.getID(), ColorPredicate.TO_BE_PROVED_STATE, message
            // .getLocation());
            // ObligationStatus obStatus = new ObligationStatus(null, obMarker);
            // proverJob.getObsMap().put(new Integer(message.getID()), obStatus);
        } else
        {
            /*
             * When the first message arrives that is not "to be proved"
             * we create all obligation markers at once. Batching marker creation
             * and wrapping the creation in an IWorkspaceRunnable sends one batch
             * resource change notification instead of one notification for each
             * marker modification. This is significantly faster than not wrapping the
             * creation in an IWorkspaceRunnable.
             */
            if (proverJob.isToBeProvedOnly())
            {
                System.out.println("Before obligation marker creation " + proverJob.getCurRelTime());
                IWorkspaceRunnable runnable = new IWorkspaceRunnable() {

                    public void run(IProgressMonitor monitor) throws CoreException
                    {
                        for (Iterator it = proverJob.getObMessageList().iterator(); it.hasNext();)
                        {
                            ObligationStatusMessage message = (ObligationStatusMessage) it.next();
                            IMarker obMarker = createObligationMarker(message.getID(), message.getLocation());
                            ObligationStatus obStatus = new ObligationStatus(null, obMarker,
                                    ColorPredicate.TO_BE_PROVED_STATE, message.getLocation(), message.getID());
                            proverJob.getObsMap().put(new Integer(message.getID()), obStatus);
                        }
                    }
                };

                try
                {
                    proverJob.getModule().getWorkspace().run(runnable, null, IWorkspace.AVOID_UPDATE, null);
                } catch (CoreException e)
                {
                    ProverUIActivator.logError("Error creating marker obligations", e);
                }
                proverJob.setToBeProvedOnly(false);
                System.out.println("After obligation marker creation " + proverJob.getCurRelTime());
            }
            /*
             * Update the state of the obligation. The obligation will
             * inform its parents step that its status should be updated.
             */
            final ObligationStatus obStatus = (ObligationStatus) proverJob.getObsMap()
                    .get(new Integer(message.getID()));

            /*
             * If the obligation does not yet have a parent, then
             * set parents for all obligations. This should only occur
             * once.
             */
            if (obStatus.getParent() == null)
            {
                System.out.println("Before ob parenting creation " + proverJob.getCurRelTime());
                /*
                 * The following iterates through all non-dummy
                 * obligations. For each obligation, we search through
                 * the map of leaf steps until we find a parent. We search
                 * by line numbers (because that is the key of the leaf step
                 * map). We search upward in the file (decreasing the line number)
                 * until we find a step that begins on that line number. This
                 * assumes only one step per line. This is hopefully efficient
                 * because obligations should be only a few lines below their parent
                 * step.
                 */
                for (Iterator it = proverJob.getObs().iterator(); it.hasNext();)
                {
                    ObligationStatus obligation = (ObligationStatus) it.next();
                    int searchLine = obligation.getTLAPMLocation().beginLine();
                    while (true)
                    {
                        StepTuple stepTuple = (StepTuple) proverJob.getLeafStepMap().get(new Integer(searchLine));
                        if (stepTuple != null)
                        {
                            obligation.setParent(stepTuple);
                            stepTuple.addChild(obligation);
                            break;
                        }
                        searchLine--;
                    }
                }

                System.out.println("After ob parenting creation " + proverJob.getCurRelTime());

            }

            obStatus.updateObligation(message);

            // update the obligations view with the new information
            UIHelper.runUIAsync(new Runnable() {

                public void run()
                {
                    ObligationsView.updateObligationView(obStatus);
                }
            });
        }
    }

    /**
     * Installs a new marker for the obligation with the given input information.
     * 
     * The message location should be for a module in the currently opened spec. If no
     * such module exists, this method returns null.
     * 
     * The initialState is the state of the obligation at the time of creation
     * of this marker. Obligation states are explained in {@link ColorPredicate}.
     * 
     * Returns the marker created.
     */
    public static IMarker createObligationMarker(int id, Location location)
    {
        IResource module = ResourceHelper.getResourceByModuleName(location.source());
        if (module != null && module instanceof IFile && module.exists())
        {
            /*
             * We may need to convert the 4-int location of the message
             * to a 2-int region if an existing marker is not found. We use a FileDocumentProvider.
             * We create it now so that if it is used, it can be disconnected in
             * the finally block of the following try block to avoid a memory leak.
             */
            FileEditorInput fileEditorInput = new FileEditorInput((IFile) module);
            FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();

            try
            {

                // the marker created
                Map markerAttributes = new HashMap();
                markerAttributes.put(OBLIGATION_ID, new Integer(id));
                // markerAttributes.put(OBLIGATION_STATE, new Integer(initialState));
                // markerAttributes.put(OBLIGATION_LOCATION, locToString(location));

                fileDocumentProvider.connect(fileEditorInput);
                IDocument document = fileDocumentProvider.getDocument(fileEditorInput);
                IRegion obRegion = AdapterFactory.locationToRegion(document, location);
                /*
                 * For marking a region that starts at offset o and has length l, the
                 * start character is o and the end character is o+l.
                 */
                markerAttributes.put(IMarker.CHAR_START, new Integer(obRegion.getOffset()));
                markerAttributes.put(IMarker.CHAR_END, new Integer(obRegion.getOffset() + obRegion.getLength()));

                IMarker marker = module.createMarker(OBLIGATION_MARKER);
                marker.setAttributes(markerAttributes);

                // DEBUG
                // System.out.println("Marker created for obligation from message \n" + message);
                return marker;
            } catch (CoreException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (BadLocationException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } finally
            {
                fileDocumentProvider.disconnect(fileEditorInput);
            }
        }
        return null;

    }

    /**
     * Should be called to update the status of a proof
     * step using a message from the tlapm. This method always
     * stores the message in a map for later use comparing messages
     * from the tlapm to step status computed by the toolbox.
     * 
     * If addMarker is true, this searches for an existing SANY marker
     * with the same location as the status. If found, replaces
     * this marker with the appropriate step status marker. If
     * a SANY marker is not found, this is a bug and will be
     * printed out on the console.
     * 
     * The proverJob is the instance of {@link ProverJob} used to launch the prover
     * and passed to listeners of TLAPM output for that launch. It provides access
     * to information about launch parameters and other useful data structures.
     * 
     * @param status
     * @param proverJob the description of the launch of the prover
     * indicating its status
     */
    public static void newStepStatusMessage(StepStatusMessage status, ProverJob proverJob)
    {
        proverJob.getStepMessageMap().put(new Integer(status.getLocation().beginLine()), status);

        /*
         * The following was commented out because the proof step status markers are now always
         * put on by the toolbox.
         */
        // if (proverJob.isStatusCheck())
        // {
        //
        // if (status == null)
        // {
        // return;
        // }
        // /*
        // * Create a marker located at the proof step. The current location
        // * of the proof step is determined by finding an existing SANY marker
        // * whose attribute matches the location according to the method
        // * findSANYMarker().
        // */
        // Location location = status.getLocation();
        // IResource module = ResourceHelper.getResourceByModuleName(location.source());
        // if (module != null && module instanceof IFile && module.exists())
        // {
        // /*
        // * Try to find an existing SANY marker.
        // *
        // * If a sany marker is found, put a marker at the current location
        // * of the sany marker (not at the SANY location attribute of the sany marker).
        // */
        // IMarker sanyMarker = findSANYMarker(module, location);
        //
        // if (sanyMarker == null)
        // {
        // ProverUIActivator.logDebug("Existing SANY marker not found for location " + location
        // + ". This is a bug.");
        // }
        //
        // newStepStatusMarker(sanyMarker, status.getStatus());
        //
        // // the following code was commented out because it is basically
        // // done in newStepStatusMarker().
        // // try
        // // {
        // // /*
        // // * If the status string does not correspond
        // // * to a marker type, then do not create a marker.
        // // */
        // // String markerType = statusStringToMarkerType(status.getStatus());
        // //
        // // if (markerType == null)
        // // {
        // // ProverUIActivator
        // // .logDebug("Status of proof step does not correspond to an existing marker type. The status is "
        // // + status.getStatus());
        // // return;
        // // }
        // //
        // // IMarker newMarker = module.createMarker(markerType);
        // // Map markerAttributes = new HashMap(2);
        // // // value based on whether a sany marker is found or not
        // // int newCharStart;
        // // int newCharEnd;
        // // if (sanyMarker != null)
        // // {
        // // newCharStart = sanyMarker.getAttribute(IMarker.CHAR_START, 0);
        // // newCharEnd = sanyMarker.getAttribute(IMarker.CHAR_END, 0);
        // // } else
        // // {
        // // ProverUIActivator.logDebug("Existing SANY marker not found for location " + location
        // // + ". This is a bug.");
        // // // the region from the tlapm message
        // // IRegion messageRegion = AdapterFactory.locationToRegion(location);
        // // /*
        // // * For marking a region that starts at offset o and has length l, the
        // // * start character is o and the end character is o+l.
        // // */
        // // newCharStart = messageRegion.getOffset();
        // // newCharEnd = messageRegion.getOffset() + messageRegion.getLength();
        // // return;
        // // }
        // //
        // // /*
        // // * Remove any existing step status markers that overlap
        // // * with the new step status marker.
        // // */
        // // IMarker[] existingMarkers = module.findMarkers(ProverHelper.STEP_STATUS_MARKER, true,
        // // IResource.DEPTH_ZERO);
        // // for (int i = 0; i < existingMarkers.length; i++)
        // // {
        // // IMarker existingMarker = existingMarkers[i];
        // // int existingCharStart = existingMarker.getAttribute(IMarker.CHAR_START, -1);
        // // int existingCharEnd = existingMarker.getAttribute(IMarker.CHAR_END, -1);
        // //
        // // // conditions for overlapping
        // // if (existingCharStart < newCharEnd && existingCharEnd > newCharStart)
        // // {
        // // existingMarker.delete();
        // // }
        // // }
        // //
        // // markerAttributes.put(IMarker.CHAR_START, new Integer(newCharStart));
        // // markerAttributes.put(IMarker.CHAR_END, new Integer(newCharEnd));
        // // newMarker.setAttributes(markerAttributes);
        // //
        // // } catch (CoreException e)
        // // {
        // // ProverUIActivator.logError("Error creating new status marker.", e);
        // // }
        // } else
        // {
        // ProverUIActivator.logDebug("A module could not be located for a step status.\n" + "Status : "
        // + status.getStatus() + "\nLocation : " + location);
        // }
        // }
    }

    /**
     * Compares the step status computations of the TLAPM and the toolbox.
     * Any discrepancies are reported. Currently the reporting is to the
     * console.
     * 
     * This method does the comparison for the step statuses computed
     * for the launch of the prover described by proverJob.
     * This is the instance of {@link ProverJob} used to launch the prover
     * and passed to listeners of TLAPM output for that launch.
     */
    public static void compareStepStatusComputations(ProverJob proverJob)
    {
        // System.out.println("------------------Comparing TLAPM and Toolbox Step Status------------");
        // Collection stepTuples = proverJob.getStepMap().values();
        // for (Iterator it = stepTuples.iterator(); it.hasNext();)
        // {
        // StepTuple stepTuple = (StepTuple) it.next();
        // Location stepLoc = stringToLoc(stepTuple.getSanyMarker().getAttribute(SANY_LOC_ATR, ""));
        // StepStatusMessage stepMessage = (StepStatusMessage) proverJob.getStepMessageMap().remove(
        // new Integer(stepLoc.beginLine()));
        // if (stepMessage == null)
        // {
        // System.out.println("NO STATUS BUG :\n No TLAPM step status message found for the step at " + stepLoc
        // + " . The Toolbox thinks the status is "
        // + statusIntToStatusString(stepTuple.getColorPredicateValues()));
        // } else if (!stepMessage.getStatus().equals(statusIntToStatusString(stepTuple.getColorPredicateValues())))
        // {
        // System.out.println("DIFFERENT STATUS BUG : \n Loc : " + stepLoc + "\n TLAPM : "
        // + stepMessage.getStatus() + "\n Toolbox : "
        // + statusIntToStatusString(stepTuple.getColorPredicateValues()));
        // }
        // }
        //
        // Collection remainingMessages = proverJob.getStepMessageMap().values();
        // for (Iterator it = remainingMessages.iterator(); it.hasNext();)
        // {
        // StepStatusMessage message = (StepStatusMessage) it.next();
        // System.out.println("NO STATUS BUG :\n No Toolbox step status message found for the step at "
        // + message.getLocation() + " . The TLAPM reports the status " + message.getStatus());
        // }
        //
        // System.out.println("------------------Done Comparing TLAPM and Toolbox Step Status------------");
    }

    /**
     * Creates a new marker at the current location of sanyMarker indicating the
     * status given by status. If status is not a known type (the method
     * {@link #colorPredNumToMarkerType(int, boolean) returns null) then this deletes
     * any markers overlapping with sanyMarker but does not create a new marker. If sanyMarker is null, this also
     * prints some debugging message and returns. This method removes any step status markers
     * overlapping with the new marker that is created.
     * 
     * Color predicate numbers begin at 1 and end at {@link ProverPreferencePage#NUM_STATUS_COLORS}.
     * 
     * @param sanyMarker
     * @param predNum
     */
    public static void newStepStatusMarker(final IMarker sanyMarker, int predNum)
    {
        if (sanyMarker == null)
        {
            ProverUIActivator.logDebug("Null sanyMarker passed to newStepStatusMarker. This is a bug.");
            return;
        }

        try
        {
            final IResource module = sanyMarker.getResource();
            /*
             * If the status string does not correspond
             * to a marker type, then do not create a marker.
             */
            final String markerType = colorPredNumToMarkerType(predNum, sanyMarker
                    .getAttribute(SANY_IS_LEAF_ATR, false));

            // This is commented out because we now will not create a marker if
            // marker type is null. A null marker type indicates that all overlapping markers
            // should be deleted and a new one not created.
            // if (markerType == null)
            // {
            // ProverUIActivator
            // .logDebug("Status of proof step does not correspond to an existing marker type. The status is "
            // + status);
            // return;
            // }

            /*
             * We wrap the marker creation and deletion operation
             * in a runnable that tells the workspace to avoid
             * sending resource change notifications while
             * the run method is executing.
             */
            IWorkspaceRunnable runnable = new IWorkspaceRunnable() {

                public void run(IProgressMonitor monitor) throws CoreException
                {
                    /*
                     * Its important to note that the location of the marker
                     * obtained by sanyMarker.getAttribute(IMarker.CHAR_START, 0)
                     * and sanyMarker.getAttribute(IMarker.CHAR_END, 0) can be different
                     * than the location of the marker in the editor if the editor is
                     * currently dirty. It seems that the eclipse text editors update
                     * the CHAR_START and CHAR_END attributes of markers only on save.
                     * The current position of the marker in the editor can be obtained
                     * through the editor's annotation model. The code for doing this
                     * is in the method EditorUtil.getMarkerPosition(sanyMarker).
                     */

                    // The current position of the sany marker in the editor
                    // if there is at least one editor open on the module.
                    Position curPosition = EditorUtil.getMarkerPosition(sanyMarker);
                    // char start and end of the marker to be created
                    int newCharStart;
                    int newCharEnd;

                    if (curPosition != null)
                    {
                        newCharStart = curPosition.getOffset();
                        newCharEnd = curPosition.getOffset() + curPosition.getLength();
                    } else
                    {
                        /*
                         * We cannot get the position, which means there may not be
                         * an editor open on the module, so we just use the marker's location
                         * attributes.
                         */
                        newCharStart = sanyMarker.getAttribute(IMarker.CHAR_START, 0);
                        newCharEnd = sanyMarker.getAttribute(IMarker.CHAR_END, 0);
                    }

                    /*
                     * Remove any existing step status markers that overlap
                     * with the new step status marker.
                     */
                    IMarker[] existingMarkers = module.findMarkers(ProverHelper.STEP_STATUS_MARKER, true,
                            IResource.DEPTH_ZERO);
                    for (int i = 0; i < existingMarkers.length; i++)
                    {
                        IMarker existingMarker = existingMarkers[i];
                        int existingCharStart = existingMarker.getAttribute(IMarker.CHAR_START, -1);
                        int existingCharEnd = existingMarker.getAttribute(IMarker.CHAR_END, -1);

                        // conditions for overlapping
                        if (existingCharStart < newCharEnd && existingCharEnd > newCharStart)
                        {
                            existingMarker.delete();
                        }
                    }

                    if (markerType != null)
                    {
                        // the attributes for the new marker to be created
                        Map markerAttributes = new HashMap(2);
                        markerAttributes.put(IMarker.CHAR_START, new Integer(newCharStart));
                        markerAttributes.put(IMarker.CHAR_END, new Integer(newCharEnd));
                        markerAttributes.put(IMarker.LINE_NUMBER, new Integer(stringToLoc(
                                sanyMarker.getAttribute(SANY_LOC_ATR, "")).beginLine()));

                        // create the new marker and set its attributes
                        IMarker newMarker = module.createMarker(markerType);
                        newMarker.setAttributes(markerAttributes);
                    }
                }
            };

            module.getWorkspace().run(runnable, null, IWorkspace.AVOID_UPDATE, null);

        } catch (CoreException e)
        {
            ProverUIActivator.logError("Error creating new status marker.", e);
        }
    }

    /**
     * Removes all status markers from the module.
     */
    public static void removeStatusFromModule(IResource module)
    {
        try
        {
            module.deleteMarkers(STEP_STATUS_MARKER, true, IResource.DEPTH_ZERO);
        } catch (CoreException e)
        {
            ProverUIActivator.logError("Error removing status markers from module " + module, e);
        }
    }

    /**
     * Removes or modifies status markers so that no markers appear on any
     * of the lines from the begin line to the end line of the root.
     * Any markers that are only on those lines are deleted. Any markers that overlap
     * with those lines are shortened so that they do not overlap.
     * 
     * If root is a TheoremNode with a proof, then the begin line is
     * root.getLocation().beginLine() and the end line is
     * root.getProof().getLocation().endLine().
     * 
     * For all other cases, the begin line is root.getLocation().beginLine()
     * and the end line is root.getLocation().endLine().
     *  
     * @param module
     * @param root
     */
    public static void removeStatusFromTree(IFile module, LevelNode root)
    {
        try
        {
            /*
             * We need a  document to convert
             * from the 4-int location provided by SANY
             * to the 2-int location of markers.
             */
            IDocument document = ResourceHelper.getDocFromFile(module);
            /*
             * SANY lines are 1-based and document lines
             * are 0-based. We use document lines from now
             * on.
             */
            int beginLine = root.getLocation().beginLine() - 1;
            int endLine = root.getLocation().endLine() - 1;

            if (root instanceof TheoremNode && ((TheoremNode) root).getProof() != null)
            {
                endLine = ((TheoremNode) root).getProof().getLocation().endLine() - 1;
            }
            // get the start and end characters of the tree
            int treeBeginChar = document.getLineOffset(beginLine);
            /*
             * In the following, we subtract 1 to get the end char.
             * 
             * For a marker representing a region that starts at offset o and has length l, the
             * start character is o and the end character is o+l.
             */
            int treeEndChar = document.getLineOffset(endLine) + document.getLineLength(endLine);

            // get all existing step status markers on the module
            IMarker[] markers = module.findMarkers(STEP_STATUS_MARKER, true, IResource.DEPTH_ZERO);
            for (int i = 0; i < markers.length; i++)
            {
                IMarker oldMarker = markers[i];
                // get the start and end characters of the marker
                int markerStartChar = oldMarker.getAttribute(IMarker.CHAR_START, -1);
                int markerEndChar = oldMarker.getAttribute(IMarker.CHAR_END, -1);

                /*
                 * It appears that simply altering the char start and char end
                 * attributes of a marker will not cause that change to be reflected in the
                 * open editor. To solve this, markers that should be altered will instead
                 * be deleted and one or two markers will be created at the correct locations.
                 * 
                 * If the marker is completely contained by the tree, delete it.
                 * 
                 * If the marker starts before the tree and ends inside the tree, delete
                 * the marker and create one new marker that begins at the same point
                 * as the deleted marker but ends one character before the start of the tree.
                 * 
                 * If the marker completely contains the tree, delete that marker. Create two
                 * new markers. One marker will start at the old marker's start point and end
                 * one character before the tree. The second marker will begin one character after
                 * the end of the tree and end at the old marker's end point.
                 * 
                 * If the marker starts inside the tree and ends after the tree, delete that marker.
                 * Create a new marker that begins one character after the end of the tree and
                 * ends at the old marker's end point.
                 */
                if (markerStartChar >= treeBeginChar && markerEndChar <= treeEndChar)
                {
                    oldMarker.delete();
                } else if (markerStartChar < treeBeginChar && markerEndChar >= treeBeginChar
                        && markerEndChar <= treeEndChar)
                {
                    IMarker newMarker = module.createMarker(oldMarker.getType());
                    newMarker.setAttribute(IMarker.CHAR_START, markerStartChar);
                    newMarker.setAttribute(IMarker.CHAR_END, treeBeginChar - 1);
                    oldMarker.delete();
                } else if (markerStartChar < treeBeginChar && markerEndChar > treeEndChar)
                {
                    // marker before the tree
                    IMarker beforeMarker = module.createMarker(oldMarker.getType());
                    beforeMarker.setAttribute(IMarker.CHAR_START, markerStartChar);
                    beforeMarker.setAttribute(IMarker.CHAR_END, treeBeginChar - 1);

                    // marker after the tree
                    IMarker afterMarker = module.createMarker(oldMarker.getType());
                    afterMarker.setAttribute(IMarker.CHAR_START, treeEndChar + 1);
                    afterMarker.setAttribute(IMarker.CHAR_END, markerEndChar);

                    oldMarker.delete();
                } else if (markerStartChar >= treeBeginChar && markerStartChar <= treeEndChar
                        && markerEndChar > treeEndChar)
                {
                    IMarker newMarker = module.createMarker(oldMarker.getType());
                    newMarker.setAttribute(IMarker.CHAR_START, treeEndChar + 1);
                    newMarker.setAttribute(IMarker.CHAR_END, markerEndChar);
                    oldMarker.delete();
                }
            }
        } catch (CoreException e)
        {
            ProverUIActivator.logError("Error removing status markers from tree rooted at " + root, e);
        } catch (BadLocationException e)
        {
            ProverUIActivator.logError("Error removing status markers from tree rooted at " + root, e);
        }
    }

    /**
     * Requests cancellation of all running prover jobs. If wait
     * is true, sleeps the current thread until all prover jobs are done
     * that they are done.
     */
    public static void cancelProverJobs(boolean wait)
    {

        ProverJobMatcher jobMatcher = new ProverJob.ProverJobMatcher();
        Job.getJobManager().cancel(jobMatcher);
        if (wait)
        {
            while (Job.getJobManager().find(jobMatcher).length > 0)
            {
                try
                {
                    Thread.sleep(1000);
                } catch (InterruptedException e)
                {
                    ProverUIActivator.logError("Error sleeping thread.", e);
                }
            }
        }

    }

    /**
     * Runs the prover on the active selection in the {@link TLAEditor} with
     * focus. The active selection is the position of the caret. This method
     * runs the prover on the step at the caret, where step is either a proof
     * step or a top level USE node. A step is at the caret if the method
     * {@link ResourceHelper#getPfStepOrUseHideFromMod(ParseResult, String, ITextSelection, IDocument)}
     * returns that node for the text selection representing the caret position.
     * 
     * If there is not a step at the caret, this method will launch the prover
     * on the entire module.
     * 
     * If there are dirty editors open, this method will prompt the user
     * to save them before continuing. If there is not a valid parse result
     * available, this method will parse the module in the editor with focus.
     * If there are parse errors, the prover will not be launched, but the parse
     * error window will show the errors.
     * 
     * If statusCheck is true, this tells prover job to launch the prover
     * for status checking, not proving. If isaprove is true, the PM will
     * be launched with the --isaprove option.
     * 
     * @param checkStatus true iff the prover should only be run for status checking
     * @param isaprove true iff the PM should be called with the isaprove option
     * 
     * @return
     */
    public static void runProverForActiveSelection(boolean checkStatus, boolean isaprove)
    {
        boolean proceed = UIHelper.promptUserForDirtyModules();
        if (!proceed)
        {
            // the user cancelled
            return;
        }

        TLAEditor editor = EditorUtil.getTLAEditorWithFocus();
        Assert.isNotNull(editor, "User attempted to run prover without a tla editor in focus. This is a bug.");

        String[] options = null;
        if (isaprove)
        {
            options = new String[] { ITLAPMOptions.ISAPROVE };
        }

        ProverJob proverJob = new ProverJob(((FileEditorInput) editor.getEditorInput()).getFile(),
                ((ITextSelection) editor.getSelectionProvider().getSelection()).getOffset(), checkStatus, options, true);

        proverJob.setUser(true);
        proverJob.schedule();

    }

    /**
     * Runs the prover on the entire module in the active editor. If checkStatus is true,
     * the prover is launched only for status checking. If it is false,
     * the prover is launched for proving. If isaprove is true, the PM will
     * be launched with the --isaprove option.
     * 
     * If there are dirty editors, this method first prompts the user to save them.
     * 
     * @param checkStatus true iff the prover should only be run for status checking
     * @param isaprove true iff the PM should be called with the isaprove option
     */
    public static void runProverForEntireModule(boolean checkStatus, boolean isaprove)
    {
        boolean proceed = UIHelper.promptUserForDirtyModules();
        if (!proceed)
        {
            // the user cancelled
            return;
        }

        String[] options = null;
        if (isaprove)
        {
            options = new String[] { ITLAPMOptions.ISAPROVE };
        }

        TLAEditor editor = EditorUtil.getTLAEditorWithFocus();
        Assert.isNotNull(editor, "User attempted to run prover without a tla editor in focus. This is a bug.");

        ProverJob proverJob = new ProverJob(((FileEditorInput) editor.getEditorInput()).getFile(), -1, checkStatus,
                options, true);
        proverJob.setUser(true);
        proverJob.schedule();
    }

    /**
     * Takes the String representation of the status of a step
     * or obligation and translates to the integer representation
     * of the status of a proof step.
     * 
     * This can be used to map from the current state of an obligation
     * and the new status of the obligation for a prover into the new state
     * of the obligation. See {@link ColorPredicate} for explanation of
     * obligation states.
     * 
     * Returns currentStatus if status is not a known status. Also throws
     * an {@link AssertionFailedException} in that case.
     * 
     * @param status the new status string from tlapm
     * @param currentState the current state of the obligation
     * @param backEndName the name of the backend, e.g. isabelle, tlapm, zenon
     * @return
     */
    public static int getIntFromStringStatus(String status, int currentState, String backEndName)
    {
        int backendNum = getNumOfBackend(backEndName);

        if (status.equals(PROVED) || status.equals(TRIVIAL))
        {
            return ColorPredicate.newStateNumber(currentState, backendNum, ColorPredicate.numberOfProverStatus(
                    backendNum, ColorPredicate.PROVED_STATUS));
        } else if (status.equals(BEING_PROVED))
        {
            return ColorPredicate.newStateNumber(currentState, backendNum, ColorPredicate.numberOfProverStatus(
                    backendNum, ColorPredicate.PROVING_STATUS));
        } else if (status.equals(FAILED))
        {
            return ColorPredicate.newStateNumber(currentState, backendNum, ColorPredicate.numberOfProverStatus(
                    backendNum, ColorPredicate.FAILED_STATUS));
        } else if (status.equals(INTERUPTED))
        {
            return ColorPredicate.newStateNumber(currentState, backendNum, ColorPredicate.numberOfProverStatus(
                    backendNum, ColorPredicate.STOPPED_STATUS));
        }

        Assert.isTrue(false, "Unknown status : " + status);
        return currentState;

    }

    /**
     * Returns the number in {@link ColorPredicate} corresponding
     * to the backend reported by tlapm.
     * 
     * @param backend
     * @return
     */
    public static int getNumOfBackend(String backend)
    {
        if (backend.equals("isabelle"))
        {
            return ColorPredicate.ISABELLE_NUM;
        } else if (backend.equals("tlapm"))
        {
            return ColorPredicate.TLAPM_NUM;
        } else
        {
            return ColorPredicate.OTHER_BACKEND_NUM;
        }
    }

    /**
     * Processes a warning message from the tlapm. This simply displays
     * a warning to the user.
     * 
     * @param warningMessage
     */
    public static void processWarningMessage(final WarningMessage warningMessage)
    {
        UIHelper.runUIAsync(new Runnable() {

            public void run()
            {
                InformationDialog.openWarning(warningMessage.getMessage(), "TLAPM Warning");
            }
        });

    }

    /**
     * Processes an error message from the tlapm.
     * 
     * @param message
     */
    public static void processErrorMessage(final ErrorMessage message)
    {

        UIHelper.runUIAsync(new Runnable() {

            public void run()
            {
                TLAPMErrorDialog.open(message.getMessage(), "TLAPM Error", message.getURL());
            }
        });

    }

    /**
     * Sends a signal to the prover indicating that the obligation,
     * whose status is represented by marker, should be stopped.
     * 
     * The marker should by of the type {@link #OBLIGATION_MARKER}.
     * 
     * This method assumes that there is at most one prover job currently
     * running and that this marker is for an obligation from that prover
     * job.
     * 
     * @param marker
     */
    public static void stopObligation(IMarker marker)
    {

        System.out.println("Stop obligation " + marker.getAttribute(OBLIGATION_ID, -1));

        // a count of running prover jobs for debugging
        // check to see that there is at most 1
        int numProverJobs = 0;
        Job[] jobs = Job.getJobManager().find(new ProverJob.ProverJobMatcher());
        for (int i = 0; i < jobs.length; i++)
        {
            if (jobs[i] instanceof ProverJob && jobs[i].getState() == Job.RUNNING)
            {
                numProverJobs++;
                ProverJob proverJob = (ProverJob) jobs[i];
                proverJob.stopObligation(marker.getAttribute(OBLIGATION_ID, -1));
            }
        }

        if (numProverJobs > 1)
        {
            ProverUIActivator.logDebug("We found " + numProverJobs + " running when obligation "
                    + marker.getAttribute(OBLIGATION_ID, -1) + " was stopped. This is a bug.");
        }

    }
    
    /**
     * If the user has specified a number of threads preference of i,
     * then adds the appropriate entries to the list command of arguments.
     * @return
     */
    public static void setThreadsOption(ArrayList command) {
        String numThreadsText = ProverUIActivator.getDefault().getPreferenceStore().getString(ProverSecondPreferencePage.NUM_THREADS_KEY);
        if (numThreadsText.trim().length() == 0) {
            return ;
        }
        command.add(ITLAPMOptions.THREADS); 
        command.add(numThreadsText); 
    }
    
    /**
     * If the user has specified a solver preference pref,
     * then adds the appropriate entries to the list command of arguments.
     * @return
     */
    public static void setSolverOption(ArrayList command) {
        String solverText = ProverUIActivator.getDefault().getPreferenceStore().getString(ProverSecondPreferencePage.SOLVER_KEY);
        if (solverText.trim().length() == 0) {
            return;
        }
        command.add(ITLAPMOptions.SOLVER);
        command.add("\"" + solverText + "\""); 
    }
    
    /**
     * If the user has specified a solver preference pref,
     * then adds the appropriate entries to the list command of arguments.
     * @return
     */
    public static void setSafeFPOption(ArrayList command) {
        boolean safefp = ProverUIActivator.getDefault().getPreferenceStore().getBoolean(ProverSecondPreferencePage.SAFEFP_KEY);
        if (safefp) {
            command.add(ITLAPMOptions.SAFEFP); 
        }    
    }
}
