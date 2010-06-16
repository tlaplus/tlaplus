package org.lamport.tla.toolbox.tool.prover.ui.util;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.ModuleParserLauncher;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob;
import org.lamport.tla.toolbox.tool.prover.job.ProverJobRule;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob.ProverJobMatcher;
import org.lamport.tla.toolbox.tool.prover.output.internal.ProverLaunchDescription;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatus;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepTuple;
import org.lamport.tla.toolbox.tool.prover.ui.view.ObligationsView;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.LeafProofNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.UseOrHideNode;
import tla2sany.st.Location;
import util.UniqueString;

/**
 * Helper methods for the launching of the prover. There are 
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
    /**
     * Attribute on an obligation marker giving the String status of the obligation.
     */
    public static final String OBLIGATION_STATUS = "org.lamport.tla.toolbox.tool.prover.obStatus";
    /**
     * Attribute on an obligation marker giving the String method of the obligation.
     */
    public static final String OBLIGATION_METHOD = "org.lamport.tla.toolbox.tool.prover.obMethod";
    /**
     * Attribute on an obligation marker giving the formatted String of the obligation.
     */
    public static final String OBLIGATION_STRING = "org.lamport.tla.toolbox.tool.prover.obString";

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
     * Attribute on a SANY marker giving the location of the proof
     * step the last time the prover was launched for a proof step
     * status check.
     */
    public static final String SANY_LOC_ATR = "org.lamport.tla.toolbox.tool.prover.ui.sanyLoc";

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
     * has been proved by the value of the "meth" field.
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
    /**
     * Obligation status indicating that the obligation
     * has been skipped by the value of the "meth" field.
     */
    public static final String SKIPPED = "skipped";
    /**
     * Obligation status indicating that the obligation
     * has been checked.
     */
    public static final String CHECKED = "checked";
    /**
     * Obligation status indicating that the checking
     * has failed on the obligation.
     */
    public static final String CHECKING_FAILED = "checking failed";
    /**
     * Obligation status indicating that checking an obligation
     * was interrupted.
     */
    public static final String CHECKING_INTERUPTED = "checking interrupted";
    /**
     * Obligation status indicating that the obligation
     * has been proved in a prior run of the prover.
     */
    public static final String PROVED_ALREADY = "proved (already processed)";
    /**
     * Obligation status indicating that the obligation
     * was determined to be trivial in a prior run of the prover.
     */
    public static final String TRIVIAL_ALREADY = "trivial (already processed)";
    /**
     * Obligation status indicating that proving the obligation
     * failed in a prior run of the prover.
     */
    public static final String FAILED_ALREADY = "failed (already processed)";
    /**
     * Obligation status indicating that the obligation
     * has been checked in a prior run of the prover.
     */
    public static final String CHECKED_ALREADY = "checked (already processed)";
    /**
     * Obligation status indicating that the obligation
     * has not yet been sent anywhere to be proved.
     */
    public static final String TO_BE_PROVED = "to be proved";

    /***********************************************************************************
     * Step status marker types.                                                       *
     ***********************************************************************************/
    /**
     * Marker type corresponding to the status {@link StepStatusMessage#PROVING_FAILED}
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
     * Map from {@link Integer} ids of obligations
     * to {@link ObligationStatus}
     */
    private static HashMap obsMap = new HashMap();
    /**
     * Map from {@link LevelNode}s to {@link StepTuple}s.
     */
    private static HashMap stepMap = new HashMap();
    /**
     * Map from {@link Integer} line numbers of steps to
     * the last {@link StepStatusMessage} reported by the prover
     * for that step.
     */
    private static HashMap stepMessageMap = new HashMap();

    /**
     * Removes all markers indicating obligation information on  a resource. Does
     * nothing if the resource does not exist. It deletes these markers only at one level
     * under the resource.
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
     * Returns true iff the marker is of the type
     * {@link ProverHelper#OBLIGATION_MARKER} and represents
     * an obligation that is in an "interesting" state. Interesting
     * currently means one of:
     * 
     * {@link #BEING_PROVED}
     * {@link #FAILED}
     * {@link #FAILED_ALREADY}
     * {@link #CHECKING_FAILED}
     * {@link #CHECKING_INTERUPTED}
     * 
     * @param marker
     * @return
     * @throws CoreException 
     */
    public static boolean isInterestingObligation(IMarker marker)
    {
        /*
         * Should return true iff that status is one of some collection of strings.
         * 
         * A status is interesting if it contains the string "beingproved",
         * e.g. "beingproved(3s)".
         */
        String obStatus = marker.getAttribute(OBLIGATION_STATUS, "");
        return obStatus.contains(BEING_PROVED) || obStatus.equals(FAILED) || obStatus.equals(FAILED_ALREADY)
                || obStatus.equals(CHECKING_FAILED) || obStatus.equals(CHECKING_INTERUPTED);
    }

    /**
     * Returns true iff the marker represents an obligation that is
     * finished being processed in any way (proving or checking).
     * 
     * The description gives information about the parameters used to launch
     * the prover.
     * 
     * @param message
     * @param description
     * @return
     * @throws CoreException 
     */
    public static boolean isObligationFinished(ObligationStatusMessage message, ProverLaunchDescription description)
    {

        String status = message.getStatus();

        boolean isTrivial = status.equals(TRIVIAL) || status.equals(TRIVIAL_ALREADY);

        if (!description.isCheckProofs())
        {
            return isTrivial || status.equals(PROVED) || status.equals(PROVED_ALREADY);
        }

        if (description.isCheckProofs())
        {
            return isTrivial || status.equals(CHECKED) || status.equals(CHECKED_ALREADY);
        }
        return false;
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
     * It takes the following steps:
     * 
     * 1.) Call {@link #removeSANYStepMarkers(IResource)} on the module.
     * 2.) If level node is not null, call {@link #removeStatusFromTree(IFile, LevelNode)}. Else
     *     call {@link #removeStatusFromModule(IResource)}.
     * 3.) If levelNode is null, then the following is done for the entire module.
     *     If it is not null, the following is only done for the tree rooted at levelNode:
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
     * @param module
     * @throws CoreException 
     */
    public static void prepareModuleForProverLaunch(IFile module, LevelNode levelNode) throws CoreException
    {
        removeSANYStepMarkers(module);
        if (levelNode == null)
        {
            removeStatusFromModule(module);
        } else
        {
            removeStatusFromTree(module, levelNode);
        }
        /*
         * Clear the maps that hold information about obligations
         * and steps.
         */
        obsMap.clear();
        stepMap.clear();
        stepMessageMap.clear();

        if (levelNode != null)
        {
            prepareTreeForProverLaunch(levelNode, module);
            return;
        }

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
                prepareTreeForProverLaunch(topLevelNodes[i], module);
            }
        }
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
     * @param theoremNode
     * @throws CoreException 
     */
    public static StepTuple prepareTreeForProverLaunch(LevelNode levelNode, IResource module) throws CoreException
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
             * Create the tuple and return the levelNode.
             */
            StepTuple stepTuple = new StepTuple();
            stepTuple.setSanyMarker(marker);
            stepMap.put(levelNode, stepTuple);

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

                        /*
                         * Recursively put markers on each child node.
                         */
                        for (int i = 0; i < steps.length; i++)
                        {
                            StepTuple childTuple = prepareTreeForProverLaunch(steps[i], module);
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
                        // leaf proof
                        LeafProofNode leafProof = (LeafProofNode) proof;
                        if (leafProof.getOmitted())
                        {
                            stepTuple.setStatus(getIntFromStringStatus(StepStatusMessage.OMITTED));
                        }
                    }
                } else
                {
                    // missing proof
                    stepTuple.setStatus(getIntFromStringStatus(StepStatusMessage.MISSING_PROOFS));
                }

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
     * Takes a string produced by {@link ProverHelper#locToString(Location)}
     * and produces a {@link Location}.
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
     * {@link #STEP_CHECKED_MARKER}
     * {@link #STEP_CHECKING_FAILED_MARKER}
     * {@link #STEP_MISSING_MARKER}
     * {@link #STEP_OMITTED_MARKER}
     * {@link #STEP_PROVED_MARKER}
     * {@link #STEP_PROVING_FAILED_MARKER}
     * 
     * If the input is not one of these, this
     * method will return null.
     * 
     * @param status
     * @return
     */
    public static String statusStringToMarkerType(String status)
    {
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
            return STEP_PROVING_FAILED_MARKER;
        } else if (status.equals(StepStatusMessage.BEING_PROVED))
        {
            return STEP_BEING_PROVED_MARKER;
        }
        return null;
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
        default:
            return null;
        }
    }

    /**
     * Process the obligation message. If the status of the message is not
     * {@link #TO_BE_PROVED} then it creates a marker for that obligation
     * by calling {@link #newObligationStatus(ObligationStatusMessage)}. Else, it prepares
     * the necessary data structure for computing proof step statuses.
     * 
     * @param message
     * @param nodeToProve the step or module on which the prover was launched
     */
    public static void processObligationMessage(ObligationStatusMessage message, LevelNode nodeToProve)
    {
        if (message.getStatus().equals(TO_BE_PROVED))
        {
            /*
             * Find the LevelNode in the semantic tree containing
             * the obligation.
             */
            Location obLoc = message.getLocation();
            LevelNode levelNode = ResourceHelper.getLevelNodeFromTree(nodeToProve, obLoc.beginLine());
            if (levelNode == null)
            {
                ProverUIActivator.logDebug("Cannot find level node containing obligation at " + obLoc
                        + ". This is a bug.");
                return;
            }

            /*
             * Get the step tuple for the level node containing
             * the obligation. This is the parent of the obligation.
             * Create a new ObligationStatus with the step tuple as the
             * parent and the message status as the initial status, add
             * the obligation as a child of the step tuple. Adding
             * the obligation as a child will update the status of the parent.
             */
            StepTuple stepTuple = (StepTuple) stepMap.get(levelNode);
            if (stepTuple != null)
            {
                ObligationStatus obStatus = new ObligationStatus(stepTuple, getIntFromStringStatus(message.getStatus()));
                stepTuple.addChild(obStatus);
                obsMap.put(new Integer(message.getID()), obStatus);
            } else
            {
                ProverUIActivator.logDebug("Cannot find a step tuple for level node at " + levelNode.getLocation()
                        + ". This is a bug.");
            }
        } else
        {
            /*
             * Update the status of the obligation. The obligation will
             * inform its parents step that its status should be updated.
             * 
             * Don't update the status if the status is checking interrupted.
             */
            if (!message.getStatus().equals(CHECKING_INTERUPTED))
            {
                ObligationStatus obStatus = (ObligationStatus) obsMap.get(new Integer(message.getID()));
                obStatus.setStatus(getIntFromStringStatus(message.getStatus()));
            }

            // create the marker and update the obligations view
            final IMarker obMarker = newObligationStatus(message);
            UIHelper.runUIAsync(new Runnable() {

                public void run()
                {
                    ObligationsView.updateObligationView(obMarker);
                }
            });
        }
    }

    /**
     * Installs a new marker on the obligation in the message or updates the existing
     * marker on that obligation (if there is one) with the information contained in
     * message.
     * 
     * The message location should be for a module in the currently opened spec. If no
     * such module exists, this method returns null.
     * 
     * Returns the marker created or updated.
     * 
     * @param message must not be null
     */
    public static IMarker newObligationStatus(ObligationStatusMessage message)
    {
        Location location = message.getLocation();
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
                /*
                 * First try to find an existing marker with the same id
                 * and update it.
                 */
                IMarker[] markers = module.findMarkers(OBLIGATION_MARKER, false, IResource.DEPTH_ZERO);

                // the marker to be updated or created from the message
                IMarker marker = null;
                for (int i = 0; i < markers.length; i++)
                {
                    if (markers[i].getAttribute(OBLIGATION_ID, -1) == message.getID())
                    {

                        // DEBUG
                        // System.out.println("Marker updated for obligation from message \n" + message);
                        marker = markers[i];
                        break;
                    }
                }

                if (marker == null)
                {
                    // marker not found, create new one
                    marker = module.createMarker(OBLIGATION_MARKER);
                    marker.setAttribute(OBLIGATION_ID, message.getID());
                }

                marker.setAttribute(OBLIGATION_METHOD, message.getMethod());
                marker.setAttribute(OBLIGATION_STATUS, message.getStatus());
                /*
                 * The obligation string is not sent by the prover for every message.
                 * It is only sent once when the obligation is first interesting.
                 * Thus, message.getObString() can be null. Everytime a new message comes
                 * in for a given id, we set the obligation string. This way, when the obligation
                 * string is actually sent by the prover, it is set on the marker.
                 */
                marker.setAttribute(OBLIGATION_STRING, message.getObString());

                fileDocumentProvider.connect(fileEditorInput);
                IDocument document = fileDocumentProvider.getDocument(fileEditorInput);
                IRegion obRegion = AdapterFactory.locationToRegion(document, location);
                /*
                 * For marking a region that starts at offset o and has length l, the
                 * start character is o and the end character is o+l.
                 */
                marker.setAttribute(IMarker.CHAR_START, obRegion.getOffset());
                marker.setAttribute(IMarker.CHAR_END, obRegion.getOffset() + obRegion.getLength());

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
     * step. Searches for an existing SANY marker
     * with the same location as the status. If found, replaces
     * this marker with the appropriate step status marker. If
     * a SANY marker is not found, this is a bug and will be
     * printed out on the console.
     * 
     * @param status
     */
    public static void newStepStatusMessage(StepStatusMessage status)
    {
        stepMessageMap.put(new Integer(status.getLocation().beginLine()), status);

        // if (status == null)
        // {
        // return;
        // }
        // /*
        // * Create a marker located at the proof step.
        // *
        // * The type of the marker depends on the status.
        // */
        // Location location = status.getLocation();
        // IResource module = ResourceHelper.getResourceByModuleName(location.source());
        // if (module != null && module instanceof IFile && module.exists())
        // {
        // /*
        // * Try to find an existing SANY marker.
        // *
        // * For the moment, if an existing SANY marker is not
        // * found, put a marker at the location given by the
        // * message location. Also log a debug message saying
        // * a sany marker has not been found.
        // *
        // * If a sany marker is found, put a marker at the current location
        // * of the sany marker (not at the SANY location attribute of the sany marker).
        // */
        // IMarker sanyMarker = findSANYMarker(module, location);
        // try
        // {
        // /*
        // * If the status string does not correspond
        // * to a marker type, then do not create a marker.
        // */
        // String markerType = statusStringToMarkerType(status.getStatus());
        //
        // if (markerType == null)
        // {
        // ProverUIActivator
        // .logDebug("Status of proof step does not correspond to an existing marker type. The status is "
        // + status.getStatus());
        // return;
        // }
        //
        // IMarker newMarker = module.createMarker(markerType);
        // Map markerAttributes = new HashMap(2);
        // // value based on whether a sany marker is found or not
        // int newCharStart;
        // int newCharEnd;
        // if (sanyMarker != null)
        // {
        // newCharStart = sanyMarker.getAttribute(IMarker.CHAR_START, 0);
        // newCharEnd = sanyMarker.getAttribute(IMarker.CHAR_END, 0);
        // } else
        // {
        // ProverUIActivator.logDebug("Existing SANY marker not found for location " + location
        // + ". This is a bug.");
        // // the region from the tlapm message
        // IRegion messageRegion = AdapterFactory.locationToRegion(location);
        // /*
        // * For marking a region that starts at offset o and has length l, the
        // * start character is o and the end character is o+l.
        // */
        // newCharStart = messageRegion.getOffset();
        // newCharEnd = messageRegion.getOffset() + messageRegion.getLength();
        // return;
        // }
        //
        // /*
        // * Remove any existing step status markers that overlap
        // * with the new step status marker.
        // */
        // IMarker[] existingMarkers = module.findMarkers(ProverHelper.STEP_STATUS_MARKER, true,
        // IResource.DEPTH_ZERO);
        // for (int i = 0; i < existingMarkers.length; i++)
        // {
        // IMarker existingMarker = existingMarkers[i];
        // int existingCharStart = existingMarker.getAttribute(IMarker.CHAR_START, -1);
        // int existingCharEnd = existingMarker.getAttribute(IMarker.CHAR_END, -1);
        //
        // // conditions for overlapping
        // if (existingCharStart < newCharEnd && existingCharEnd > newCharStart)
        // {
        // existingMarker.delete();
        // }
        // }
        //
        // markerAttributes.put(IMarker.CHAR_START, new Integer(newCharStart));
        // markerAttributes.put(IMarker.CHAR_END, new Integer(newCharEnd));
        // newMarker.setAttributes(markerAttributes);
        //
        // } catch (CoreException e)
        // {
        // ProverUIActivator.logError("Error creating new status marker.", e);
        // }
        // } else
        // {
        // ProverUIActivator.logDebug("A module could not be located for a step status.\n" + "Status : "
        // + status.getStatus() + "\nLocation : " + location);
        // }
    }

    /**
     * Compares the step status computations of the TLAPM and the toolbox.
     * Any discrepancies are reported. Currently the reporting is to the
     * console.
     */
    public static void compareStepStatusComputations()
    {
        Collection stepTuples = stepMap.values();
        for (Iterator it = stepTuples.iterator(); it.hasNext();)
        {
            StepTuple stepTuple = (StepTuple) it.next();
            Location stepLoc = stringToLoc(stepTuple.getSanyMarker().getAttribute(SANY_LOC_ATR, ""));
            StepStatusMessage stepMessage = (StepStatusMessage) stepMessageMap.remove(new Integer(stepLoc.beginLine()));
            if (stepMessage == null)
            {
                System.out.println("NO STATUS BUG :\n No TLAPM step status message found for the step at " + stepLoc);
            } else if (!stepMessage.getStatus().equals(statusIntToStatusString(stepTuple.getStatus())))
            {
                System.out.println("DIFFERENT STATUS BUG : \n Loc : " + stepLoc + "\n TLAPM : "
                        + stepMessage.getStatus() + "\n Toolbox : " + statusIntToStatusString(stepTuple.getStatus()));
            }
        }

        Collection remainingMessages = stepMessageMap.values();
        for (Iterator it = remainingMessages.iterator(); it.hasNext();)
        {
            StepStatusMessage message = (StepStatusMessage) it.next();
            System.out.println("NO STATUS BUG :\n No Toolbox step status message found for the step at "
                    + message.getLocation());
        }
    }

    public static void newStepStatusMarker(IMarker sanyMarker, String status)
    {
        if (status == null)
        {
            return;
        }

        try
        {
            IResource module = sanyMarker.getResource();
            /*
             * If the status string does not correspond
             * to a marker type, then do not create a marker.
             */
            String markerType = statusStringToMarkerType(status);

            if (markerType == null)
            {
                ProverUIActivator
                        .logDebug("Status of proof step does not correspond to an existing marker type. The status is "
                                + status);
                return;
            }

            IMarker newMarker = module.createMarker(markerType);
            Map markerAttributes = new HashMap(2);
            // char start and end of the marker to be created
            int newCharStart = sanyMarker.getAttribute(IMarker.CHAR_START, 0);
            int newCharEnd = sanyMarker.getAttribute(IMarker.CHAR_END, 0);

            /*
             * Remove any existing step status markers that overlap
             * with the new step status marker.
             */
            IMarker[] existingMarkers = module.findMarkers(ProverHelper.STEP_STATUS_MARKER, true, IResource.DEPTH_ZERO);
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

            markerAttributes.put(IMarker.CHAR_START, new Integer(newCharStart));
            markerAttributes.put(IMarker.CHAR_END, new Integer(newCharEnd));
            newMarker.setAttributes(markerAttributes);

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
     * step or a top level USE node. A step is at the caret if it is the first
     * step on the line containing the caret.
     * 
     * If there is not a step at the caret, this method will show a message
     * indicating this to the user and will not launch the prover.
     * 
     * If there are dirty editors open, this method will prompt the user
     * to save them before continuing. If there is not a valid parse result
     * available, this method will parse the module in the editor with focus.
     * If there are parse errors, the prover will not be launched, but the parse
     * error window will show the errors.
     * 
     * If statusCheck is true, this tells prover job to launch the prover
     * for status checking, not proving.
     * 
     * @return
     */
    public static void runProverForActiveSelection(boolean statusCheck)
    {
        /*
         * This method works by scheduling a ProverJob. The ProverJob
         * requires a full file system path to the module for which it is launched
         * and the node on which the prover will be launched. In order
         * to do this, this method will take the following steps:
         * 
         * 1.) Prompt the user to save any modules that are currently open
         *     and unsaved.
         * 2.) Get the active module editor.
         * 3.) Try to obtain a valid parse result for the module in the active editor.
         *     A valid parse result is one that was created since the module was last
         *     written. If there is no valid parse result available, then prompt the user
         *     to parse the module (or maybe just always parse the module). This creates
         *     a valid parse result because the parsing is run in the UI thread.
         * 4.) Check if there are errors in the valid parse result obtained in step 3. If
         *     there are errors, return on this method. There is no need to show a message
         *     to the user in this case because the parse errors view will pop open anyway.
         * 5.) Get the LevelNode representing a step or top level use/hide containing the caret,
         *     if the caret is at such a node.
         * 6.) If a LevelNode is not found in step 5, show a message to the user saying
         *     the caret is not at a step and return on this method.
         * 7.) Create and schedule a prover job if a level node is found in step 5.
         * 
         * Note that at step 6 ,there are some other possibilities:
         *     -If the caret is not at any proof step, check the whole module.
         *     -If the caret is at a step without a proof, check the whole module.
         *     -If the caret is at a step without a proof, show a message to the user.
         *     -If the caret is at a step without a proof, disable this handler.
         *     -If the caret is not at any proof step, disable this handler.
         *     -If the caret is not at a step with a proof, ask the user if he wants
         *      to check the entire module.
         */

        /**********************************************************
         * Step 1                                                 *
         **********************************************************/
        boolean proceed = UIHelper.promptUserForDirtyModules();
        if (!proceed)
        {
            // the user cancelled
            return;
        }

        /**********************************************************
         * Step 2                                                 *
         **********************************************************/
        TLAEditor editor = EditorUtil.getTLAEditorWithFocus();
        Assert.isNotNull(editor, "CheckProofStepHandler was executed without a tla editor in focus. This is a bug.");

        /**********************************************************
         * Step 3                                                 *
         **********************************************************/
        IFile moduleFile = ((FileEditorInput) editor.getEditorInput()).getFile();
        ParseResult parseResult = ResourceHelper.getValidParseResult(moduleFile);

        if (parseResult == null)
        {
            parseResult = new ModuleParserLauncher().parseModule(moduleFile, new NullProgressMonitor());
        }

        /**********************************************************
         * Step 4                                                 *
         **********************************************************/
        if (parseResult.getStatus() != IParseConstants.PARSED)
        {
            return;
        }

        /**********************************************************
         * Step 5                                                 *
         **********************************************************/
        String moduleName = ResourceHelper.getModuleName(moduleFile);
        IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
        LevelNode nodeToProve = ResourceHelper.getPfStepOrUseHideFromMod(parseResult, moduleName,
                (ITextSelection) editor.getSelectionProvider().getSelection(), document);

        /**********************************************************
         * Step 6                                                 *
         **********************************************************/

        if (nodeToProve == null)
        {
            // ask user if he wants to check the entire module
            MessageDialog.openWarning(UIHelper.getShellProvider().getShell(), "Cannot launch prover",
                    "The caret is not at a step or USE node. It must be to launch this command.");
            return;
        }

        /***********************************************************
         * Step 7                                                  *
         ***********************************************************/
        ProverJob proverJob = new ProverJob(moduleFile, statusCheck, nodeToProve, false);
        // proverJob.setLocation(beginLine, 0, endLine, 0);
        proverJob.setUser(true);
        proverJob.setRule(new ProverJobRule());
        proverJob.schedule();
    }

    /**
     * Takes the String representation of the status of a step
     * or obligation and translates to the integer representation
     * of the status of a proof step.
     * 
     * This can be used to translate the String status of an obligation
     * to the integer status that can be used to compute the status of
     * the proof step containing that obligation.
     * 
     * Returns -1 if no known status is passed in. Returns 100 if
     * {@link #CHECKING_FAILED} is the status.
     * 
     * @param status
     * @return
     */
    public static int getIntFromStringStatus(String status)
    {
        if (status.equals(CHECKED) || status.equals(CHECKED_ALREADY))
        {
            return STEP_CHECKED_INT;
        } else if (status.equals(PROVED) || status.equals(PROVED_ALREADY) || status.equals(SKIPPED)
                || status.equals(TRIVIAL) || status.equals(TRIVIAL_ALREADY))
        {
            return STEP_PROVED_INT;
        } else if (status.equals(TO_BE_PROVED))
        {
            return STEP_TO_BE_PROVED_INT;
        } else if (status.equals(BEING_PROVED))
        {
            return STEP_BEING_PROVED_INT;
        } else if (status.equals(StepStatusMessage.OMITTED))
        {
            return STEP_PROOF_OMITTED_INT;
        } else if (status.equals(StepStatusMessage.MISSING_PROOFS))
        {
            return STEP_PROOF_MISSING_INT;
        } else if (status.equals(FAILED) || status.equals(FAILED_ALREADY))
        {
            return STEP_PROVING_FAILED_INT;
        } else if (status.equals(CHECKING_FAILED))
        {
            return STEP_CHECKING_FAILED_INT;
        }

        System.out.println("Unknown status : " + status);
        return STEP_UNKNOWN_INT;

    }
}
