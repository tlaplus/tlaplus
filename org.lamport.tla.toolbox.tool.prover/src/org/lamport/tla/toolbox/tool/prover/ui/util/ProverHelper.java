package org.lamport.tla.toolbox.tool.prover.ui.util;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob.ProverJobMatcher;
import org.lamport.tla.toolbox.tool.prover.output.IProverProcessOutputSink;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;
import org.lamport.tla.toolbox.tool.prover.ui.status.ProofStepStatus;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;
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

    /**
     * Type of marker that contains SANY information about a proof step.
     * In particular, it contains the location of the proof step as reported
     * by SANY when the prover was last launched for a step status update.
     * This location may not be the same as the marker's location
     * because the marker is sticky and the module may have been edited since
     * the prover was last launch for a status check.
     */
    public static final String SANY_MARKER = "";
    /**
     * Attribute on a SANY marker giving the location of the proof
     * step the last time the prover was launched for a proof step
     * status check.
     */
    public static final String SANY_LOC_ATR = "";
    /**
     * Delimiter used for representing
     * locations as strings.
     */
    public static final String LOC_DELIM = ":";

    /**
     * Obligation status that occurs when
     * zenon or isabelle "takes time" to prove an obligation.
     */
    public static final String BEING_PROVED = "beingproved";
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
    public static final String CHECKED_ALREADY = "checked (already processed";

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
         * A status is interesting if it contains the string being proved,
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
     * typeOfProverLaunch should be one of {@link IProverProcessOutputSink#TYPE_PROVE}
     * or {@link IProverProcessOutputSink#TYPE_CHECK}.
     * 
     * @param marker
     * @return
     * @throws CoreException 
     */
    public static boolean isObligationFinished(IMarker marker, int typeOfProverLaunch)
    {
        try
        {
            if (!marker.getType().equals(OBLIGATION_MARKER))
            {
                return false;
            }

            String status = marker.getAttribute(OBLIGATION_STATUS, "");

            boolean isTrivial = status.equals(TRIVIAL) || status.equals(TRIVIAL_ALREADY);

            if (typeOfProverLaunch == IProverProcessOutputSink.TYPE_PROVE)
            {
                return isTrivial || status.equals(PROVED) || status.equals(PROVED_ALREADY);
            }

            if (typeOfProverLaunch == IProverProcessOutputSink.TYPE_CHECK)
            {
                return isTrivial || status.equals(CHECKED) || status.equals(CHECKED_ALREADY);
            }
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
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
     * Creates all SANY step markers on the module. Puts a marker
     * on every step in the module with a proof. If there is no
     * valid parse result for the module, this method does nothing.
     * 
     * See {@link ProverHelper#SANY_MARKER} for a description of
     * these markers.
     * 
     * @param module
     * @throws CoreException 
     */
    public static void createSANYStepMarkers(IFile module) throws CoreException
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
        TheoremNode[] theorems = moduleNode.getTheorems();

        for (int i = 0; i < theorems.length; i++)
        {
            TheoremNode theoremNode = theorems[i];

            if (theoremNode.getLocation().source().equals(moduleName))
            {
                // found a theorem in the module
                createSANYMarkersForTheorem(theoremNode, module);
            }
        }
    }

    /**
     * Creates a SANY marker for theoremNode if it has a proof. Recursively
     * places SANY markers on each {@link TheoremNode} that is a child of
     * theoremNode and has a proof.
     * 
     * See {@link ProverHelper#SANY_MARKER} for a description of
     * these markers.
     * 
     * @param theoremNode
     * @throws CoreException 
     */
    public static void createSANYMarkersForTheorem(TheoremNode theoremNode, IResource module) throws CoreException
    {
        if (theoremNode == null)
        {
            return;
        }

        ProofNode proof = theoremNode.getProof();
        if (proof != null)
        {
            IMarker marker = module.createMarker(SANY_MARKER);
            marker.setAttribute(SANY_LOC_ATR, locToString(theoremNode.getLocation()));
            // TODO set location of marker. Which location do we use?

            if (proof instanceof NonLeafProofNode)
            {
                NonLeafProofNode nonLeafProof = (NonLeafProofNode) proof;
                LevelNode[] steps = nonLeafProof.getSteps();

                /*
                 * From the documentation of NonLeafProofNode,
                 * a step can be one of four types:
                 * 
                 * DefStepNode
                 * UseOrHideNode
                 * InstanceNode
                 * TheoremNode
                 * 
                 * Only TheoremNode can have a proof. Recursively
                 * put markers on each child theorem node.
                 */
                for (int i = 0; i < steps.length; i++)
                {
                    if (steps[i] instanceof TheoremNode)
                    {
                        createSANYMarkersForTheorem((TheoremNode) steps[i], module);
                    }
                }
            }
        }
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
     * is the same as the location passed to this method.
     * 
     * See {@link ProverHelper#SANY_MARKER} for a description of
     * these markers.
     * 
     * @param location
     * @param module
     * @return
     */
    public static IMarker findSANYStepMarker(IResource module, Location location)
    {
        return null;
    }

    /**
     * Converts a {@link TLAPMMessage} to a {@link ProofStepStatus}. Returns
     * null if the message is not a message about the status of a proof step.
     * The proof step status can be added as a marker to the module by calling
     * {@link ProverHelper#newStepStatus(ProofStepStatus)}.
     * 
     * It seems unnecessary to convert from a message to this proof step
     * status object, but I'm using this method in case we decide that the
     * Toolbox has to compute the status of proof steps from messages rather
     * than receiving the status of proof steps in the messages.
     * 
     * @param message
     * @return
     */
    public static ProofStepStatus messageToStatus(TLAPMMessage message)
    {
        if (message instanceof StepStatusMessage)
        {
            StepStatusMessage stepMessage = (StepStatusMessage) message;
            if (stepMessage.getLocation() != null && stepMessage.getStatus() != null)
            {
                return new ProofStepStatus(stepMessage.getStatus(), stepMessage.getLocation());
            }
        }
        return null;

    }

    /**
     * Converts the status string to the correct marker type.
     * The status string should be one of {@link ProofStepStatus#FULLY_CHECKED},
     * {@link ProofStepStatus#CHECK_OR_EXPL_OMIT}, {@link ProofStepStatus#WRITTEN_PROOFS_CHECKED},
     * or {@link ProofStepStatus#FAILED_OBS_FOR_STEP}. If the input is not one of these, this
     * method will return null.
     * 
     * @param status
     * @return
     */
    public static String statusStringToMarkerType(String status)
    {
        if (status.equals(ProofStepStatus.FULLY_CHECKED))
        {
            return ProverHelper.FULLY_CHECKED_MARKER;
        } else if (status.equals(ProofStepStatus.CHECK_OR_EXPL_OMIT))
        {
            return ProverHelper.CHECK_OR_EXPL_OMIT_MARKER;
        } else if (status.equals(ProofStepStatus.WRITTEN_PROOFS_CHECKED))
        {
            return ProverHelper.WRITTEN_PROOFS_CHECKED_MARKER;
        } else if (status.equals(ProofStepStatus.FAILED_OBS_FOR_STEP))
        {
            return ProverHelper.FAILED_OBS_FOR_STEP_MARKER;
        }
        return null;
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
                 * start character is o and the end character is o+l-1.
                 */
                marker.setAttribute(IMarker.CHAR_START, obRegion.getOffset());
                marker.setAttribute(IMarker.CHAR_END, obRegion.getOffset() + obRegion.getLength() - 1);

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
     * step. Does nothing if status is null.
     * 
     * @param status
     */
    public static void newStepStatus(ProofStepStatus status)
    {
        if (status == null)
        {
            return;
        }
        /*
         * Create a marker located at the proof step.
         * 
         * The type of the marker depends on the status.
         * 
         * If there is already a marker overlapping (in location)
         * with the new marker, remove the existing marker.
         */
        Location location = status.getLocation();
        IResource module = ResourceHelper.getResourceByModuleName(location.source());
        if (module != null && module instanceof IFile && module.exists())
        {
            /*
             * We need a document to convert the 4-int location to a 2-int
             * region. We use a FileDocumentProvider. It is disconnected
             * from the input in the finally block to avoid a memory leak.
             */
            FileEditorInput fileEditorInput = new FileEditorInput((IFile) module);
            FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
            try
            {
                fileDocumentProvider.connect(fileEditorInput);
                IDocument document = fileDocumentProvider.getDocument(fileEditorInput);

                IMarker newMarker = module.createMarker(statusStringToMarkerType(status.getStatus()));
                Map markerAttributes = new HashMap(2);

                IRegion stepRegion = AdapterFactory.locationToRegion(document, location);
                /*
                 * For marking a region that starts at offset o and has length l, the
                 * start character is o and the end character is o+l-1.
                 */
                markerAttributes.put(IMarker.CHAR_START, new Integer(stepRegion.getOffset()));
                markerAttributes
                        .put(IMarker.CHAR_END, new Integer(stepRegion.getOffset() + stepRegion.getLength() - 1));

                newMarker.setAttributes(markerAttributes);

                /*
                 * Remove any overlapping existing markers.
                 */
                IMarker[] existingMarkers = module.findMarkers(ProverHelper.STEP_STATUS_MARKER, true,
                        IResource.DEPTH_ZERO);
                for (int i = 0; i < existingMarkers.length; i++)
                {
                    IMarker existingMarker = existingMarkers[i];
                    int startChar = existingMarker.getAttribute(IMarker.CHAR_START, -1);
                    int endChar = existingMarker.getAttribute(IMarker.CHAR_END, -1);

                    if (stepRegion.getOffset() < startChar && stepRegion.getLength() + stepRegion.getOffset() > endChar)
                    {
                        // new marker overlaps with old marker
                        // remove old marker
                        existingMarker.delete();
                    }
                }
            } catch (CoreException e)
            {
                ProverUIActivator.logError("Error creating marker for new status.\n" + "Status : " + status.getStatus()
                        + "\nLocation : " + location, e);
            } catch (BadLocationException e)
            {
                ProverUIActivator.logError("Could not convert location to region for a step status.\n" + "Status : "
                        + status.getStatus() + "\nLocation : " + location, e);
            } finally
            {
                fileDocumentProvider.disconnect(fileEditorInput);
            }
        } else
        {
            ProverUIActivator.logDebug("A module could not be located for a step status.\n" + "Status : "
                    + status.getStatus() + "\nLocation : " + location);
        }
    }

    /**
     * Marker type indicating that for a step, there exists an obligation that was rejected.
     */
    public static final String FAILED_OBS_FOR_STEP_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.obligationFailedForStep";
    /**
     * Marker type indicating that for a step, all written proofs are checked.
     */
    public static final String WRITTEN_PROOFS_CHECKED_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.writtenProofsCheckedStep";
    /**
     * Marker type indicating that for a step, all obligations have proofs or proof omitted that are checked.
     */
    public static final String CHECK_OR_EXPL_OMIT_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.checkedOrExplicitOmitStep";
    /**
     * Marker type indicating that for a step, all obligations have proofs that are checked
     */
    public static final String FULLY_CHECKED_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.fullyCheckedStep";
    /**
     * Super type for the following four marker types for step status.
     */
    public static final String STEP_STATUS_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.proofStepStatus";

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
}
