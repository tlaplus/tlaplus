package org.lamport.tla.toolbox.tool.prover.ui.status;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.st.Location;

/**
 * This class contains static methods for installing and removing markers indicating proof
 * step status.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProofStepStatusMarkerHelper
{

    /**
     * Super type for the following four marker types for step status.
     */
    public static final String STEP_STATUS_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.proofStepStatus";
    /**
     * Marker type indicating that for a step, all obligations have proofs that are checked
     */
    public static final String FULLY_CHECKED_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.fullyCheckedStep";
    /**
     * Marker type indicating that for a step, all obligations have proofs or proof omitted that are checked.
     */
    public static final String CHECK_OR_EXPL_OMIT_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.checkedOrExplicitOmitStep";
    /**
     * Marker type indicating that for a step, all written proofs are checked.
     */
    public static final String WRITTEN_PROOFS_CHECKED_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.writtenProofsCheckedStep";
    /**
     * Marker type indicating that for a step, there exists an obligation that was rejected.
     */
    public static final String FAILED_OBS_FOR_STEP_MARKER = "org.lamport.tla.toolbox.tool.prover.ui.obligationFailedForStep";

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
        if (module != null && module instanceof IFile)
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
                markerAttributes.put(IMarker.CHAR_START, new Integer(stepRegion.getOffset()));
                markerAttributes.put(IMarker.CHAR_END, new Integer(stepRegion.getOffset() + stepRegion.getLength()));

                newMarker.setAttributes(markerAttributes);

                /*
                 * Remove any overlapping existing markers.
                 */
                IMarker[] existingMarkers = module.findMarkers(STEP_STATUS_MARKER, true, IResource.DEPTH_ZERO);
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
            }
        } else
        {
            ProverUIActivator.logDebug("A module could not be located for a step status.\n" + "Status : "
                    + status.getStatus() + "\nLocation : " + location);
        }
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
            return FULLY_CHECKED_MARKER;
        } else if (status.equals(ProofStepStatus.CHECK_OR_EXPL_OMIT))
        {
            return CHECK_OR_EXPL_OMIT_MARKER;
        } else if (status.equals(ProofStepStatus.WRITTEN_PROOFS_CHECKED))
        {
            return WRITTEN_PROOFS_CHECKED_MARKER;
        } else if (status.equals(ProofStepStatus.FAILED_OBS_FOR_STEP))
        {
            return FAILED_OBS_FOR_STEP_MARKER;
        }
        return null;
    }

    /**
     * Converts a {@link TLAPMMessage} to a {@link ProofStepStatus}. Returns
     * null if the message is not a message about the status of a proof step.
     * The proof step status can be added as a marker to the module by calling
     * {@link ProofStepStatusMarkerHelper#newStepStatus(ProofStepStatus)}.
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
}
