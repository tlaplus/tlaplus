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
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.st.Location;

/**
 * This class contains static methods for installing and removing markers
 * on proofs.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProofMarkerHelper
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
                IMarker[] markers = module.findMarkers(ProverHelper.OBLIGATION_MARKER, false, IResource.DEPTH_ZERO);

                // the marker to be updated or created from the message
                IMarker marker = null;
                for (int i = 0; i < markers.length; i++)
                {
                    if (markers[i].getAttribute(ProverHelper.OBLIGATION_ID, -1) == message.getID())
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
                    marker = module.createMarker(ProverHelper.OBLIGATION_MARKER);
                    marker.setAttribute(ProverHelper.OBLIGATION_ID, message.getID());
                }

                marker.setAttribute(ProverHelper.OBLIGATION_METHOD, message.getMethod());
                marker.setAttribute(ProverHelper.OBLIGATION_STATUS, message.getStatus());
                /*
                 * The obligation string is not sent by the prover for every message.
                 * It is only sent once when the obligation is first interesting.
                 * Thus, message.getObString() can be null. Everytime a new message comes
                 * in for a given id, we set the obligation string. This way, when the obligation
                 * string is actually sent by the prover, it is set on the marker.
                 */
                marker.setAttribute(ProverHelper.OBLIGATION_STRING, message.getObString());

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
     * {@link ProofMarkerHelper#newStepStatus(ProofStepStatus)}.
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
