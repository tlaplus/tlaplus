package org.lamport.tla.toolbox.tool.prover.ui.util;

import java.util.HashMap;
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
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.StepStatusMessage;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;
import org.lamport.tla.toolbox.tool.prover.ui.status.ProofStepStatus;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NonLeafProofNode;
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
     * @param marker
     * @param description
     * @return
     * @throws CoreException 
     */
    public static boolean isObligationFinished(IMarker marker, ProverLaunchDescription description)
    {
        try
        {
            if (!marker.getType().equals(OBLIGATION_MARKER))
            {
                return false;
            }

            String status = marker.getAttribute(OBLIGATION_STATUS, "");

            boolean isTrivial = status.equals(TRIVIAL) || status.equals(TRIVIAL_ALREADY);

            if (!description.isCheckProofs())
            {
                return isTrivial || status.equals(PROVED) || status.equals(PROVED_ALREADY);
            }

            if (description.isCheckProofs())
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
     * Creates SANY markers on all nodes in the module for which there can be
     * a prover status. A SANY marker stores the location of the node as returned
     * by SANY when the marker is created. Since markers are "sticky", SANY markers
     * can be used to map from locations returned by the prover to the current
     * location of a node. A location returned by the prover should equal
     * the SANY location of a SANY marker.
     * 
     * This currently puts SANY markers on all step or top level
     * USE node markers on the module. If there is no
     * valid parse result for the module, this method does nothing.
     * 
     * See {@link ProverHelper#SANY_MARKER} for a description of
     * these markers.
     * 
     * @param module
     * @throws CoreException 
     */
    public static void createSANYMarkers(IFile module) throws CoreException
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
                createSANYMarkersForTree(topLevelNodes[i], module);
            }
        }
    }

    /**
     * Creates a SANY marker for levelNode if it is a {@link TheoremNode} or a {@link UseOrHideNode}.
     * If it has a proof, this method recursively calls it self on all children.
     * 
     * See {@link ProverHelper#SANY_MARKER} for a description of
     * these markers.
     * 
     * @param theoremNode
     * @throws CoreException 
     */
    public static void createSANYMarkersForTree(LevelNode levelNode, IResource module) throws CoreException
    {
        if (levelNode == null)
        {
            return;
        }

        if (levelNode instanceof UseOrHideNode || levelNode instanceof TheoremNode)
        {
            IMarker marker = module.createMarker(SANY_MARKER);
            marker.setAttribute(SANY_LOC_ATR, locToString(levelNode.getLocation()));
        }

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
                            createSANYMarkersForTree((TheoremNode) steps[i], module);
                        }
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
     * is the same as the location passed to this method. Returns null
     * if such a marker is not found.
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
                    if (sanyLoc.equals(location))
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
     * step. Searches for an existing SANY marker
     * with the same location as the status. If found, replaces
     * this marker with the appropriate step status marker. If
     * a SANY marker is not found, this is a bug and will be
     * printed out on the console.
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
         */
        Location location = status.getLocation();
        IResource module = ResourceHelper.getResourceByModuleName(location.source());
        if (module != null && module instanceof IFile && module.exists())
        {
            IMarker sanyMarker = findSANYMarker(module, location);
            if (sanyMarker != null)
            {
                try
                {
                    IMarker newMarker = module.createMarker(statusStringToMarkerType(status.getStatus()));
                    Map markerAttributes = new HashMap(2);
                    markerAttributes.put(IMarker.CHAR_START,
                            new Integer(sanyMarker.getAttribute(IMarker.CHAR_START, 0)));
                    markerAttributes.put(IMarker.CHAR_END, new Integer(sanyMarker.getAttribute(IMarker.CHAR_END, 0)));

                    newMarker.setAttributes(markerAttributes);
                } catch (CoreException e)
                {
                    ProverUIActivator.logError("Error creating new status marker.", e);
                }
            } else
            {
                ProverUIActivator.logDebug("Existing SANY marker not found for location " + location
                        + ". This is a bug.");
            }
        } else
        {
            ProverUIActivator.logDebug("A module could not be located for a step status.\n" + "Status : "
                    + status.getStatus() + "\nLocation : " + location);
        }

        // if (module != null && module instanceof IFile && module.exists())
        // {
        // /*
        // * We need a document to convert the 4-int location to a 2-int
        // * region. We use a FileDocumentProvider. It is disconnected
        // * from the input in the finally block to avoid a memory leak.
        // */
        // FileEditorInput fileEditorInput = new FileEditorInput((IFile) module);
        // FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
        // try
        // {
        // fileDocumentProvider.connect(fileEditorInput);
        // IDocument document = fileDocumentProvider.getDocument(fileEditorInput);
        //
        // IMarker newMarker = module.createMarker(statusStringToMarkerType(status.getStatus()));
        // Map markerAttributes = new HashMap(2);
        //
        // IRegion stepRegion = AdapterFactory.locationToRegion(document, location);
        // /*
        // * For marking a region that starts at offset o and has length l, the
        // * start character is o and the end character is o+l-1.
        // */
        // markerAttributes.put(IMarker.CHAR_START, new Integer(stepRegion.getOffset()));
        // markerAttributes
        // .put(IMarker.CHAR_END, new Integer(stepRegion.getOffset() + stepRegion.getLength() - 1));
        //
        // newMarker.setAttributes(markerAttributes);
        //
        // // The following was commentted out
        // // because there should not longer be any overlapping
        // // markers. Any overlapping markers should be removed before
        // // launching the prover.
        // // /*
        // // * Remove any overlapping existing markers.
        // // */
        // // IMarker[] existingMarkers = module.findMarkers(ProverHelper.STEP_STATUS_MARKER, true,
        // // IResource.DEPTH_ZERO);
        // // for (int i = 0; i < existingMarkers.length; i++)
        // // {
        // // IMarker existingMarker = existingMarkers[i];
        // // int startChar = existingMarker.getAttribute(IMarker.CHAR_START, -1);
        // // int endChar = existingMarker.getAttribute(IMarker.CHAR_END, -1);
        // //
        // // if (stepRegion.getOffset() < startChar && stepRegion.getLength() + stepRegion.getOffset() > endChar)
        // // {
        // // // new marker overlaps with old marker
        // // // remove old marker
        // // existingMarker.delete();
        // // }
        // // }
        // } catch (CoreException e)
        // {
        // ProverUIActivator.logError("Error creating marker for new status.\n" + "Status : " + status.getStatus()
        // + "\nLocation : " + location, e);
        // } catch (BadLocationException e)
        // {
        // ProverUIActivator.logError("Could not convert location to region for a step status.\n" + "Status : "
        // + status.getStatus() + "\nLocation : " + location, e);
        // } finally
        // {
        // fileDocumentProvider.disconnect(fileEditorInput);
        // }
        // } else
        // {
        // ProverUIActivator.logDebug("A module could not be located for a step status.\n" + "Status : "
        // + status.getStatus() + "\nLocation : " + location);
        // }
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
        /*
         * We need a file document provider for the
         * module in order to get a document to convert
         * from the 4-int location provided by SANY
         * to the 2-int location of markers.
         */
        FileDocumentProvider fdp = new FileDocumentProvider();
        FileEditorInput input = new FileEditorInput(module);
        try
        {
            fdp.connect(input);
            IDocument document = fdp.getDocument(input);
            int beginLine = root.getLocation().beginLine();
            int endLine = root.getLocation().endLine();
            if (root instanceof TheoremNode && ((TheoremNode) root).getProof() != null)
            {
                endLine = ((TheoremNode) root).getProof().getLocation().endLine();
            }
            int beginChar = document.getLineOffset(beginLine);
            /*
             * In the following, we subtract 1 to get the end char.
             * 
             * For a marker representing a region that starts at offset o and has length l, the
             * start character is o and the end character is o+l-1.
             */
            int endChar = document.getLineOffset(endLine) + document.getLineLength(endLine) - 1;
            IMarker[] markers = module.findMarkers(STEP_STATUS_MARKER, true, IResource.DEPTH_ZERO);
            for (int i = 0; i < markers.length; i++)
            {
                int markerStartChar = markers[i].getAttribute(IMarker.CHAR_START, -1);
                int markerEndChar = markers[i].getAttribute(IMarker.CHAR_END, -1);

                if (markerStartChar >= beginChar && markerEndChar <= endChar)
                {
                    markers[i].delete();
                } else if (markerStartChar < beginChar && markerEndChar >= beginChar)
                {
                    markers[i].setAttribute(IMarker.CHAR_END, beginChar - 1);
                } else if (markerStartChar >= beginChar && markerEndChar > endChar)
                {
                    markers[i].setAttribute(IMarker.CHAR_END, endChar + 1);
                }
            }
        } catch (CoreException e)
        {
            ProverUIActivator.logError("Error removing status markers from tree rooted at " + root, e);
        } catch (BadLocationException e)
        {
            ProverUIActivator.logError("Error removing status markers from tree rooted at " + root, e);
        } finally
        {
            fdp.disconnect(input);
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

}
