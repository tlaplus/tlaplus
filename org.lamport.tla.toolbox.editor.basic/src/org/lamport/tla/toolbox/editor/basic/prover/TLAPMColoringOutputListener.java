package org.lamport.tla.toolbox.editor.basic.prover;

import java.util.HashMap;

import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatus;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMData;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.ITLAPMOutputSourceListener;
import org.lamport.tla.toolbox.tool.prover.ui.output.source.TLAPMOutputSourceRegistry;

import tla2sany.st.Location;

/**
 * Performs the status coloring of proofs.
 * 
 * @author Daniel Ricketts
 *
 */
public class TLAPMColoringOutputListener implements ITLAPMOutputSourceListener
{

    public static final String VERIFIED_TYPE = "org.lamport.tla.toolbox.editor.basic.verifiedProofStep";
    public static final String REJECTED_TYPE = "org.lamport.tla.toolbox.editor.basic.rejectedProofStep";
    private TLAEditor editor;

    public TLAPMColoringOutputListener(TLAEditor editor)
    {
        this.editor = editor;

        TLAPMOutputSourceRegistry.getInstance().addListener(this);
    }

    public IPath getFullModulePath()
    {
        return ((FileEditorInput) editor.getEditorInput()).getFile().getLocation();
    }

    public void newData(TLAPMData data)
    {
        if (data instanceof ObligationStatus)
        {
            ObligationStatus obRegion = (ObligationStatus) data;

            String type = null;
            if (obRegion.getStatus() == ObligationStatus.STATUS_VERIFIED)
            {
                type = VERIFIED_TYPE;
            } else if (obRegion.getStatus() == ObligationStatus.STATUS_REJECTED)
            {
                type = REJECTED_TYPE;
            }
            if (type != null)
            {
                Location loc = obRegion.getLocation();
                try
                {

                    IRegion locRegion = DocumentHelper.locationToRegion(editor.getDocumentProvider().getDocument(
                            editor.getEditorInput()), loc);
                    HashMap newAnnotations = new HashMap();
                    newAnnotations.put(new Annotation(type, false, ""), new Position(locRegion.getOffset(), locRegion
                            .getLength()));
                    editor.modifyRegularAnnotations(null, newAnnotations, null);
                } catch (BadLocationException e)
                {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
        }
    }

    /**
     * Removes itself as a listener from the {@link TLAPMOutputSourceRegistry}.
     */
    public void dispose()
    {
        TLAPMOutputSourceRegistry.getInstance().removeListener(this);
    }
}
