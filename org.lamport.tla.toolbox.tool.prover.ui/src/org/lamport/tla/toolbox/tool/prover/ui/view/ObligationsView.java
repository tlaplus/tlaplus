package org.lamport.tla.toolbox.tool.prover.ui.view;

import java.util.HashMap;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.ExpandBar;
import org.eclipse.swt.widgets.ExpandItem;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.prover.util.ProverHelper;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A view that shows information about interesting
 * obligations.
 * 
 * This view can be updated with information about
 * an obligation using the static method {@link ObligationsView#updateObligationView(IMarker)}.
 * Check the method documentation for how it works.
 * 
 * When the method is opened, it searches for all obligation markers on any module in the
 * currently opened project, where the currently opened project is the project returned
 * by {@link Spec#getProject()} for the currently opened spec. This view assumes
 * that all such markers are from the same run of the prover and are from the most
 * recent run of the prover on any module in the project.
 * 
 * @author Daniel Ricketts
 *
 */
public class ObligationsView extends ViewPart
{

    public static final String VIEW_ID = "org.lamport.tla.toolbox.tool.prover.ui.rejectedObligations";
    private ExpandBar bar = null;
    /**
     * A map of obligation id (as an Integer object)
     * to {@link ExpandItem}s.
     */
    private HashMap items;
    /**
     * Listens to when the user clicks
     * on an item's widget and jumps to the marker.
     * 
     * This listener assumes that the data of the widget
     * is the marker. In general, every widget has a data
     * field that can be any object. In the method
     * newMarker(), we set the widget data to be the marker
     * for widgets that should jump to that marker.
     */
    private Listener listener = new Listener() {

        public void handleEvent(Event event)
        {
            if (event.type == SWT.MouseDown)
            {

                if (event.widget.getData() instanceof IMarker)
                {
                    TLAMarkerHelper.gotoMarker((IMarker) event.widget.getData());
                }
            }
        }
    };

    public ObligationsView()
    {
        items = new HashMap();
    }

    public void createPartControl(Composite parent)
    {
        /*
         * Create the expand bar that will contain
         * a list of ExpandItems with interesting information
         * about obligations. These items are created
         * in the method newMarker().
         */
        bar = new ExpandBar(parent, SWT.V_SCROLL | SWT.BORDER);
        bar.setSpacing(8);

        /*
         * Retrieve all obligation markers on any module in the
         * currently opened project, where the currently opened project is the project returned
         * by {@link Spec#getProject()} for the currently opened spec. This view assumes
         * that all such markers are from the same run of the prover and are from the most
         * recent run of the prover on any module in the project.
         */
        try
        {
            IMarker[] markers = ToolboxHandle.getCurrentSpec().getProject().findMarkers(ProverHelper.OBLIGATION_MARKER,
                    false, IResource.DEPTH_ONE);
            for (int i = 0; i < markers.length; i++)
            {
                newMarker(markers[i]);
            }
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    /**
     * Updates the view with the information in this marker. If the marker is not
     * of the type {@link ProverHelper#OBLIGATION_MARKER} then this method will have
     * no effect.
     * 
     * Must be run from the UI thread.
     * 
     * @param marker
     */
    public static void updateObligationView(IMarker marker)
    {

        ObligationsView oblView = (ObligationsView) UIHelper.openView(VIEW_ID);
        if (oblView != null)
        {
            oblView.newMarker(marker);
        }

    }

    /**
     * Adds the information from the marker to the view. Should be
     * a marker of type {@link ProverHelper#OBLIGATION_METHOD}.
     * 
     * If there is already an item with information of the same
     * obligation as the marker, that item is updated. If no
     * such item exists, a new one is created.
     */
    private void newMarker(IMarker marker)
    {
        try
        {
            Assert.isTrue(marker.getType().equals(ProverHelper.OBLIGATION_MARKER),
                    "Non obligation marker passed to newMarker method. This is a bug.");
            int id = marker.getAttribute(ProverHelper.OBLIGATION_ID, -1);
            if (id != -1)
            {
                /*
                 * Try to retrieve an existing item with the same id.
                 */
                ExpandItem item = (ExpandItem) items.get(new Integer(id));

                /*
                 * If the marker represents an obligation that is
                 * not interesting, we dispose of the existing item
                 * (if there is one) and then return. There is nothing
                 * more to do.
                 */
                if (!ProverHelper.isInterestingObligation(marker))
                {
                    if (item != null)
                    {
                        item.getControl().dispose();
                        item.dispose();
                        items.remove(new Integer(id));
                    }
                    return;
                }

                /*
                 * If there is no existing item, create
                 * a new one.
                 */
                if (item == null)
                {
                    item = new ExpandItem(bar, SWT.None, 0);

                    /*
                     * Create the widget that will appear when the
                     * item is expanded.
                     */
                    Composite oblWidget = new Composite(bar, SWT.LINE_SOLID);
                    GridLayout gl = new GridLayout(1, true);
                    // no margin around the widget.
                    gl.marginWidth = 0;
                    gl.marginHeight = 0;
                    oblWidget.setLayout(gl);

                    /*
                     * We use a source viewer to display the
                     * obligation. We could simply use StyledText,
                     * but by using a source viewer, we leave open
                     * the possibility of configuring it with a source
                     * viewer configuration that will perform syntax
                     * highlighting of the obligation. This might be nice,
                     * but is not a top priority.
                     */
                    SourceViewer viewer = new SourceViewer(oblWidget, null, SWT.READ_ONLY | SWT.MULTI | SWT.WRAP);
                    StyledText text = viewer.getTextWidget();

                    // set the viewers document to the obligation.
                    String oblString = marker.getAttribute(ProverHelper.OBLIGATION_STRING, "");
                    viewer.setDocument(new Document(oblString.trim()));

                    item.setControl(oblWidget);
                    item.setExpanded(true);

                    /*
                     * Set the data to be the marker so that when
                     * the user clicks on the item, we can jump to that marker.
                     * 
                     * See the documentation for listener.
                     */
                    item.setData(marker);
                    viewer.getTextWidget().setData(marker);
                    oblWidget.setData(marker);
                    item.addListener(SWT.MouseDown, listener);
                    viewer.getTextWidget().addListener(SWT.MouseDown, listener);
                    oblWidget.addListener(SWT.MouseDown, listener);

                    /*
                     * Give the item the appropriate number of lines
                     * to display the entire obligation.
                     */
                    item.setHeight(text.getLineHeight() * text.getLineCount());
                    items.put(new Integer(id), item);
                }

                /*
                 * Whether this marker gives information for an existing
                 * item or a new item, we always update the title of the
                 * item to display the current status of the obligation.
                 */
                String status = marker.getAttribute(ProverHelper.OBLIGATION_STATUS, "Unknown");
                String method = marker.getAttribute(ProverHelper.OBLIGATION_METHOD, "");
                item.setText("Obligation " + id + " - status : " + status + " - method : " + method);

            }
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }

    public void setFocus()
    {
        /*
         * Set focus on appropriate control to which
         * context help is attached.
         */
    }
}
