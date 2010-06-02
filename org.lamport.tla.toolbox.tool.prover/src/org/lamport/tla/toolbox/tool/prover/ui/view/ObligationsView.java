package org.lamport.tla.toolbox.tool.prover.ui.view;

import java.util.HashMap;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.ExpandBar;
import org.eclipse.swt.widgets.ExpandItem;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.ScrollBar;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;
import org.lamport.tla.toolbox.util.FontPreferenceChangeListener;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A view that shows information about interesting
 * obligations.
 * 
 * This view can be updated with information about
 * an obligation using the static method {@link ObligationsView#updateObligationView(IMarker)}
 * with a marker that contains information about an obligation.
 * Check the method documentation for how it works.
 * 
 * It is important that whenever this view is open, it shows only information on obligations
 * from the currently opened project, where the currently opened project is the project returned
 * by {@link Spec#getProject()} for the currently opened spec.
 * This is maintained in the following two ways:
 * 
 * 1.) When the view is opened, the method createPartControl() is called. This creates
 * a new {@link ExpandBar} widget for displaying obligation item information with no items.
 * The method then searches for all obligation markers on any module in the
 * currently opened project. This view assumes that all such markers are from the
 * same run of the prover and are from the most recent run of the prover on any module
 * in the project. If any markers are found from the currently opened project, the expand bar
 * is populated with one item for each marker that has information about an "interesting"
 * obligation. If no such markers are found, the view is left empty.
 * 
 * 2.) The method {@link ObligationsView#refreshObligationView()} is called at the appropriate times.
 *
 *    -It is called when a spec is opened. This ensures that when the currently opened spec in the toolbox
 *     changes, obligation information from the previously opened spec is not shown.
 *    -It is called when obligation markers have been deleted. This should mean that the prover
 *     has been launched, causing the previous obligation markers to be removed. Calling refreshObligationView()
 *     will clear the information from these previous markers from the view, if the view is currently open.
 *     If the view is not currently open, it doesn't matter because the view stores no information.
 *     
 * The font and syntax coloring of the items in the view is the same as that of the tla editor. The
 * syntax coloring is done by configuring the obligation items with the {@link ObligationSourceViewerConfiguration}
 * and the font is done by adding a listener to the preference for text editor font.
 * 
 * Side note :  I've noticed that the documentation for {@link IWorkbenchPart} claims that createPartControl()
 * should also be called when the view is made invisible and then visible again, but experimentation
 * shows that this is not the case.
 * 
 * @author Daniel Ricketts
 *
 */
public class ObligationsView extends ViewPart
{

    public static final String VIEW_ID = "org.lamport.tla.toolbox.tool.prover.ui.rejectedObligations";
    /**
     * The beginning of the view name. The total view name will be
     * PART_NAME_BASE + moduleName.
     */
    public static final String PART_NAME_BASE = "Interesting Obligations for ";
    /**
     * The widget that displays a list of items, each
     * containing information about an interesting obligation.
     */
    private ExpandBar bar = null;
    /**
     * A map of obligation id (as an Integer object)
     * to {@link ExpandItem}s.
     */
    private HashMap items;
    /**
     * A map from {@link ExpandItem} to their
     * associated {@link SourceViewer}.
     */
    private HashMap viewers;
    /**
     * A listener that reacts to changes of the text editor font
     * by notifying all items in this view that they should update
     * their font.
     */
    private FontPreferenceChangeListener fontListener;
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
        viewers = new HashMap();
        fontListener = new FontPreferenceChangeListener(null, JFaceResources.TEXT_FONT);
        JFaceResources.getFontRegistry().addListener(fontListener);
    }

    public void createPartControl(Composite parent)
    {
        /*
         * Create the expand bar that will contain
         * a list of ExpandItems with interesting information
         * about obligations. The items for each obligation are created
         * in the method newMarker().
         */
        bar = new ExpandBar(parent, SWT.V_SCROLL | SWT.BORDER);
        bar.setSpacing(8);

        fillFromCurrentSpec();
    }

    /**
     * This method must be run from a UI thread.
     * 
     * Used to refresh the obligation view if it is currently open. If the view
     * is not currently open, this method does nothing. If the view is currently open,
     * this takes the following two steps:
     * 
     * 1.) Removes all items from the expand bar for this view.
     * 
     * 2.) Retrieve all obligation markers on any module in the
     * currently opened project, where the currently opened project is the project returned
     * by {@link Spec#getProject()} for the currently opened spec. This view assumes
     * that all such markers are from the same run of the prover and are from the most
     * recent run of the prover on any module in the project. For each such marker,
     * call {@link ObligationsView#newMarker(IMarker)}. This has the effect of repopulating
     * the expand bar with items if any of markers are for an interesting obligation.
     */
    public static void refreshObligationView()
    {

        ObligationsView oblView = (ObligationsView) UIHelper.findView(VIEW_ID);
        if (oblView != null)
        {

            /*
             * Remove all items in the bar.
             * 
             * For each item:
             * 1.) Dispose the item's control.
             * 2.) Dispose the item.
             * 
             * After disposing of all items, clear
             * the map of ids to items.
             */
            ExpandItem[] expandItems = oblView.bar.getItems();
            for (int i = 0; i < expandItems.length; i++)
            {
                oblView.removeItem(expandItems[i]);
            }

            /*
             * Fill the obligation view with markers from the current spec.
             * If there are no such markers, hide the view.
             */
            boolean hide = !oblView.fillFromCurrentSpec();

            if (hide)
            {
                UIHelper.getActivePage().hideView(oblView);
            }

        }

    }

    /**
     * Fills the obligation view with information
     * from all obligation markers in the currently
     * opened spec. Returns true iff the current spec
     * has obligation markers.
     */
    private boolean fillFromCurrentSpec()
    {
        try
        {
            IMarker[] markers = ProverHelper.getObMarkersCurSpec();
            if (markers != null)
            {
                for (int i = 0; i < markers.length; i++)
                {
                    updateItem(markers[i]);
                }

                return markers.length > 0;
            }

            return false;
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        return false;
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
        /*
         * If the marker is not interesting, try to find the view.
         * If the view is found update the view with that marker.
         * 
         * If the view is not found, there is no need to update it
         * with the new markers.
         * 
         * If the marker is interesting, open the view and update it.
         */
        ObligationsView oblView;
        if (!ProverHelper.isInterestingObligation(marker))
        {
            oblView = (ObligationsView) UIHelper.findView(VIEW_ID);
        } else
        {
            oblView = (ObligationsView) UIHelper.openView(VIEW_ID);
        }

        if (oblView != null)
        {

            String moduleName = marker.getResource().getName();
            if (!oblView.getPartName().equals(PART_NAME_BASE + moduleName))
            {
                oblView.setPartName(PART_NAME_BASE + moduleName);
            }

            oblView.updateItem(marker);

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
    private void updateItem(IMarker marker)
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
                        removeItem(item);
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
                     * obligation. This allows us to easily do
                     * syntax highlighting by configuring the source
                     * viewer with a source viewer configuration
                     * that basically takes some code from the editor
                     * plug-in. This code does the syntax highlighting.
                     * See ObligationSourceViewerConfiguration.
                     * 
                     * For the style bits, we want the source viewer to be read
                     * only, multiline, and have a horizontal scroll bar. We
                     * don't want the text to wrap because that makes the
                     * obligations difficult to read, so a horizontal scroll
                     * bar is necessary.
                     */
                    SourceViewer viewer = new SourceViewer(oblWidget, null, SWT.READ_ONLY | SWT.MULTI | SWT.H_SCROLL);
                    viewer.getTextWidget().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
                    viewer.configure(new ObligationSourceViewerConfiguration());
                    viewer.getControl().setFont(JFaceResources.getTextFont());
                    // add the control to the list of controls to be notified when the
                    // text editor font changes.
                    fontListener.addControl(viewer.getControl());

                    // item maps to viewer for later access
                    viewers.put(item, viewer);

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
                    // adding the listener to the item seems to have no effect.
                    item.addListener(SWT.MouseDown, listener);
                    viewer.getTextWidget().addListener(SWT.MouseDown, listener);
                    oblWidget.addListener(SWT.MouseDown, listener);

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

                /*
                 * Get the item's viewer. If the viewer's document does not contain
                 * the obligation string and the obligation string in the marker is not empty,
                 * set the viewer's document to a new document containing
                 * the obligation string.
                 */
                SourceViewer viewer = (SourceViewer) viewers.get(item);
                Assert.isNotNull(viewer, "Expand item has been created without a source viewer. This is a bug.");
                String oblString = marker.getAttribute(ProverHelper.OBLIGATION_STRING, "");
                if ((viewer.getDocument() == null || !viewer.getDocument().get().equals(oblString))
                        && !oblString.isEmpty())
                {
                    // set the viewers document to the obligation.
                    viewer.setDocument(new Document(oblString.trim()));
                    StyledText text = viewer.getTextWidget();

                    /*
                     * Give the item the appropriate height to show
                     * the obligation. This includes both the height
                     * of the text of the obligation and the height
                     * of the horizontal scroll bar, if there is one.
                     */
                    ScrollBar hBar = text.getHorizontalBar();
                    item.setHeight(text.getLineHeight() * text.getLineCount() + (hBar != null ? hBar.getSize().y : 0));
                } else
                {
                    /*
                     * A slight hack. For some interesting obligations, the prover
                     * does not send back the pretty printed obligation. This is
                     * a bug. In the meantime, we need the source viewer to be visible
                     * so that the user can click on it to jump to the obligation.
                     * The following does that.
                     */
                    viewer.setDocument(new Document("No obligation text available."));
                    item.setHeight(100);
                }

            }
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }

    public void setFocus()
    {
        // TODO Auto-generated method stub

    }

    public void dispose()
    {
        JFaceResources.getFontRegistry().removeListener(fontListener);
        super.dispose();
    }

    /**
     * Removes the item from the view, performing necessary
     * cleanup.
     * 
     * @param item
     */
    private void removeItem(ExpandItem item)
    {
        // remove the source viewer's control from the
        // font listener since it no longer needs to be
        // notified of font changes.
        fontListener.removeControl(((SourceViewer) viewers.get(item)).getControl());

        // retrieve the id for the item
        // the id is stored in the item's data, which should be a marker,
        // as set in the updateItem method
        Integer id = new Integer(((IMarker) item.getData()).getAttribute(ProverHelper.OBLIGATION_ID, -1));
        items.remove(id);

        item.getControl().dispose();
        item.dispose();
    }
}
