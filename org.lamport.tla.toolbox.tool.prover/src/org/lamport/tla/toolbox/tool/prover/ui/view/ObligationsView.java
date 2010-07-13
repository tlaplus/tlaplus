package org.lamport.tla.toolbox.tool.prover.ui.view;

import java.util.HashMap;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.ExpandBar;
import org.eclipse.swt.widgets.ExpandItem;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ObligationStatus;
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
 * obligation.
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
 * The methods {@link #refreshObligationView()} and {@link #updateObligationView(IMarker)} ensure that when the
 * obligation view is empty, it is hidden. The only way to open an empty obligation view is to select the menu item
 * opening the view.
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
    private Listener obClickListener = new Listener() {

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

    /**
     * A listener for the stop obligation button for an obligation.
     * This sends a signal to the prover indicating that the proving
     * of that obligation should stop.
     */
    private SelectionListener stopObListener = new SelectionAdapter() {
        public void widgetSelected(SelectionEvent e)
        {
            if (e.widget instanceof Button && e.widget.getData() instanceof IMarker)
            {
                ProverHelper.stopObligation((IMarker) e.widget.getData());
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
     * 2.) Retrieve all obligation statuses by calling {@link ProverHelper#getObligationStatuses()}.
     *     Fills the view with information from these statuses.
     * 
     * 3.) If there are no interesting obligations in the view after steps 1 and 2, then
     * the view is hidden.
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
                oblView.removeItem((InterestingObligationExpandItem) expandItems[i]);
            }

            /*
             * Fill the obligation view with markers from the current spec.
             * If the obligations view is empty after doing this (there are
             * no interesting obligations) then hide the view.
             */
            oblView.fillFromCurrentSpec();

            if (oblView.isEmpty())
            {
                UIHelper.getActivePage().hideView(oblView);
            }

        }

    }

    /**
     * Fills the obligation view with information
     * from the most recent launch of the prover.
     */
    private void fillFromCurrentSpec()
    {
        ObligationStatus[] statuses = ProverHelper.getObligationStatuses();
        if (statuses != null)
        {
            for (int i = 0; i < statuses.length; i++)
            {
                updateItem(statuses[i]);
            }

        }

    }

    /**
     * Updates the view with the information in this obligation status message.
     * 
     * This method hides the view if after updating the item, the view is empty (there are no
     * more interesting obligations).
     * 
     * Must be run from the UI thread.
     * 
     * @param marker
     */
    public static void updateObligationView(ObligationStatus status)
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
        if (!ProverHelper.isInterestingObligation(status))
        {
            oblView = (ObligationsView) UIHelper.findView(VIEW_ID);
        } else
        {
            oblView = (ObligationsView) UIHelper.openView(VIEW_ID);
        }

        if (oblView != null)
        {

            String moduleName = status.getObMarker().getResource().getName();
            if (!oblView.getPartName().equals(PART_NAME_BASE + moduleName))
            {
                oblView.setPartName(PART_NAME_BASE + moduleName);
            }

            oblView.updateItem(status);

            /*
             * If after updating the item, the obligations view is empty, it should be hidden.
             */
            if (oblView.isEmpty())
            {
                UIHelper.getActivePage().hideView(oblView);
            }

        }

    }

    /**
     * Adds the information from the obligation status to the view.
     * 
     * If there is already an item with information of the same
     * obligation as the status, that item is updated. If no
     * such item exists, a new one is created.
     */
    private void updateItem(ObligationStatus status)
    {
        int id = status.getId();
        if (id != -1)
        {
            /*
             * Try to retrieve an existing item with the same id.
             */
            InterestingObligationExpandItem item = (InterestingObligationExpandItem) items.get(new Integer(id));

            /*
             * If the marker represents an obligation that is
             * not interesting, we dispose of the existing item
             * (if there is one) and then return. There is nothing
             * more to do.
             */
            if (!ProverHelper.isInterestingObligation(status))
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
                item = new InterestingObligationExpandItem(bar, SWT.None, 0, id);
                ;

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
                 * Add a button for stopping the obligation. This button is
                 * later disabled if the obligation is not being proved.
                 * 
                 * The data field for the button stores a pointer to the
                 * marker for the obligation. This allows a listener
                 * to retrieve the id of the obligation, or any other information
                 * which it must send to the prover to stop the proof.
                 */
                Button stopButton = new Button(oblWidget, SWT.PUSH);
                stopButton.setText("Stop Proving");
                stopButton.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
                stopButton.setData(status.getObMarker());
                stopButton.addSelectionListener(stopObListener);
                item.setButton(stopButton);

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
                item.setData(status.getObMarker());
                viewer.getTextWidget().setData(status.getObMarker());
                oblWidget.setData(status.getObMarker());
                // adding the listener to the item seems to have no effect.
                item.addListener(SWT.MouseDown, obClickListener);
                viewer.getTextWidget().addListener(SWT.MouseDown, obClickListener);
                oblWidget.addListener(SWT.MouseDown, obClickListener);

                items.put(new Integer(id), item);
            }

            /*
             * Whether this marker gives information for an existing
             * item or a new item, we always update the title of the
             * item to display the current status of the obligation.
             */
            item.setText("Obligation " + id + " - status : " + status.getProverStatusString());

            /*
             * Enable the "Being Proved" button iff the obligation is being proved.
             */
            item.getButton().setEnabled(ProverHelper.isBeingProvedObligation(status));

            /*
             * Get the item's viewer. If the viewer's document does not contain
             * the obligation string and the obligation string in the marker is not empty,
             * set the viewer's document to a new document containing
             * the obligation string.
             */
            SourceViewer viewer = (SourceViewer) viewers.get(item);
            Assert.isNotNull(viewer, "Expand item has been created without a source viewer. This is a bug.");
            String oblString = status.getObligationString();
            if ((viewer.getDocument() == null || !viewer.getDocument().get().equals(oblString)) && !oblString.isEmpty())
            {
                // set the viewers document to the obligation.
                viewer.setDocument(new Document(oblString.trim()));

                /*
                 * The following explanation for computing the height
                 * of each expand item is no longer used. Instead, we
                 * simply ask the expand item's control for its preferred height.
                 * This seems to work. However, we leave the old code and comments
                 * just in case.
                 * 
                 * Give the item the appropriate height to show
                 * the obligation. This includes both the height
                 * of the text of the obligation and the height
                 * of the horizontal scroll bar, if there is one.
                 */
                // StyledText text = viewer.getTextWidget();
                // ScrollBar hBar = text.getHorizontalBar();
                // item.setHeight(text.getLineHeight() * text.getLineCount() + (hBar != null ? hBar.getSize().y :
                // 0));
                item.setHeight(item.getControl().computeSize(SWT.DEFAULT, SWT.DEFAULT, true).y);
            } else if (oblString.isEmpty() && (viewer.getDocument() == null || viewer.getDocument().get().isEmpty()))
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

    }

    private boolean isEmpty()
    {
        return bar.getItemCount() == 0;
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
    private void removeItem(InterestingObligationExpandItem item)
    {
        // remove the source viewer's control from the
        // font listener since it no longer needs to be
        // notified of font changes.
        fontListener.removeControl(((SourceViewer) viewers.get(item)).getControl());

        // retrieve the id for the item
        // the id is stored in the item's data, which should be a marker,
        // as set in the updateItem method
        items.remove(new Integer(item.getId()));

        item.getControl().dispose();
        item.dispose();
    }

    /**
     * A subclass of ExpandItem that contains a Button.  Used so that
     * the "Stop Proving" button can be disabled for an interesting
     * obligation that is not being proved.
     * 
     * @author lamport
     *
     */
    public static class InterestingObligationExpandItem extends ExpandItem
    {
        /**
         * The obligation id.
         */
        private int id;

        /**
         * Returns the id of the obligation.
         * 
         * @return
         */
        public int getId()
        {
            return id;
        }

        private Button button;

        public Button getButton()
        {
            return button;
        }

        public void setButton(Button button)
        {
            this.button = button;
        }

        // public InterestingObligationExpandItem(ExpandBar parent, int style)
        // {
        // super(parent, style);
        // // Auto-generated constructor stub
        // }

        /**
         * Creates an expand bar item for the obligation with the given id. The parent style
         * and index are the arguments used for the constructor {@link ExpandItem#ExpandItem(ExpandBar, int, int)}.
         */
        public InterestingObligationExpandItem(ExpandBar parent, int style, int index, int id)
        {
            super(parent, style, index);
            // Auto-generated constructor stub
            this.id = id;
        }
    }
}
