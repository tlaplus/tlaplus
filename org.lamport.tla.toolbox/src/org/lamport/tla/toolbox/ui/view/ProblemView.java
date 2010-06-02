package org.lamport.tla.toolbox.ui.view;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.ExpandBar;
import org.eclipse.swt.widgets.ExpandItem;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.compare.MarkerComparator;

/**
 * Shows parse problems
 * @version $Id$
 * @author Simon Zambrovski
 */
public class ProblemView extends ViewPart
{
    public static final String ID = "toolbox.view.ProblemView";
    private ExpandBar bar = null;
    public ProblemView()
    {
    }

    /**
     * Creates the layout and fill it with data 
     */
    public void createPartControl(Composite parent)
    {
        bar = new ExpandBar(parent, SWT.V_SCROLL | SWT.BORDER);
        bar.setSpacing(8);
        UIHelper.setHelp(bar, "ProblemView");
        fillData(Activator.getSpecManager().getSpecLoaded());
    }

    /**
     * Fill data
     * @param specLoaded
     */
    private void fillData(Spec specLoaded)
    {
        if (specLoaded == null)
        {
            hide();
            return;
        } else
        {

            // retrieve the markers associated with the loaded spec
            IMarker[] markers = TLAMarkerHelper.getProblemMarkers(specLoaded.getProject(), null);

            if (markers == null || markers.length == 0)
            {
                hide();
            }

            // sort the markers
            List markersList = new ArrayList(Arrays.asList(markers));
            Collections.sort(markersList, new MarkerComparator());

            // Bug fix: 2 June 2010.  It takes forever if
            // there are a large number of markers, which
            // can easily happen if you remove a definition
            // that's used hundreds of times.
            int iterations = Math.min(markers.length, 20);
            for (int j = 0; j < iterations; j++)
            {
                final IMarker problem = (IMarker) markersList.get(j);

                // listener
                Listener listener = new Listener() {
                    // goto marker on click
                    public void handleEvent(Event event)
                    {
                        TLAMarkerHelper.gotoMarker(problem);
                    }
                };

                // contents of the item
                Composite problemItem = new Composite(bar, SWT.LINE_SOLID);
                problemItem.setLayout(new RowLayout(SWT.VERTICAL));
                problemItem.addListener(SWT.MouseDown, listener);

                String[] lines = problem.getAttribute(IMarker.MESSAGE, "").split("\n");
                for (int i = 0; i < lines.length; i++)
                {
                    StyledText styledText = new StyledText(problemItem, SWT.INHERIT_DEFAULT);
                    styledText.setEditable(false);
                    styledText.setCursor(styledText.getDisplay().getSystemCursor(SWT.CURSOR_HAND));
                    styledText.setText(lines[i]);
                    styledText.addListener(SWT.MouseDown, listener);

                    if (isErrorLine(lines[i], problem))
                    {
                        StyleRange range = new StyleRange();
                        range.underline = true;
                        range.foreground = styledText.getDisplay().getSystemColor(SWT.COLOR_RED);
                        range.start = 0;
                        range.length = lines[i].length();
                        styledText.setStyleRange(range);
                    }
                }

                ExpandItem item = new ExpandItem(bar, SWT.NONE, 0);
                item.setExpanded(true);
                
                String markerType = TLAMarkerHelper.getType(problem);
                item.setText(AdapterFactory.getMarkerTypeAsText(markerType) + " " + AdapterFactory.getSeverityAsText(problem.getAttribute(IMarker.SEVERITY,
                        IMarker.SEVERITY_ERROR)));
                item.setHeight(problemItem.computeSize(SWT.DEFAULT, SWT.DEFAULT).y);
                item.setControl(problemItem);
                item.addListener(SWT.MouseDown, listener);
            }
        }
        return ;
    }

    /**
     * 
     */
    public void hide()
    {
        UIHelper.runUIAsync(new Runnable() 
        {
            public void run()
            {
                // UIHelper.closeWindow(ProblemsPerspective.ID);
                getViewSite().getPage().hideView(ProblemView.this);
            }
        });
    }

    private boolean isErrorLine(String line, IMarker marker)
    {
        return line.indexOf("module "
                + marker.getAttribute(TLAMarkerHelper.LOCATION_MODULENAME, TLAMarkerHelper.LOCATION_MODULENAME)) != -1;
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
     */
    public void setFocus()
    {
        bar.setFocus();
    }
}
