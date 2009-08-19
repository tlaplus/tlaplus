package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.ExpandBar;
import org.eclipse.swt.widgets.ExpandItem;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCError;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCErrorView extends ViewPart
{
    public static final String ID = "toolbox.tool.tlc.view.TLCErrorView";
    private ExpandBar bar = null;

    
    /**
     * Creates the layout and fill it with data 
     */
    public void createPartControl(Composite parent)
    {
        bar = new ExpandBar(parent, SWT.V_SCROLL | SWT.BORDER);
        bar.setSpacing(8);
        UIHelper.setHelp(bar, "TLCErrorView");
    }

    /**
     * Fill data
     * @param specLoaded
     */
    public void fillData(List problems)
    {
        if (problems == null || problems.isEmpty())
        {
            hide();
            return;
        } else
        {

            for (int j = 0; j < problems.size(); j++)
            {
                final TLCError problem = (TLCError) problems.get(j);

//                // listener
//                Listener listener = new Listener() {
//                    // goto marker on click
//                    public void handleEvent(Event event)
//                    {
//                        TLAMarkerHelper.gotoMarker(problem);
//                    }
//                };

                // contents of the item
                Composite problemItem = new Composite(bar, SWT.LINE_SOLID);
                problemItem.setLayout(new RowLayout(SWT.VERTICAL));
                
                // problemItem.addListener(SWT.MouseDown, listener);

                String[] lines = problem.getMessage().split("\n");
                for (int i = 0; i < lines.length; i++)
                {
                    StyledText styledText = new StyledText(problemItem, SWT.INHERIT_DEFAULT);
                    styledText.setEditable(false);
                    styledText.setCursor(styledText.getDisplay().getSystemCursor(SWT.CURSOR_HAND));
                    styledText.setText(lines[i]);
                    
                    // styledText.addListener(SWT.MouseDown, listener);

//                    if (isErrorLine(lines[i], problem))
//                    {
//                        StyleRange range = new StyleRange();
//                        range.underline = true;
//                        range.foreground = styledText.getDisplay().getSystemColor(SWT.COLOR_RED);
//                        range.start = 0;
//                        range.length = lines[i].length();
//                        styledText.setStyleRange(range);
//                    }
                }

                ExpandItem item = new ExpandItem(bar, SWT.NONE, 0);
                item.setExpanded(true);
                
                // String markerType = TLAMarkerHelper.getType(problem);
                item.setText("Error ");
                item.setHeight(problemItem.computeSize(SWT.DEFAULT, SWT.DEFAULT).y);
                item.setControl(problemItem);
                
                // item.addListener(SWT.MouseDown, listener);
            }
        }
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
                getViewSite().getPage().hideView(TLCErrorView.this);
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
