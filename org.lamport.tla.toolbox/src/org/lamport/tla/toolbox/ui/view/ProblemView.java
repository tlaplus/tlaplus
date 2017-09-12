package org.lamport.tla.toolbox.ui.view;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.e4.core.services.events.IEventBroker;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.ExpandBar;
import org.eclipse.swt.widgets.ExpandItem;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.TLAUnicodeReplacer;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.compare.MarkerComparator;
import org.osgi.service.event.EventHandler;

import tla2unicode.Unicode;

/**
 * Shows parse problems
 * @version $Id$
 * @author Simon Zambrovski
 */
public class ProblemView extends ViewPart
{
    public static final String ID = "toolbox.view.ProblemView";
    private ExpandBar bar = null;
    private EventHandler eventHandler;

	/**
     * Creates the layout and fill it with data 
     */
    public void createPartControl(Composite parent)
    {
        bar = new ExpandBar(parent, SWT.V_SCROLL | SWT.BORDER);
        bar.setSpacing(8);
        UIHelper.setHelp(bar, "ProblemView");
        fillData(Activator.getSpecManager().getSpecLoaded());
        UIHelper.getEventBroker().subscribe(TLAUnicodeReplacer.EVENTID_TOGGLE_UNICODE, getEventHandler());
    }
    
	private synchronized EventHandler getEventHandler() {
		if (eventHandler == null) {
			this.eventHandler = new EventHandler() {
				@Override
				public void handleEvent(org.osgi.service.event.Event event) {
					if (event == null)
						return;
					final Object value = event.getProperty(IEventBroker.DATA);
					switch (event.getTopic()) {
					case TLAUnicodeReplacer.EVENTID_TOGGLE_UNICODE:
						unicodeToggleHandler((Boolean)value);
						break;
					default:		
					}
				}
			};
		}
		return eventHandler;
	}

    @Override
	public void dispose() {
    	UIHelper.getEventBroker().unsubscribe(eventHandler);
		super.dispose();
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
            List<IMarker> markersList = new ArrayList<IMarker>(Arrays.asList(markers));
            Collections.sort(markersList, new MarkerComparator());

            // Bug fix: 2 June 2010.  It takes forever if
            // there are a large number of markers, which
            // can easily happen if you remove a definition
            // that's used hundreds of times.
            int iterations = Math.min(markers.length, 20);
            for (int j = 0; j < iterations; j++)
            {
                final IMarker problem = markersList.get(j);

                // listener
                Listener listener = new Listener() {
                    // goto marker on click
                    public void handleEvent(Event event)
                    {
                        TLAMarkerHelper.gotoMarker(problem, ((event.stateMask & SWT.CTRL) != 0));
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
                    styledText.setText(Unicode.convert(TLAUnicodeReplacer.isUnicode(), lines[i]));
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
	
    private void unicodeToggleHandler(boolean unicode) {
		for (Control c1 : bar.getChildren()) {
			if (c1 instanceof Composite) {
				Composite problemItem = (Composite)c1;
				for (Control c2 : problemItem.getChildren()) {
					if (c2 instanceof StyledText) {
						StyledText styledText = (StyledText)c2;
						styledText.setText(Unicode.convert(TLAUnicodeReplacer.isUnicode(), styledText.getText()));
					}
				}
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
