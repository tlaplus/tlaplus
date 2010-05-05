package org.lamport.tla.toolbox.tool.tlc.ui.util;

import java.util.regex.Matcher;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.st.Location;

public class TLCUIHelper
{

    /**
     * Registers a control to the context
     * This can only be used within the plug-in org.lamport.tla.toolbox.tool.tlc.ui
     * @param control control to register 
     * @param localContext the context id relative to plug-in ID org.lamport.tla.toolbox.tool.tlc.ui
     * <br>
     * Note: there should be a corresponding context ID defined in the contexts.xml defining the context for current ID. 
     */
    public static void setHelp(Control control, String localContext)
    {
        PlatformUI.getWorkbench().getHelpSystem().setHelp(control, TLCUIActivator.PLUGIN_ID + "." + localContext);
    }

    /**
     * Installs hyperlinks for locations reported by TLC on the {@link StyledText}.
     * This handles both creating the appearance of the hyperlink and storing
     * the module location that should be shown when the link is opened.
     * 
     * When this method is used to create the links, {@link TLCUIHelper#openTLCLocationHyperlink(StyledText, Event)}
     * should be used to open the link.
     * 
     * @param styledText
     */
    public static void setTLCLocationHyperlinks(StyledText styledText)
    {
        String text = styledText.getText();
        /*
         * For each Pattern defined in the Location class, we find
         * all matches of the pattern.
         * 
         * Do not link to locations that are null, equal
         * to nullLoc, or point to the MC module.
         */
        Matcher matcher;
        for (int i = 0; i < Location.ALL_PATTERNS.length; i++)
        {
            matcher = Location.ALL_PATTERNS[i].matcher(text);
            while (matcher.find())
            {
                String locationString = matcher.group();
                Location location = Location.parseLocation(locationString);
                if (location != null && !location.equals(Location.nullLoc)
                        && !location.source().equals(ModelHelper.MC_MODEL_NAME))
                {
                    /*
                     * To create the link, we follow the instructions
                     * found here:
                     * 
                     * https://bugs.eclipse.org/bugs/show_bug.cgi?id=83408
                     */
                    // found a location to link
                    // create the style for the link
                    StyleRange style = new StyleRange(matcher.start(), matcher.end() - matcher.start(), null, null);
                    style.underlineStyle = SWT.UNDERLINE_LINK;
                    style.underline = true;
                    // set the data field of the style range to store the location
                    // this can be used for jumping to the location when
                    // the hyperlink is opened
                    style.data = location;
                    styledText.setStyleRange(style);
                }
            }
        }
    }

    /**
     * If the trigger corresponds to a location in the styled text that
     * is a link created by {@link TLCUIHelper#setTLCLocationHyperlinks(StyledText)}, then
     * this method jumps to the location in the module corresponding to the link.
     * 
     * @param styledText
     * @param trigger
     */
    public static void openTLCLocationHyperlink(StyledText styledText, MouseEvent trigger)
    {
        try
        {
            int offset = styledText.getOffsetAtLocation(new Point(trigger.x, trigger.y));
            StyleRange range = styledText.getStyleRangeAtOffset(offset);
            if (range != null)
            {
                Object data = range.data;
                if (data instanceof Location)
                {
                    UIHelper.jumpToLocation((Location) data);
                }
            }
        } catch (IllegalArgumentException e)
        {
            /*
             * This type of exception can occur if the mouse event does
             * not correspond to an area of text in the styled text widget.
             * In this case, just do nothing.
             */
        }
    }

}
