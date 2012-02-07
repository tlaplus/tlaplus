package org.lamport.tla.toolbox.tool.tlc.ui.util;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IRegion;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.st.Location;
import util.UniqueString;

public class TLCUIHelper
{

    /**
     * A pattern to match locations reported when an assertion
     * written in PlusCal fails. These locations have the format
     *   
     *   Failure of assertion at line 11, column 2
     *   
     * Group one of the pattern is the begin line, and group two is the begin column.
     */
    public static final Pattern PCAL_LOC_PATTERN = Pattern.compile("line " + "([0-9]+)"/*begin line group*/
            + ", column " + "([0-9]+)"/*begin column group*/);

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
     * When this method is used to create the links, {@link TLCUIHelper#openTLCLocationHyperlink(StyledText, Event, ILaunchConfiguration)}
     * should be used to open the link.
     * 
     * @param styledText
     */
    public static void setTLCLocationHyperlinks(final StyledText styledText)
    {
        final String text = styledText.getText();
        final List<StyleRange> list = setTLCLocationHyperlinks(text);
        for (StyleRange styleRange : list) {
			styledText.setStyleRange(styleRange);
		}
    }
    
    protected static List<StyleRange> setTLCLocationHyperlinks(final String text) {
    	final List<StyleRange> result = new ArrayList<StyleRange>();

    	/*
         * Will be set to the module name
         * of the last location found in the following for
         * loop. This will be used to set the module
         * name for any plus cal assertion failed locations.
         * Those location statements do not contain
         * the module, but it is the same as the module in the
         * error reported by TLC for the failed assertion.
         */
        String pcalModuleName = null;

        /*
         * For each Pattern defined in the Location class, we find
         * all matches of the pattern.
         * 
         * Do not link to locations that are null, equal
         * to nullLoc, or point to the MC or TE modules.
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
                        && !location.source().equals(ModelHelper.MC_MODEL_NAME)
                        && !location.source().equals(ModelHelper.TE_MODEL_NAME))
                {
                    pcalModuleName = location.source();
                    result.add(getHyperlinkStyleRange(location, matcher.start(), matcher.end()));
                }
            }
        }

        /*
         * First we search for any locations that are printed as a result
         * of assertion failure statements where the assertion was
         * written in PlusCal.
         */
        matcher = PCAL_LOC_PATTERN.matcher(text);
        if (matcher.find())
        {
            try
            {
                Assert
                        .isNotNull(pcalModuleName,
                                "Found a plus cal assertion failed location without a TLC error location with the module name.");
                int beginLine = Integer.parseInt(matcher.group(1));
                int beginColumn = Integer.parseInt(matcher.group(2));

                result.add(getHyperlinkStyleRange(new Location(UniqueString
                        .uniqueStringOf(pcalModuleName), beginLine, beginColumn, beginLine, beginColumn), matcher
                        .start(), matcher.end()));
            } catch (NumberFormatException e)
            {
                TLCUIActivator.logError("Error parsing PlusCal assertion failed location.", e);
            }
        }
        return result;
    }

    /**
     * If the trigger corresponds to a point in the styled text that
     * is a link created by {@link TLCUIHelper#setTLCLocationHyperlinks(StyledText)}, then
     * this method jumps to the location in the module corresponding to the link.
     * 
     * Passing in the launch configuration allows this to jump to the location in a saved
     * module, if an editor is open on such a module.
     * 
     * @param styledText
     * @param trigger
     * @param config
     */
    public static void openTLCLocationHyperlink(StyledText styledText, MouseEvent trigger, ILaunchConfiguration config)
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
                    boolean jumpToSavedModule = jumpToSavedLocation((Location) data, config);
                    if (!jumpToSavedModule)
                    {
                        UIHelper.jumpToLocation((Location) data, (trigger.stateMask & SWT.CTRL) != 0);
                    }
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

    /**
     * Creates a hyperlink style range that begins at start and ends at end.
     * Sets the data field of the hyperlink to location.
     * 
     * The data field can be used to jump to the location when the link
     * is opened. Use {@link TLCUIHelper#openTLCLocationHyperlink(StyledText, MouseEvent, ILaunchConfiguration)}
     * to open such links.
     * 
     * @param location
     * @param start
     * @param end
     * @return
     */
    public static StyleRange getHyperlinkStyleRange(Location location, int start, int end)
    {
        /*
         * To create the link, we follow the instructions
         * found here:
         * 
         * https://bugs.eclipse.org/bugs/show_bug.cgi?id=83408
         */
        // create the style for the link
        StyleRange style = new StyleRange(start, end - start, null, null);
        style.underlineStyle = SWT.UNDERLINE_LINK;
        style.underline = true;
        // set the data field of the style range to store the location
        // this can be used for jumping to the location when
        // the hyperlink is opened
        style.data = location;
        return style;
    }

    /**
     * Attempts to jump to the location in a saved version
     * of the module for the given model. It will jump to the location
     * in a nested editor in the model editor for configuration if such
     * a nested editor is already open. If a nested editor is not already
     * open, it will not make the jump and will return false.
     * Returns true if it successfully jumps to the location in the nested
     * editor showing the saved module.
     * 
     * @param location
     * @param configuration
     * @return
     */
    public static boolean jumpToSavedLocation(Location location, ILaunchConfiguration configuration)
    {
        IEditorPart editor = ModelHelper.getEditorWithModelOpened(configuration);
        if (editor instanceof ModelEditor)
        {
            ModelEditor modelEditor = (ModelEditor) editor;

            ITextEditor moduleEditor = modelEditor.getSavedModuleEditor(location.source());

            if (moduleEditor != null)
            {
                try
                {
                    IRegion jumpToRegion = AdapterFactory.locationToRegion(moduleEditor.getDocumentProvider()
                            .getDocument(moduleEditor.getEditorInput()), location);
                    // bring the model editor into focus
                    UIHelper.getActivePage().activate(modelEditor);
                    // set the nested module editor as the active page in the model editor
                    modelEditor.setActiveEditor(moduleEditor);
                    // highlight the appropriate text
                    moduleEditor.selectAndReveal(jumpToRegion.getOffset(), jumpToRegion.getLength());
                    return true;
                } catch (BadLocationException e)
                {
                    TLCUIActivator.logError("Error converting location to region in saved module. The location is "
                            + location, e);
                }
            }
        }
        return false;
    }

}
