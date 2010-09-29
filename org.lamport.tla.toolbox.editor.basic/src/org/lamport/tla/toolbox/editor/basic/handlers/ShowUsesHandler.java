package org.lamport.tla.toolbox.editor.basic.handlers;

import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.PopupDialog;
import org.eclipse.jface.text.IRegion;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.tla.TokenSpec;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;
import tla2sany.st.SyntaxTreeConstants;

/**
 * 
 */

/**
 * This is the handler for the Show Uses command, which allows the user
 * to mark and visit all uses of a symbol.  However, unlike the Show
 * Declaration command, for an instantiated symbol like Foo!bar, it 
 * shows only uses of Foo!bar, not other uses of the original symbol
 * bar.
 * 
 * If the chosen symbol is used in more than one module (possible only
 * by EXTENDing a module with its declaration or by INSTANCEing it
 * with no renaming or parameter substitution), then a pop-up dialog
 * allows the user to choose which module to display.
 * 
 * Note: Implementing SyntaxTreeConstants simply imports the definitions
 *       of the constants defined in that interface.
 *       
 * Note: See roadmap.txt for how to get the markers to show on the right-hand
 *       vertical bar.
 * 
 * @author lamport
 *
 */
public class ShowUsesHandler extends AbstractHandler implements IHandler, SyntaxTreeConstants
{
    /**    This is the handler for the Goto Next Use command.
     * 
     * @author lamport
     *
     */

    public static String titleText(String prefix)
    {
        if (prefix == "")
        {
            return "Definitions and Declarations";
        } else
        {
            return prefix;
        }

    }

    /**
     * This class defines the pop-up dialog that allows the user
     * to choose which module's uses to show.
     * 
     * The code was copied from the ShowDeclarationsPopupDialog
     * subclass of ShowDeclarationsHandler.
     * 
     * @author lamport
     *
     */
    public static class ShowUsesPopupDialog extends PopupDialog
    {
        Shell parent; // The dialog's parent shell

        /**
         * moduleList is the list of all modules from which the user chooses.
         * 
         * showUses[i] is an array of all uses in module moduleList[i].
         */
        String[] moduleList;
        SemanticNode[][] showUses;

        List list; // The org.eclipse.swt.widgets.List (not ordinary Java List) being displayed.
        boolean showAll = true; // True iff displaying definitions imported by instantiation.
        String filterPrefix = ""; // For filtering displayed declarations as user types prefix.

        /*
         * The TLA editor with focus and the module it's open on.  They are saved because the editor
         * no longer has focus when the popup dialog is raised.
         */
        TLAEditor editor;
        ModuleNode module;

        public ShowUsesPopupDialog(Shell parent, String[] moduleList, SemanticNode[][] usesArray)
        {
            super(parent, SWT.NO_TRIM, true, // takeFocusOnOpen
                    false, // persistSize
                    true, // persistLocation
                    true, // showDialogMenu
                    true, // showPersistActions
                    "Choose Module", // titleText
                    "Click or choose by typing prefix or arrow keys and enter."); // infoText
            this.parent = parent;
            this.moduleList = moduleList;
            this.showUses = usesArray;
            this.editor = EditorUtil.getTLAEditorWithFocus();
            if (this.editor != null)
            {
                module = ResourceHelper.getModuleNode(editor.getModuleName());
            }
        }

        /**
         * This is the method that puts the content into the popup's
         * dialog area.  It puts an org.eclipse.swt.widgets.List
         * (note that this isn't an ordinary Java List) there.
         * 
         * This is identical to the corresponding method in 
         * ShowDeclarationsHandler except for the obvious name changes
         * and the different setList method.  See that method
         * for the comments.
         * 
         */
        protected Control createDialogArea(Composite composite)
        {
            list = new List(composite, SWT.SINGLE | SWT.V_SCROLL | SWT.RESIZE);
            setList();
            list.addSelectionListener(new ShowUsesSelectionListener(this.showUses, this.moduleList)); // EditorUtil.getTLAEditorWithFocus()));
            list.addKeyListener(new ShowUsesKeyListener(this)); // Testing
            list.setSelection(0);
            return list;
        }

        /**
         * This is just to make setTitleText a public method so the handlers
         * can call it.
         */
        public void setTitleText(String str)
        {
            super.setTitleText(str);
        }

        protected void setList()
        {
            list.removeAll();
            for (int i = 0; i < moduleList.length; i++)
            {
                if (moduleList[i].startsWith(filterPrefix))
                {
                    list.add(moduleList[i]);
                }
            }
        }
    }

    /**
     * A listener for the List put into the dialog by the createDialogArea
     * method of ShowDefinitionsPopupDialog.
     * 
     * @author lamport
     *
     */
    public static class ShowUsesSelectionListener implements SelectionListener
    {
        // Copies of the arrays from ShowUsesHandler
        SemanticNode[][] showUses;
        String[] moduleNames;

        public ShowUsesSelectionListener(SemanticNode[][] showUses2, String[] moduleNames) // TLAEditor editor)
        {
            super();
            this.showUses = showUses2;
            this.moduleNames = moduleNames;
        }

        /**
         * This method seems to be called on the second click
         * when double-clicking on the selection.  Or maybe not.
         */
        public void widgetDefaultSelected(SelectionEvent e)
        {
        }

        /**
         * Called when the user selects an item in the List.
         */
        public void widgetSelected(SelectionEvent e)
        {
            List list = ((List) e.widget);
            Spec spec = ToolboxHandle.getCurrentSpec();
            if (spec != null)
            {
                spec.setModuleToShow(list.getSelection()[0]);

                String moduleName = list.getSelection()[0];
                spec.setModuleToShow(list.getSelection()[0]);
                int idx = selectString(moduleNames, moduleName);
                if (idx != -1)
                {
                    setUseMarkers(showUses[idx], moduleName, spec);
                }

            }
        }
    }

    /**
     * The Key Listener for keyboard input to the popup dialog.  The following
     * kinds of keyboard input are handled:
     * <ul>
     * <li> Return, which is equivalent to clicking on the selected item.
     * <li> Space, which toggles between showing and hiding instantiated declarations.
     * <li> Arrow keys, which move the selection.
     * <li> Letters, numbers, "_", and "!", which are added to the prefix used for
     *      filtering what is shown.
     * <li> Delete/backspace, which deletes one character from the filtering prefix.
     * </ul>
     * Other typed input is ignored.
     * @author lamport
     *
     */
    public static class ShowUsesKeyListener implements KeyListener
    { // Shell parent;
        ShowUsesPopupDialog popup;

        // boolean showAll; // a local copy of the current specs' showAllDeclarations field.

        public ShowUsesKeyListener(ShowUsesPopupDialog popup)
        { // this.parent = parent;
            this.popup = popup;
        }

        public void keyPressed(KeyEvent e)
        {
            char keyPressed = e.character;
            int keyCode = e.keyCode;
            List list = popup.list;
            int selection = list.getSelectionIndex();

            // This prevents the KeyEvent from changing the selection and triggering
            // execution of the SelectionListener.
            e.doit = false;

            // Check which key was pressed and handle it appropriately.
            if (keyCode == SWT.ARROW_DOWN || keyCode == SWT.ARROW_RIGHT)
            {
                if (list.getItemCount() == 0 || selection == -1)
                {
                    return;
                }
                list.select(Math.min(list.getItemCount(), selection + 1));
            } else if (keyCode == SWT.ARROW_UP || keyCode == SWT.ARROW_LEFT)
            {
                if (list.getItemCount() == 0 || selection == -1)
                {
                    return;
                }
                list.select(Math.max(0, selection - 1));
            } else if (keyCode == SWT.CR || keyCode == SWT.KEYPAD_CR)
            {
                Spec spec = ToolboxHandle.getCurrentSpec();
                if (spec != null)
                {
                    String moduleName = list.getSelection()[0];
                    spec.setModuleToShow(list.getSelection()[0]);
                    int idx = selectString(popup.moduleList, moduleName);
                    if (idx != -1)
                    {
                        setUseMarkers(popup.showUses[idx], moduleName, spec);
                    }
                }
                ;
                popup.close();
            } else if (Character.isLetterOrDigit(keyPressed) || (keyPressed == '_') || (keyPressed == '!'))
            {
                popup.filterPrefix = popup.filterPrefix + keyPressed;
                popup.setList();
                popup.setTitleText(ShowUsesHandler.titleText(popup.filterPrefix));
                // popup.setInfoText(ShowUsesHandler.infoText(popup.showAll));
                if (list.getItemCount() > 0)
                {
                    list.select(0);
                }

            } else if ((keyCode == SWT.DEL || keyCode == SWT.BS) && !popup.filterPrefix.equals(""))
            {
                popup.filterPrefix = popup.filterPrefix.substring(0, popup.filterPrefix.length() - 1);
                popup.setList();
                popup.setTitleText(ShowUsesHandler.titleText(popup.filterPrefix));
                // popup.setInfoText(ShowUsesHandler.infoText(popup.showAll));
                if (list.getItemCount() > 0)
                {
                    list.select(0);
                }
            }
        }

        public void keyReleased(KeyEvent e)
        {
            // TODO Auto-generated method stub

        }

    }

    public static final String SHOW_USE_MARKER_TYPE = "org.lamport.tla.toolbox.editor.basic.showUse";

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // We need the current spec for accessing the fields
        // that the Show Uses command and the Goto Next/Previous Use commands need.
        // If there is no spec, there's nothing we can do.
        Spec spec = ToolboxHandle.getCurrentSpec();
        if (spec == null)
        {
            return null;
        }

        // Delete any existing markers.
        // Get the resource on which markers are to go, and set the markers.
        String oldModuleName = spec.getModuleToShow();
        if (oldModuleName != null)
        {
            IResource resource = ResourceHelper.getResourceByModuleName(oldModuleName);
            if (resource != null)
            {
                try
                {
                    resource.deleteMarkers(SHOW_USE_MARKER_TYPE, false, 99);
                } catch (CoreException e)
                {
                    // This should not happen;
                    e.printStackTrace();
                }
                spec.setMarkersToShow(null);
            }
        }

        // We will need the module name, which we get from the editor.
        TLAEditor tlaEditor = EditorUtil.getTLAEditorWithFocus();
        if (tlaEditor == null)
        {
            return null;
        }
        String moduleName = tlaEditor.getModuleName();
        ModuleNode moduleNode = ResourceHelper.getModuleNode(moduleName);
        if (moduleNode == null)
        {
            return null;
        }

        // We now get the SymbolNode that is the definition or declaration
        // of the symbol at which the TLA Editor's cursor is.
        TokenSpec currentTokenSpec = TokenSpec.findCurrentTokenSpec();
        if (currentTokenSpec == null || currentTokenSpec.resolvedSymbol == null)
        {
            return null;
        }
        SymbolNode resolvedSymbol = currentTokenSpec.resolvedSymbol;

        // System.out.println("We found symbol node named " + resolvedSymbol.getName());

        // Set tempModuleNames to the sorted array of all user module names.
        String[] tempModuleNames = ResourceHelper.getModuleNames();

        // Set tempUsesArray[i] to the array of OpAplNode[] nodes at are uses of
        // resolvedSymbol in module moduleNames[i], and sets numberOfModulesUsedIn
        // to the number of values of i for which usesArray[i] is neither null
        // nor a zero-length array.
        int numberOfModulesUsedIn = 0;
        SemanticNode[][] tempUsesArray = new SemanticNode[tempModuleNames.length][];
        for (int i = 0; i < tempModuleNames.length; i++)
        {
            tempUsesArray[i] = ResourceHelper.getUsesOfSymbol(resolvedSymbol, ResourceHelper
                    .getModuleNode(tempModuleNames[i]));
            if ((tempUsesArray[i] != null) && (tempUsesArray[i].length > 0))
            {
                numberOfModulesUsedIn++;
            }
        }

        // Raise an error menu if there are no instances.
        if (numberOfModulesUsedIn == 0)
        {
            MessageDialog.openWarning(UIHelper.getShellProvider().getShell(), "Cannot find uses",
                    "There are no uses of the symbol " + resolvedSymbol.getName());
            return null;
        }

        // Set usesArray and moduleNames to the subarrays of of tempUsesArray and
        // tempModuleNames for which there are instances of the symbols, with the
        // currently selected module's name put first if it is one of them.
        SemanticNode[][] usesArray = new SemanticNode[numberOfModulesUsedIn][];
        String[] moduleNames = new String[numberOfModulesUsedIn];
        int j = 0;
        for (int i = 0; i < tempModuleNames.length; i++)
        {
            if ((tempUsesArray[i] != null) && (tempUsesArray[i].length > 0))
            {
                usesArray[j] = tempUsesArray[i];
                moduleNames[j] = tempModuleNames[i];
                j++;
            }
        }
        j = -1;
        for (int i = 0; i < moduleNames.length; i++)
        {
            if (moduleName.equals(moduleNames[i]))
            {
                j = i;
                break;
            }
        }
        if (j > 0)
        {
            SemanticNode[] savedUses = usesArray[j];
            for (int i = j - 1; i > -1; i--)
            {
                usesArray[i + 1] = usesArray[i];
                moduleNames[i + 1] = moduleNames[i];
            }
            usesArray[0] = savedUses;
            moduleNames[0] = moduleName;
        }

        // If there are uses in more than one module, have the user choose
        // which one
        String moduleToShow = null;
        if (moduleNames.length > 1)
        {
            Shell parent = UIHelper.getShellProvider().getShell();
            ShowUsesPopupDialog popup = new ShowUsesPopupDialog(parent, moduleNames, usesArray);
            popup.open();
        } else
        {
            moduleToShow = moduleName;

            spec.setModuleToShow(moduleToShow);

            int moduleIndex = -1;
            for (int i = 0; i < moduleNames.length; i++)
            {
                if (moduleNames[i].equals(moduleToShow))
                {
                    moduleIndex = i;
                    break;
                }
            }
            if (moduleIndex < 0)
            {
                Activator.logDebug("Could not find module name in array in which it should be.  " + "This is a bug.");
                return null;
            }

            // Set locations to the array of Locations of the uses. To do this, we
            // look at the OpApplNode's syntax node tree and check for the following cases:
            // Foo(...) : the node is an N_OpApplication node, it's
            // first child is an N_GeneralID whose location is good.
            // ... %% ... : the node is an N_InfixExpr node, whose 2nd child is
            // an N_GenInfixOp whose location is good.
            // x : the node is an N_GeneralID node whose location is good
            // ...^+ : the node is an N_PostfixExpr node whose second heir
            // is an N_GeneralPostfixOp whose location is good
            SemanticNode[] uses = usesArray[moduleIndex];
            setUseMarkers(uses, moduleName, spec);
        }
        // Location[] locations = new Location[uses.length];
        // for (int i = 0; i < locations.length; i++)
        // {
        // // Set stn to the syntax tree node whose location should
        // // be used.
        // SyntaxTreeNode stn = (SyntaxTreeNode) uses[i].stn;
        // switch (stn.getKind()) {
        // case N_OpApplication:
        // stn = (SyntaxTreeNode) stn.heirs()[0];
        // break;
        // case N_InfixExpr:
        // case N_PostfixExpr:
        // stn = (SyntaxTreeNode) stn.heirs()[1];
        // break;
        // default:
        // System.out.println("Found unexpected kind " + stn.getKind() + " for stn node of symbol use.");
        // }
        // locations[i] = stn.getLocation();
        // }
        // Arrays.sort(locations, new LocationComparator());
        //
        // // Jump to the first location. This ensures that the module is
        // // now displayed by the current editor. (At least, I hope this
        // // happens synchronously.)
        // UIHelper.jumpToLocation(locations[0]);
        // spec.setCurrentSelection(0);
        //
        // // Get the resource on which markers are to go, and set the markers.
        // IResource resource = ResourceHelper.getResourceByModuleName(spec.getModuleToShow());
        // if (resource == null)
        // {
        // System.out.println("Why the hell is the resource null?");
        // return null;
        // }
        //
        // try
        // {
        // // Remove all markers showing uses.
        // resource.deleteMarkers(SHOW_USE_MARKER_TYPE, false, 99);
        // spec.setMarkersToShow(null);
        //
        // IMarker[] markersToShow = new IMarker[locations.length];
        //
        // // create the markers and put them in this.markersToShow
        // for (int i = 0; i < markersToShow.length; i++)
        // {
        // // The following is inefficient, because it's doing the same
        // // computation each time to find the document from the
        // // location.
        // IRegion iregion = AdapterFactory.locationToRegion(locations[i]);
        // IMarker marker;
        // marker = resource.createMarker(SHOW_USE_MARKER_TYPE);
        // Map markerAttributes = new HashMap(2);
        // markerAttributes.put(IMarker.CHAR_START, new Integer(iregion.getOffset()));
        // markerAttributes.put(IMarker.CHAR_END, new Integer(iregion.getOffset() + iregion.getLength()));
        // marker.setAttributes(markerAttributes);
        // markersToShow[i] = marker;
        // }
        // spec.setMarkersToShow(markersToShow);
        // } catch (CoreException e)
        // {
        // // TODO Auto-generated catch block
        // e.printStackTrace();
        // }

        return null;
    }

    /**
     * TODO: This method has the following minor bug.  When Foo is defined in module
     * M, which is instantiated by  I == INSTANCE M, then when one of the OpApplNodes
     * in uses represents a subexpression name like I!Foo!2, then just the "I" rather
     * than the "I!Foo" is marked.  This is pretty harmless and is probably not worth
     * fixing.
     * 
     * @param uses
     * @param moduleName
     * @param spec
     */
    private static void setUseMarkers(SemanticNode[] uses, String moduleName, Spec spec)
    {
        Location[] locations = new Location[uses.length];
        for (int i = 0; i < locations.length; i++)
        {
            // Set stn to the syntax tree node whose location should
            // be used.
            SyntaxTreeNode stn = (SyntaxTreeNode) uses[i].stn;
            switch (stn.getKind()) {
            case N_OpApplication:
                stn = (SyntaxTreeNode) stn.heirs()[0];
                break;
            case N_InfixExpr:
            case N_PostfixExpr:
                stn = (SyntaxTreeNode) stn.heirs()[1];
                break;
            case N_GeneralId:
                // Following code added by LL on 14 Sep 2010 as part of fix
                // for handling uses of a defined symbol in a subexpression name.
                // For a use of Foo in a subexpression name like Foo!..., the
                // OpApplNode uses[i] will have as its subExpressionOf field
                // non-null and a SyntaxTreeNode representing a tree whose
                // left-most leaf SyntaxTreeNode is a syntactic element
                // representing "Foo". We recognize this SyntaxTreeNode because
                // if has a kind representing a syntactic element, which means
                // a kind less than NULL_ID.
                // Following code modified by LL on 17 Sep 2010 by adding second
                // conjunct of `if' test. It appears that, if an OpApplNode represents
                // the application of a defined operator, and not a subexpression name,
                // then its subExpression field equals (==) its operator field, rather
                // than being null.
                if (uses[i] instanceof OpApplNode)
                {
                    OpApplNode oan = (OpApplNode) uses[i];
                    if (oan.subExpressionOf != null && oan.subExpressionOf != oan.getOperator())
                    {
                        while (stn.getKind() > NULL_ID && stn.heirs() != null && stn.heirs().length > 0)
                        {
                            stn = (SyntaxTreeNode) stn.heirs()[0];
                        }
                    }
                }
                break;
            default:
                System.out.println("Found unexpected kind " + stn.getKind() + " for stn node of symbol use.");
            }
            locations[i] = stn.getLocation();
        }
        Arrays.sort(locations, new LocationComparator());

        // Jump to the first location. This ensures that the module is
        // now displayed by the current editor. (At least, I hope this
        // happens synchronously.)
        UIHelper.jumpToLocation(locations[0]);
        spec.setCurrentSelection(0);

        // Get the resource on which markers are to go, and set the markers.
        IResource resource = ResourceHelper.getResourceByModuleName(spec.getModuleToShow());
        if (resource == null)
        {
            System.out.println("Why is the resource null?");
            return;
        }

        try
        {
            // Remove all markers showing uses.
            resource.deleteMarkers(SHOW_USE_MARKER_TYPE, false, 99);
            spec.setMarkersToShow(null);

            IMarker[] markersToShow = new IMarker[locations.length];

            // create the markers and put them in this.markersToShow
            for (int i = 0; i < markersToShow.length; i++)
            {
                // The following is inefficient, because it's doing the same
                // computation each time to find the document from the
                // location.
                IRegion iregion = AdapterFactory.locationToRegion(locations[i]);
                IMarker marker;
                marker = resource.createMarker(SHOW_USE_MARKER_TYPE);
                Map markerAttributes = new HashMap(2);
                markerAttributes.put(IMarker.CHAR_START, new Integer(iregion.getOffset()));
                markerAttributes.put(IMarker.CHAR_END, new Integer(iregion.getOffset() + iregion.getLength()));
                marker.setAttributes(markerAttributes);
                markersToShow[i] = marker;
            }
            spec.setMarkersToShow(markersToShow);
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }

    /**
     * If strArray[i] equals str, then return i (for the smallest
     * such i); otherwise return -1;
     * 
     * @param strArray
     * @param str
     * @return
     */
    private static int selectString(String[] strArray, String str)
    {
        for (int i = 0; i < strArray.length; i++)
        {
            if (strArray[i].equals(str))
            {
                return i;
            }
        }
        return -1;
    }

    /**
     * A comparator to compare two locations.  It must only be used
     * to compare Location objects.
     * @author lamport
     *
     */
    private static class LocationComparator implements Comparator
    {
        public int compare(Object arg0, Object arg1)
        {
            // Most of this code is a clone from SemanticNode.compareTo
            Location loc1 = (Location) arg0;
            Location loc2 = (Location) arg1;
            if (loc1.beginLine() < loc2.beginLine())
            {
                return -1;
            }
            if (loc1.beginLine() > loc2.beginLine())
            {
                return 1;
            }
            if (loc1.beginColumn() == loc2.beginColumn())
            {
                return 0;
            }
            return (loc1.beginColumn() < loc2.beginColumn()) ? -1 : 1;
        }

    }

}
