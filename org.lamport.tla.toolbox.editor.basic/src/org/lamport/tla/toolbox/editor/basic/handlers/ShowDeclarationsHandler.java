/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import java.util.Arrays;
import java.util.Vector;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.dialogs.PopupDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.ThmOrAssumpDefNode;

/**
 * The handler for the Shows Declarations operation, which pops up a list
 * of top-level definitions and declarations of the module.  The popup has an
 * option of showing or hiding instantiated definitions--which includes all instantiations
 * that involve name changing or substitution of parameters.  It also allows the user
 * to type the prefix of what he's looking for, which does the appropriate filtering of
 * what's displayed.
 * 
 * Popping up the dialog is easy.  Handling typed input isn't.  The problem is that typing
 * ordinarily changes the selection, which triggers the selection listener's code for
 * jumping to the selected declaration.  Keeping this from happening required: (1) adding the
 * listeners in the right order so the key listener gets called first, (2) always keeping 
 * some item selected so typing doesn't necessarily cause an item to be selected, and 
 * (3) having the key listener disable other key listeners by the magical 
 * <code>e.doit = false</code> statement in it.
 * 
 * 
 * @author lamport
 *
 */
public class ShowDeclarationsHandler extends AbstractHandler implements IHandler
{

    /**  This method is called to handle the Show Declarations operation.
     * 
    * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
    */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        Shell parent = UIHelper.getShellProvider().getShell();
        ShowDeclarationsPopupDialog popup = new ShowDeclarationsPopupDialog(parent);
        popup.open();

        return null;
    }

    /**
     * The text for telling the user to choose hiding/showing instantiated definitions.
     * 
     * @param showAll
     * @return
     */
    public static String infoText(boolean showAll)
    {
        return "Type space to " + (showAll ? "hide" : "show") + " instantiated definitions";
    }

    /**
     * The text at the top of the popup.  It shows the prefix string typed if that's
     * not empty, otherwise just the standard title.
     * 
     * @param prefix
     * @return
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
     * The class of which the pop dialog is an object.  It contains fields that the listeners
     * need to get hold of.
     * 
     * @author lamport
     */
    public static class ShowDeclarationsPopupDialog extends PopupDialog
    {
        Shell parent; // The dialog's parent shell.
        List list; // The org.eclipse.swt.widgets.List (not ordinary Java List) being displayed.
        boolean showAll = true; // True iff displaying definitions imported by instantiation.
        String filterPrefix = ""; // For filtering displayed declarations as user types prefix.

        /*
         * The TLA editor with focus and the module it's open on.  They are saved because the editor
         * no longer has focus when the popup dialog is raised.
         */
        TLAEditor editor;
        ModuleNode module;

        // int curSelection; // The currently selected item.

        /**
         * Constructs a new Show Declarations popup with indicated parent and
         * with showAll determining if instantiated definitions should be shown.
         * 
         * @param parent
         * @param showAll
         */
        public ShowDeclarationsPopupDialog(Shell parent)
        {
            super(parent, SWT.NO_TRIM, true, // takeFocusOnOpen
                    false, // persistSize
                    true, // persistLocation
                    true, // showDialogMenu
                    true, // showPersistActions
                    "Definitions and Declarations", // titleText
                    ""); // infoText
            this.parent = parent;
            this.showAll = true;
            this.setInfoText(ShowDeclarationsHandler.infoText(showAll));
            this.editor = EditorUtil.getTLAEditorWithFocus();
            if (this.editor != null)
            {
                module = ResourceHelper.getModuleNode(editor.getModuleName());
            }
            System.out.println("Created new popup with showAll = " + showAll);

        }

        /**
         * This is just to make setInfoText a public method so the handlers
         * can call it.
         */
        public void setInfoText(String str)
        {
            super.setInfoText(str);
        }

        /**
         * This is just to make setTitleText a public method so the handlers
         * can call it.
         */
        public void setTitleText(String str)
        {
            super.setTitleText(str);
        }

        /**
         *  Sets the class's <code>list</code> field, which contains the
         *  org.eclipse.swt.widgets.List object with the actual items to be displayed.
         *  It also sets the data for each item to be the node to jump to, so
         *  list.getData(list.getSelection()[0]) gets that node for the selected
         *  item.
         */
        protected void setList()
        {
            // Get the list of SymbolNodes to be displayed. They
            // come from the module's constant decls, variable decls,
            // opdef nodes, ThmOrAssumpDefNodes.

            String lcFilterPrefix = filterPrefix.toLowerCase();
            list.removeAll();
            // Get the current module.
            if (module == null)
            {
                return;
            }
            Vector symVec = new Vector(40);
            SymbolNode[] syms = module.getConstantDecls();
            for (int i = 0; i < syms.length; i++)
            {
                if (syms[i].getName().toString().toLowerCase().startsWith(lcFilterPrefix))
                {
                    symVec.add(syms[i]);
                }
            }

            syms = module.getVariableDecls();
            for (int i = 0; i < syms.length; i++)
            {
                if (syms[i].getName().toString().toLowerCase().toLowerCase().startsWith(lcFilterPrefix))
                {
                    symVec.add(syms[i]);
                }
            }

            OpDefNode[] symsOpD = module.getOpDefs();
            for (int i = 0; i < symsOpD.length; i++)
            {
                if (ResourceHelper.isFromUserModule(symsOpD[i].getSource())
                        && (showAll || (symsOpD[i].getSource() == symsOpD[i]))
                        && symsOpD[i].getName().toString().toLowerCase().startsWith(lcFilterPrefix))
                {
                    symVec.add(symsOpD[i]);
                }
            }

            ThmOrAssumpDefNode[] symsTAD = module.getThmOrAssDefs();
            for (int i = 0; i < symsTAD.length; i++)
            {
                if (ResourceHelper.isFromUserModule(symsTAD[i].getSource())
                        && (showAll || (symsTAD[i].getSource() == symsTAD[i]))
                        && symsTAD[i].getName().toString().toLowerCase().startsWith(lcFilterPrefix))
                {
                    symVec.add(symsTAD[i]);
                }
            }

            SymbolNode[] symbols = new SymbolNode[symVec.size()];

            for (int i = 0; i < symbols.length; i++)
            {
                symbols[i] = (SymbolNode) symVec.get(i);
            }

            Arrays.sort(symbols);

            for (int i = 0; i < symbols.length; i++)
            {
                list.add(symbols[i].getName().toString());
                list.setData(symbols[i].getName().toString(), symbols[i]);
            }
        }

        /**
         * This is the method that puts the content into the popup's
         * dialog area.  It puts an org.eclipse.swt.widgets.List
         * (note that this isn't an ordinary Java List) there.
         * 
         */
        protected Control createDialogArea(Composite composite)
        {
            // create the list
            list = new List(composite, SWT.SINGLE | SWT.V_SCROLL | SWT.RESIZE);

            // Populate the popup's display area.
            setList();

            // list.addKeyListener(listener);

            /* 
             *  To put a Composite instead of a List in the
             *  dialog area, do something like the following:
            Composite stuff = new Composite(composite, SWT.NONE);
            stuff.setLayoutData(new GridData());
            stuff.setLayout(new FillLayout(SWT.VERTICAL));
            Button button1 = new Button(stuff, SWT.FLAT);
            button1.setText("Button 1");
            // button1.setParent(stuff);
            Button button2 = new Button(stuff, SWT.PUSH);
            button2.setText("Button 2");
            */
            list.addSelectionListener(new ShowDeclarationsSelectionListener(EditorUtil.getTLAEditorWithFocus()));

            // Adding the KeyListener after the SelectionListener is necessary for the handling
            // of keystrokes to work. If they're added in the opposite order, some keys change
            // the selection and call the SelectionListener.

            list.addKeyListener(new ShowDeclarationsKeyListener(this)); // Testing

            // System.out.println("testing showAll = " + showAll);

            // It is necessary to select an item on the list if one is to be
            // able to listen for keystrokes. Otherwise, a keystroke causes the
            // current selection to change, calling the SelectionListener's widgetSelected()
            // method.
            list.setSelection(0);
            return list;
        }
    }

    /**
     * A listener for the List put into the dialog by the createDialogArea
     * method of ShowDefinitionsPopupDialog.
     * 
     * @author lamport
     *
     */
    public static class ShowDeclarationsSelectionListener implements SelectionListener
    {
        private TLAEditor srcEditor;

        public ShowDeclarationsSelectionListener(TLAEditor editor)
        {
            super();
            this.srcEditor = editor;
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
            SymbolNode node = (SymbolNode) list.getData(list.getSelection()[0]);
            EditorUtil.setReturnFromOpenDecl(srcEditor);
            UIHelper.jumpToDefOrDecl(node);
        }
    }

    /**
     * The Key Listener for keyboard input to the popup dialog.  The following
     * kinds of keyboard input are handled:
     * <ul>
     * <li> Return, which is equivalent to clicking on the selected item.
     * <li> Space, which toggles between showing and hiding instantiated declarations.
     * <li> Arrow keys, which move the selection.
     * <li> Letters, numbers,  "_", "!", and other characters like "\" and "*" that can
     *      appear in the names of user-defined operators.  These characters are added 
     *      to the prefix used for filtering what is shown.
     *      (Those other characters added by LL on 29 Mar 2012.)
     * <li> Delete/backspace, which deletes one character from the filtering prefix.
     * </ul>
     * Other typed input is ignored.
     * @author lamport
     *
     */
    public static class ShowDeclarationsKeyListener implements KeyListener
    { // Shell parent;
        ShowDeclarationsPopupDialog popup;

        // boolean showAll; // a local copy of the current specs' showAllDeclarations field.

        public ShowDeclarationsKeyListener(ShowDeclarationsPopupDialog popup)
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
            if (keyPressed == ' ')
            {
                popup.showAll = !popup.showAll;
                popup.setList();
                popup.setInfoText(ShowDeclarationsHandler.infoText(popup.showAll));
                if (list.getItemCount() > 0)
                {
                    list.select(0);
                }
            } else if (keyCode == SWT.ARROW_DOWN || keyCode == SWT.ARROW_RIGHT)
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
                SymbolNode node = (SymbolNode) list.getData(list.getSelection()[0]);
                EditorUtil.setReturnFromOpenDecl(popup.editor);
                UIHelper.jumpToDefOrDecl(node);
                popup.close();
            } else if (Character.isLetterOrDigit(keyPressed) || 
                    (keyPressed == '_') || 
                    (keyPressed == '!') ||
                    // The following added by LL on 29 Mar 2012
                    (keyPressed == '\\') ||
                    (keyPressed == '+') ||
                    (keyPressed == '-') ||
                    (keyPressed == '%') ||
                    (keyPressed == '^') ||
                    (keyPressed == '.') ||
                    (keyPressed == '<') ||
                    (keyPressed == '>') ||
                    (keyPressed == ':') ||
                    (keyPressed == '&') ||
                    (keyPressed == '|') ||
                    (keyPressed == '#') ||
                    (keyPressed == '$') ||
                    (keyPressed == '?') ||
                    (keyPressed == '@') ||
                    (keyPressed == '*') ||
                    (keyPressed == '=') ||
                    (keyPressed == '/')
                    )
            {
                popup.filterPrefix = popup.filterPrefix + keyPressed;
                popup.setList();
                popup.setTitleText(ShowDeclarationsHandler.titleText(popup.filterPrefix));
                popup.setInfoText(ShowDeclarationsHandler.infoText(popup.showAll));
                if (list.getItemCount() > 0)
                {
                    list.select(0);
                }

            } else if ((keyCode == SWT.DEL || keyCode == SWT.BS) && !popup.filterPrefix.equals(""))
            {
                popup.filterPrefix = popup.filterPrefix.substring(0, popup.filterPrefix.length() - 1);
                popup.setList();
                popup.setTitleText(ShowDeclarationsHandler.titleText(popup.filterPrefix));
                popup.setInfoText(ShowDeclarationsHandler.infoText(popup.showAll));
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

}
