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
import org.eclipse.jface.text.ITextSelection;
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
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.ThmOrAssumpDefNode;

/**
 * The handler for the Shows Definition operation, which pops up a list
 * of top-level definitions and declarations of the module.
 * 
 * @author lamport
 *
 */
public class ShowDefinitionsHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        Shell parent = UIHelper.getShellProvider().getShell();
        ShowDefinitionsPopupDialog popup = new ShowDefinitionsPopupDialog(parent);
        popup.open();
        return null;
    }

    public static class ShowDefinitionsPopupDialog extends PopupDialog
    {
        public ShowDefinitionsPopupDialog(Shell parent)
        {
            super(parent, SWT.NO_TRIM, true, // takeFocusOnOpen
                    true, // persistSize
                    true, // persistLocation
                    true, // showDialogMenu
                    true, // showPersistActions
                    "Definitions and Declarations", // titleText
                    ""); // infoText
        }

        /**
         * This is the method that puts the content into the popup's
         * dialog area.  It puts an org.eclipse.swt.widgets.List
         * (note that this isn't an ordinary Java List) there.
         * 
         */
        protected Control createDialogArea(Composite composite)
        {
            // Get the list of SymbolNodes to be displayed. They
            // come from the module's contant decls, variable decls,
            // opdef nodes, ThmOrAssumpDefNodes.

            // Get the current module.
            ModuleNode module = ResourceHelper.getModuleNode(EditorUtil.getTLAEditorWithFocus().getModuleName());
            if (module == null)
            {
                return null;
            }
            Vector symVec = new Vector(40);
            SymbolNode[] syms = module.getConstantDecls();
            for (int i = 0; i < syms.length; i++)
            {
                symVec.add(syms[i]);
                i++;
            }

            syms = module.getVariableDecls();
            for (int i = 0; i < syms.length; i++)
            {
                symVec.add(syms[i]);
                i++;
            }

            OpDefNode[] symsOpD = module.getOpDefs();
            for (int i = 0; i < symsOpD.length; i++)
            {
                if (ResourceHelper.isFromUserModule(symsOpD[i].getSource()))
                {
                    symVec.add(symsOpD[i]);
                }
                i++;
            }

            ThmOrAssumpDefNode[] symsTAD = module.getThmOrAssDefs();
            for (int i = 0; i < symsTAD.length; i++)
            {
                if (ResourceHelper.isFromUserModule(symsTAD[i].getSource()))
                {
                    symVec.add(symsTAD[i]);
                }
                i++;
            }

            SymbolNode[] symbols = new SymbolNode[symVec.size()];

            for (int i = 0; i < symbols.length; i++)
            {
                symbols[i] = (SymbolNode) symVec.get(i);
            }

            Arrays.sort(symbols);

            // Populate the popup's display area.
            List list = new List(composite, SWT.SINGLE | SWT.V_SCROLL | SWT.RESIZE);
            for (int i = 0; i < symbols.length; i++)
            {
                list.add(symbols[i].getName().toString());
                list.setData(symbols[i].getName().toString(), symbols[i]);
            }
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
            list.addSelectionListener(new ShowDefinitionsSelectionListener(EditorUtil.getTLAEditorWithFocus()));
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
    public static class ShowDefinitionsSelectionListener implements SelectionListener
    {
        private TLAEditor srcEditor;

        public ShowDefinitionsSelectionListener(TLAEditor editor)
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

    public static class ShowDefinitionsKeyListener implements KeyListener
    {

        public void keyPressed(KeyEvent e)
        {
            char keyPressed = e.character;
            // TODO Auto-generated method stub

        }

        public void keyReleased(KeyEvent e)
        {
            // TODO Auto-generated method stub

        }

    }

}
