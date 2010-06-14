/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.dialogs.PopupDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.lamport.tla.toolbox.util.UIHelper;

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
        public ShowDefinitionsPopupDialog (Shell parent) {
            super (parent, 
                    SWT.NO_TRIM,  
                    true, // takeFocusOnOpen  
                    true, // persistSize  
                    true, // persistLocation  
                    true, // showDialogMenu 
                    true, //showPersistActions 
                    "Definitions and Declarations", // titleText 
                    ""); // infoText
        }
       
        protected Control createDialogArea(Composite composite) {
            List list = new List(composite, 
                    SWT.SINGLE | SWT.V_SCROLL | SWT.RESIZE);
            list.add("Def 1");
            list.add("Def 2");
            
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
            list.addSelectionListener(new ShowDefinitionsSelectionListener());
            return list;
        }
    }
    
    public static class ShowDefinitionsSelectionListener implements SelectionListener {

        public void widgetDefaultSelected(SelectionEvent e)
        {
            // I don't think this should never be called.
            // but if it is
            
        }

        public void widgetSelected(SelectionEvent e)
        { String[] selection = ((List) e.widget).getSelection();
            System.out.println("We're here at selection: " + selection[0]);
        }
    }

}
