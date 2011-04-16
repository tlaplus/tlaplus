/**
 * This class was created by LL on 12 April 2011 to try to pop up a simple
 * message.  However, it didn't work because I was apparently calling it before
 * the Toolbox had gotten far enough to be able to display a window.  So, it
 * has never been tested.  However, it might be handy at some point. 
 * 
 * THIS METHOD IS UNNECESSARY.  USE the Eclipse MessageDialog class open method.
 */
package org.lamport.tla.toolbox.util;

import org.eclipse.jface.dialogs.PopupDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Shell;

/**
 * @author lamport
 *
 */
public class PopupMessage extends PopupDialog
{

    /**
     * @param parent
     * @param shellStyle
     * @param takeFocusOnOpen
     * @param persistSize
     * @param persistLocation
     * @param showDialogMenu
     * @param showPersistActions
     * @param titleText
     * @param infoText
     */
    public PopupMessage(Shell parent, String titleText, String infoText)
    {
        super(parent, 
              SWT.NO_TRIM, // shellStyle, 
              true, // takeFocusOnOpen, 
              false, // persistSize, 
              true, // persistLocation, 
              true, // showDialogMenu, 
              true, // showPersistActions,
              titleText, 
              infoText);
        // TODO Auto-generated constructor stub
    }
    /**
     * This should pop up a window with a title displaying a message.  However,
     * I don't really know what it does because it's never been tested.
     * 
     * @param title
     * @param message
     */
    public static void Display(String title, String message) {
        Shell parent = UIHelper.getShellProvider().getShell();
        PopupMessage popup = new PopupMessage(parent, title, message);
        popup.open();
        return;
    }
}
