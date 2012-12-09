/**
 * 
 */
package org.lamport.tla.toolbox.util;

import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.SWTError;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

/**
 * 
 * Implemented by Leslie Lamport
 */

public class HelpButton {
    public static String baseURL ;
    
    
    public static Button helpButton(Composite parent, String helpFile) {
       Button button = new Button(parent, SWT.PUSH) ;
       HelpButtonListener listener = new HelpButtonListener(helpFile) ;
       button.addSelectionListener(listener);
       baseURL = listener.baseURL ;
       return button;
    }
    
    public static class HelpButtonListener extends SelectionAdapter implements SelectionListener {

        String file ;
        String baseURL ;
        
        HelpButtonListener(String helpFile) {
            super() ;
            file = helpFile;
            Bundle bundle = FrameworkUtil.getBundle(this.getClass());
            baseURL = bundle.getLocation() ;
        }
        
        
        public void widgetSelected(SelectionEvent e) {
            Shell topshell = UIHelper.getShellProvider().getShell() ;
            Shell shell = new Shell(topshell, SWT.SHELL_TRIM) ;
            shell.setLayout(new FillLayout());
            Browser browser;
            try {
              browser = new Browser(shell, SWT.NONE);
        } catch (SWTError e1) {
                System.out.println("Could not instantiate Browser: " + e1.getMessage());
                shell.dispose();
                return;
        }
            
            Bundle bundle = FrameworkUtil.getBundle(this.getClass());
            String url = bundle.getLocation() ;
            System.out.println("What's going on");
            int idx = url.indexOf("reference:file:");
            System.out.println("original url = " + url);
            if (idx != -1) {
                url = url.substring(idx+"reference:file:".length()) ;
                if (url.charAt(0) == '/') {
                    url = url.substring(1) ;
                }
            }
            System.out.println("url - initial stuff: " + url);
            idx = url.indexOf("org.lamport.tla.toolbox") ;
            if (idx != -1) {
                url = url.substring(0, idx) + "org.lamport.tla.toolbox.doc" 
                        + url.substring(idx + "org.lamport.tla.toolbox".length());
            }
            url = url + "html/" + file;          
        System.out.println("final url: " + url); 
           browser.setUrl(url) ;
           shell.open();
      
        }
        
        public void widgetDefaultSelected(SelectionEvent e) {
           widgetSelected(e);
        }

    }

}
