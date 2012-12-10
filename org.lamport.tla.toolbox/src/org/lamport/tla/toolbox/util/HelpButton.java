/**
 * 
 */
package org.lamport.tla.toolbox.util;

import java.io.File;
import java.io.IOException;

import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.SWTError;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

/**
 * 
 * Implemented by Leslie Lamport
 */

public class HelpButton {
    public static String baseURL;

    public static Button helpButton(Composite parent, String helpFile) {
        Button button = new Button(parent, SWT.PUSH);
        HelpButtonListener listener = new HelpButtonListener(parent, helpFile);
        button.addSelectionListener(listener);
        Image helpImg = PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_LCL_LINKTO_HELP);
        button.setImage(helpImg);
        GridData gridData = new GridData();
        gridData.verticalAlignment = SWT.TOP;
        button.setLayoutData(gridData);
        button.setEnabled(true);
        baseURL = listener.url;
        return button;
    }

    public static class HelpButtonListener extends SelectionAdapter implements
            SelectionListener {

        String file;
        String url;
        Composite shell;

        HelpButtonListener(Composite parent, String helpFile) {
            super();
            file = helpFile;
            shell = parent;
            String fileX = file;
            if (!File.separator.equals("/")) {
                while (fileX.indexOf('/') != -1) {
                    fileX = fileX.substring(0, fileX.indexOf('/'))
                            + File.separator
                            + fileX.substring(fileX.indexOf('/') + 1);
                    System.out.println("FileX = " + fileX);
                }
            }
            File dir = new File("plugins");
            url = null;
            try {
                url = dir.getCanonicalPath();
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            String[] children = dir.list();
            String docdir = null;
            int i = 0;
            boolean found = false;
            while ((i < children.length) && !found) {
                docdir = children[i];
                if (docdir.indexOf("org.lamport.tla.toolbox.doc") != -1) {
                    found = true;
                }
                i++;
            }
            System.out.println("File separator = " + File.separator);
            if (found) {

                url = url + File.separator + docdir + File.separator + "html"
                        + File.separator + fileX;
            } else {
                // The Toolbox is being run from Eclipse, or else there's a
                // problem.
                Bundle bundle = FrameworkUtil.getBundle(this.getClass());
                url = bundle.getLocation();
                System.out.println("What's going on");
                int idx = url.indexOf("reference:file:");
                System.out.println("original url = " + url);
                if (idx != -1) {
                    url = url.substring(idx + "reference:file:".length());
                    if (url.charAt(0) == '/') {
                        url = url.substring(1);
                    }
                }
                System.out.println("url - initial stuff: " + url);
                idx = url.indexOf("org.lamport.tla.toolbox");
                if (idx != -1) {
                    url = url.substring(0, idx)
                            + "org.lamport.tla.toolbox.doc"
                            + url.substring(idx
                                    + "org.lamport.tla.toolbox".length());
                }
//                System.out.println("url of toolbox.doc directory: " + url);
                url = url + "html/" + file;
                System.out.println("url = " + url);
            }

        }

        public void widgetSelected(SelectionEvent e) {
            Shell topshell = UIHelper.getShellProvider().getShell();
            Shell shell = new Shell(topshell, SWT.SHELL_TRIM);
            shell.setLayout(new FillLayout());

            // String contextHelpID = "definition_override_wizard";
            // final String ECLIPSE_HELP = "org.eclipse.ui.help";
            // shell.setData(ECLIPSE_HELP,contextHelpID);
            // UIHelper.setHelp(shell, contextHelpID) ;
            // /*PlatformUI.getWorkbench().*/
            // getHelpSystem().displayHelp(contextHelpID);

            Browser browser;
            try {
                browser = new Browser(shell, SWT.NONE);
            } catch (SWTError e1) {
                System.out.println("Could not instantiate Browser: "
                        + e1.getMessage());
                shell.dispose();
                return;
            }

            // Bundle bundle = FrameworkUtil.getBundle(this.getClass());
            // String url = bundle.getLocation() ;
            // System.out.println("What's going on");
            // int idx = url.indexOf("reference:file:");
            // System.out.println("original url = " + url);
            // if (idx != -1) {
            // url = url.substring(idx+"reference:file:".length()) ;
            // if (url.charAt(0) == '/') {
            // url = url.substring(1) ;
            // }
            // }
            // System.out.println("url - initial stuff: " + url);
            // idx = url.indexOf("org.lamport.tla.toolbox") ;
            // if (idx != -1) {
            // url = url.substring(0, idx) + "org.lamport.tla.toolbox.doc"
            // + url.substring(idx + "org.lamport.tla.toolbox".length());
            // }
            // System.out.println("url of toolbox.doc directory: " + url);
            // url = url + "html/" + file ;
            // String url =
            // "http://127.0.0.1:45076/help/index.jsp?topic=%2Forg.lamport.tla.toolbox.doc%2Fhtml%2F";
            // url = url + file.replaceAll("/", "%2F") ;
            // System.out.println("final url: " + url);
            System.out.println("url actually used: " + url) ;
            browser.setUrl(url);
            shell.open();

        }

        public void widgetDefaultSelected(SelectionEvent e) {
            widgetSelected(e);
        }

    }

}
