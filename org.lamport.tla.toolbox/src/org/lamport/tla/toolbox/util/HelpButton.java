package org.lamport.tla.toolbox.util;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Platform;
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
 * This class implements a help button that takes the user to a specified location
 * in the help system's html files.  The only part of this class that is used
 * externally is the helpButton command.
 * 
 * Implemented by Leslie Lamport
 */

/*
 * Some times Eclipse default internal web browser will not work in your
 * Ubuntu environment.  Is that the case, you need to install webkit
 * library for Ubuntu.  In order to install webkit libraries got to your
 * terminal and run this command.
 *
 *   sudo apt-get install libwebkitgtk-1.0-0
 */

/*
 * To do:
 * - Add a menu bar  to the HTML browser with back and forward buttons.  See:
 * 
 *    http://www.eclipse.org/articles/Article-SWT-browser-widget/browser.html
 *    
 * - Re-use the same browser window if it exists?  Or perhaps make that a
 *   preference?
 *   
 * - Remember the previous size and location of the browser when raising
 *   a new one.
 */

/**
 * The constructor adds a help button to a specified Composite that goes
 * to the help page specified by its String argument.
 */
public class HelpButton {
    public static String baseURL;

    /**
     * 
     * @param parent    Where the button should be added.
     * @param helpFile  The suffix of the URL of the help page, which follows
     *                  .../org.lamport.tla.toolbox.doc/html/ -- for example,
     *                  "model/overview-page.html#what-to-check" .             
     * @return A Button that has been added to the Composite that, when clicked
     *         raises a browser window on the specified help page URL.
     */
    public static Button helpButton(Composite parent, String helpFile) {
        Button button = new Button(parent, SWT.NONE);
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
            // Set fileX to the file name with "/"s replaced by
            // the local file separator.
            String fileX = file;
            if (!File.separator.equals("/")) {
                while (fileX.indexOf('/') != -1) {
                    fileX = fileX.substring(0, fileX.indexOf('/'))
                            + File.separator
                            + fileX.substring(fileX.indexOf('/') + 1);
                    System.out.println("FileX = " + fileX);
                }
            }
            
            /**
             * When run on Eclipse, the following code sets baseURL to
             * 
             *    reference:file:/C:/lamport/tla/newtools/tla-workspace/org.lamport.tla.toolbox
             *    
             * When run as a standalone release on my machine, it produces:
             * 
             *     initial@reference:file:plugins/org.lamport.tla.toolbox_1.0.0.201212121501
             */
            // Bundle bundle = FrameworkUtil.getBundle(this.getClass());
            // baseURL = bundle.getLocation() ;

            
            /**
             * If the Toolbox is being executed from the directory containing the
             * executable, then this sets dir to its plugins directory
             * and dir.
             */
//            File dir = new File("plugins");
//            url = null;
//            String[] children = dir.list();
//            try {
//                url = dir.getCanonicalPath();
//            } catch (IOException e) {
//                // I don't know what can cause this, but we have little
//                // choice but to use the help pages on the Web.
//                children = null ;
//                e.printStackTrace();
//            }
//            String docdir = null;
//            if ((url == null) || (children == null) || (children.length == 0)) {
//                // Something's wrong.  The user may be running the Toolbox from
//                // a directory other than the one containing the executable.
//                // In that case, we use the help pages on the Web.
//                url = "http://tla.msr-inria.inria.fr/tlatoolbox/doc/" + fileX ;                
//            } else {
//                // We use the Toolbox's own copy of the Help files.
//                int i = 0;
//                boolean found = false;
//                while ((i < children.length) && !found) {
//                    docdir = children[i];
//                    if (docdir.indexOf("org.lamport.tla.toolbox.doc") != -1) {
//                        found = true;
//                    }
//                    i++;
//                }
//                System.out.println("File separator = " + File.separator);
//                if (found) {
//
//                    url = url + File.separator + docdir + File.separator
//                            + "html" + File.separator + fileX;
//                } else {
//                    // The Toolbox is being run from Eclipse, or else there's a
//                    // problem.
//                    Bundle bundle = FrameworkUtil.getBundle(this.getClass());
//                    url = bundle.getLocation();
//                    System.out.println("What's going on");
//                    int idx = url.indexOf("reference:file:");
//                    System.out.println("original url = " + url);
//                    if (idx != -1) {
//                        url = url.substring(idx + "reference:file:".length());
//                        if (url.charAt(0) == '/') {
//                            url = url.substring(1);
//                        }
//                    }
//                    System.out.println("url - initial stuff: " + url);
//                    idx = url.indexOf("org.lamport.tla.toolbox");
//                    if (idx != -1) {
//                        url = url.substring(0, idx)
//                                + "org.lamport.tla.toolbox.doc"
//                                + url.substring(idx
//                                        + "org.lamport.tla.toolbox".length());
//                    }
//                    // System.out.println("url of toolbox.doc directory: " +
//                    // url);
//                    url = url + "html/" + file;
//                    System.out.println("url = " + url);
//                }
//            }
            /**
             * TESTING STUFF -- which seems to work.
             */
            Bundle bundle = Platform.getBundle("org.lamport.tla.toolbox.doc");
            URL fileURL = bundle.getEntry("html/prover/test.html");
            File file = null;
            try {
                file = new File(FileLocator.resolve(fileURL).toURI());
            } catch (URISyntaxException e1) {
                e1.printStackTrace();
            } catch (IOException e1) {
                e1.printStackTrace();
            }
            if (file != null) {
              url = file.getPath();
            } ;
            if ((file == null) || (url == null)) {
                url = "http://tla.msr-inria.inria.fr/tlatoolbox/doc/" + file ;
                System.out.println("Could not find local copy of help file.");
            }
            System.out.println("url = " + url);
            /**
             * END TESTING STUFF
             */
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
