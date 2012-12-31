package org.lamport.tla.toolbox.util;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.net.URL;

import org.eclipse.swt.*;
import org.eclipse.swt.browser.*;
import org.eclipse.swt.custom.*;
import org.eclipse.swt.layout.*;
import org.eclipse.swt.widgets.*;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.dialogs.MessageDialog;
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
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
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
	
	/**
	 *  This is used only for testing
	 */
    public static String baseURL;

    // If we want clicking a help button to re-use an existing window,
    // then we need to replace the local declaration of browser in
    // widgetSelected with a static field, and also add a static field
    // to contain the current local variable shell of that method.
    //
    //    static Browser browser;
    //    static Shell shell;

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
//String testString = "";
        HelpButtonListener(Composite parent, String helpFile) {
            super();
            file = helpFile;
            shell = parent;
            // Set fileX to the file name with "/"s replaced by
            // the local file separator.
//            String fileX = file;
//            if (!File.separator.equals("/")) {
//                while (fileX.indexOf('/') != -1) {
//                    fileX = fileX.substring(0, fileX.indexOf('/'))
//                            + File.separator
//                            + fileX.substring(fileX.indexOf('/') + 1);
//                    System.out.println("FileX = " + fileX);
////testString = testString + "FileX = " + fileX + "\n" ;
//                }
//            }
            
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
            /**
             * TESTING STUFF -- which seems to work.
             */
            Bundle bundle = Platform.getBundle("org.lamport.tla.toolbox.doc");
            URL fileURL = bundle.getEntry("html/" + this.file);
            File theFile = null;
            try {
                theFile = new File(FileLocator.resolve(fileURL).toURI());
            } catch (URISyntaxException e1) {
                e1.printStackTrace();
//testString = testString + "URISyntaxException\n" ;
            } catch (IOException e1) {
                e1.printStackTrace();
//testString = testString + "IOException\n" ;
            }
            if (theFile != null) {
              url = theFile.getPath();
            } ;
            if ((theFile == null) || (url == null)) {
                url = "http://tla.msr-inria.inria.fr/tlatoolbox/doc/" + file ;
                System.out.println("Could not find local copy of help file.");
//testString = testString + "Could not find local copy of help file.\n";
            }
            System.out.println("url = " + url);
//testString = testString + "url = " + url + "\nEnd constructor\n" ;
            /**
             * END TESTING STUFF
             */
        }

        public void widgetSelected(SelectionEvent e) {
         /* The following code works.
          * 
            Shell topshell = UIHelper.getShellProvider().getShell();
            Shell shell = new Shell(topshell, SWT.SHELL_TRIM);
            shell.setLayout(new FillLayout());
            Browser browser;
            try {
                browser = new Browser(shell, SWT.NONE);
            } catch (SWTError e1) {
                System.out.println("Could not instantiate Browser: "
                        + e1.getMessage());
                shell.dispose();
                return;
            }
            browser.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, true, true)) ;
            System.out.println("url actually used: " + url) ;
            browser.setUrl(url);
            shell.open();

        */
            
            
        	Shell topshell = UIHelper.getShellProvider().getShell();
            Shell shell = new Shell(topshell, SWT.SHELL_TRIM);
            
//            FillLayout fillLayout = new FillLayout();
//            fillLayout.type = SWT.VERTICAL;
//            shell.setLayout(fillLayout);
            shell.setLayout(new FillLayout());
            Composite comp = new Composite(shell, SWT.NONE);
            comp.setLayout(new GridLayout(1, false));

            ToolBar navBar = new ToolBar(comp, SWT.NONE);
        	navBar.setLayoutData(new GridData(GridData.FILL_HORIZONTAL | GridData.HORIZONTAL_ALIGN_END));
            final ToolItem back = new ToolItem(navBar,  SWT.PUSH);
        	back.setText("<-    Back    ");
        	back.setEnabled(false);
//        	Label label = new Label(navBar, SWT.NONE);
//        	label.setText(" x  ");
        	final ToolItem forward = new ToolItem(navBar, SWT.PUSH);
        	forward.setText(" Forward  ->");
        	forward.setEnabled(false);
        	
            final Browser browser ;
            try {
                browser = new Browser(comp, SWT.NONE);
            } catch (SWTError e1) {
                System.out.println("Could not instantiate Browser: "
                        + e1.getMessage());
                shell.dispose();
                return;
            }
            GridData data = new GridData(GridData.FILL_BOTH);
        	browser.setLayoutData(data);
            
        	back.addListener(SWT.Selection, new Listener() {
        		public void handleEvent(Event event) {
        			browser.back();
        		}
        	});
        	forward.addListener(SWT.Selection, new Listener() {
        		public void handleEvent(Event event) {
        			browser.forward();
        		}
        	});
        	final LocationListener locationListener = new LocationListener() {
        		public void changed(LocationEvent event) {
        			Browser browser = (Browser)event.widget;
        			back.setEnabled(browser.isBackEnabled());
        			forward.setEnabled(browser.isForwardEnabled());
        		}
        		public void changing(LocationEvent event) {
        		}
        	};
        	browser.addLocationListener(locationListener);
        	
            System.out.println("url actually used: " + url) ;
//testString = testString + "url actually used: " + url;
            browser.setUrl(url);
            shell.open();
//MessageDialog.openError(UIHelper.getShellProvider().getShell(),
//                    "Decompose Proof Command Test", testString);
       }

        public void widgetDefaultSelected(SelectionEvent e) {
            widgetSelected(e);
        }

    }

}
