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
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.events.ShellEvent;
import org.eclipse.swt.events.ShellListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
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
//import org.lamport.tla.toolbox.editor.basic.handlers.DecomposeProofHandler;
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
 * Sometimes the Eclipse default internal web browser will not work in your
 * Ubuntu environment.  Is that the case, you need to install webkit
 * library for Ubuntu.  In order to install webkit libraries go to your
 * terminal and run this command.
 *
 *   sudo apt-get install libwebkitgtk-1.0-0
 */

/**
 * The constructor adds a help button to a specified Composite that links
 * to the help page specified by its String argument.
 */
public class HelpButton {
	
	/**
	 *  This is used only for testing
	 */
    public static String baseURL;

    /**
     * The following fields contain the Browser that displays the help page,
     * the Shell that creates the Help Window containing the browser, and the
     * location and size of that window the last time it was closed.
     */
    static Browser browser = null;
    static Shell helpShell = null;
    static Point location = null ;
    static Point size = null ;
    
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

//        String file;
        String url;
        Composite shell;

        HelpButtonListener(Composite parent, String helpFile) {
            super();
            String file = helpFile;
            shell = parent;
            /*
             * For a helpFile like "foo.html#section", set fileName to
             * "foo.html" and suffix to "#section".  If there is no
             * such suffix, then set fileName to file and suffix to "".
             */
            String fileName = file;
            String suffix = "" ;
            int idx = fileName.indexOf("#") ;
            if (idx != -1) {
                suffix = fileName.substring(idx) ;
                fileName = fileName.substring(0, idx) ;
            }
            Bundle bundle = Platform.getBundle("org.lamport.tla.toolbox.doc");
            URL fileURL = bundle.getEntry("html/" + fileName);
            File theFile = null;
            try {
                theFile = new File(FileLocator.resolve(fileURL).toURI());
            } catch (URISyntaxException e1) {
                e1.printStackTrace();
            } catch (IOException e1) {
                e1.printStackTrace();
            }
            if (theFile != null) {
              url = theFile.getPath() + suffix;
            } ;
            if ((theFile == null) || (url == null)) {
                url = "http://tla.msr-inria.inria.fr/tlatoolbox/doc/" + file ;
                System.out.println("Could not find local copy of help file.");
            }
        }
        
        /**
         * This method is called when the `?' button is clicked. It opens the
         * page in the current help window if there is one, otherwise it raises
         * a new window at the position and with the size of the window the last
         * time it was closed in the current execution of the Toolbox.
         */
        public void widgetSelected(SelectionEvent e) {
            boolean setSize = false;

            /*
             * If the window doesn't already exist, create it and add the
             * browser.
             */
            if (helpShell == null) {
                setSize = true;
                Shell topshell = UIHelper.getShellProvider().getShell();
                /*
                 * Raise the window without a minimize button because minimizing
                 * puts it as a small window in a corner of the screen, not on
                 * the task bar.
                 */
                helpShell = new Shell(topshell, SWT.CLOSE | SWT.TITLE
                        | SWT.RESIZE);
                helpShell.setText("Toolbox Help");
                helpShell.addDisposeListener(new HelpWindowDisposeListener());
                helpShell.addShellListener(new HelpShellListener());
                browser = null;
                helpShell.setLayout(new FillLayout());
                Composite comp = new Composite(helpShell, SWT.NONE);
                comp.setLayout(new GridLayout(1, false));

                /*
                 * Add the "back" and "forward" buttons.
                 */
                ToolBar navBar = new ToolBar(comp, SWT.NONE);
                navBar.setLayoutData(new GridData(GridData.FILL_HORIZONTAL
                        | GridData.HORIZONTAL_ALIGN_END));
                final ToolItem back = new ToolItem(navBar, SWT.PUSH);
                back.setText("<-    Back    ");
                back.setEnabled(false);
                final ToolItem forward = new ToolItem(navBar, SWT.PUSH);
                forward.setText(" Forward  ->");
                forward.setEnabled(false);

                /*
                 * Add an html browser.
                 */
                try {
                    browser = new Browser(comp, SWT.NONE);
                } catch (SWTError e1) {
                    System.out.println("Could not instantiate Browser: "
                            + e1.getMessage());
                    helpShell.dispose();
                    return;
                }

                GridData data = new GridData(GridData.FILL_BOTH);
                browser.setLayoutData(data);

                /*
                 * Add the listeners for the "back" and "forward" buttons.
                 */
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
                        Browser browser = (Browser) event.widget;
                        back.setEnabled(browser.isBackEnabled());
                        forward.setEnabled(browser.isForwardEnabled());
                    }

                    public void changing(LocationEvent event) {
                    }
                };
                browser.addLocationListener(locationListener);
            }

            /*
             * Load the page into the browser.
             */
            browser.setUrl(url);

            /*
             * If a new window is being created, set its size to what it was the
             * when the previous window was closed.
             */
            if (setSize) {
                if (HelpButton.location != null) {
                    helpShell.setLocation(HelpButton.location);
                }
                if (HelpButton.size != null) {
                    helpShell.setSize(HelpButton.size);
                }
            }
            helpShell.open();
            helpShell.forceFocus();
        }

        public void widgetDefaultSelected(SelectionEvent e) {
            widgetSelected(e);
        }
    }

    static class HelpShellListener implements ShellListener {

        public void shellActivated(ShellEvent e) {
            // TODO Auto-generated method stub
//            System.out.println("shellActivated") ;
            
        }

        public void shellClosed(ShellEvent e) {
            // TODO Auto-generated method stub
//            System.out.println("shellClosed") ;
        }

        public void shellDeactivated(ShellEvent e) {
//            System.out.println("shellDeActivated") ;
            
        }

        public void shellDeiconified(ShellEvent e) {
            // TODO Auto-generated method stub
//            System.out.println("shellDeiconified") ;
        }

        public void shellIconified(ShellEvent e) {
            // TODO Auto-generated method stub
//            System.out.println("shellIconified") ;
            
        }
        
    }
    static class HelpWindowDisposeListener implements DisposeListener {
//        DecomposeProofHandler commandHandler;

//        WindowDisposeListener(DecomposeProofHandler handler) {
//            commandHandler = handler;

//        }

        public void widgetDisposed(DisposeEvent e) {
            HelpButton.location = helpShell.getLocation();
            HelpButton.size = helpShell.getSize();
            HelpButton.helpShell = null ;
            
            
            
        }
    }

}
