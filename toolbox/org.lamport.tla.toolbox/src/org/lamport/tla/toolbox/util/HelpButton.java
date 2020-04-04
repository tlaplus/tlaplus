package org.lamport.tla.toolbox.util;

import java.io.File;
import java.io.IOException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Platform;
import org.eclipse.swt.SWT;
import org.eclipse.swt.SWTError;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.browser.LocationEvent;
import org.eclipse.swt.browser.LocationListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.osgi.framework.Bundle;

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
     * 
     * @param parent    Where the button should be added.
     * @param helpFile  The suffix of the URL of the help page, which follows
     *                  .../org.lamport.tla.toolbox.doc/html/ -- for example,
     *                  "model/overview-page.html#what-to-check" .             
     * @return A Button that has been added to the Composite that, when clicked
     *         raises a browser window on the specified help page URL.
     */
    public static Button helpButton(final Composite parent, final String helpFile) {
    	final Button button = new Button(parent, SWT.NONE);
    	final HelpButtonListener listener = new HelpButtonListener(parent, helpFile);
        button.addSelectionListener(listener);
        button.setImage(PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_LCL_LINKTO_HELP));
        final GridData gridData = new GridData();
        gridData.verticalAlignment = SWT.TOP;
        button.setLayoutData(gridData);
        button.setEnabled(true);
        return button;
    }

    
	private static class HelpButtonListener extends SelectionAdapter implements SelectionListener {
        private final String url;
        
        private Browser browser = null;
        private Shell helpShell = null;
        private Point location = null ;
        private Point size = null ;

        HelpButtonListener(final Composite parent, final String helpFile) {
            final String file = helpFile;
            /*
             * For a helpFile like "foo.html#section", set fileName to
             * "foo.html" and suffix to "#section".  If there is no
             * such suffix, then set fileName to file and suffix to "".
             */
            String fileName = file;
            String suffix = "" ;
            final int idx = fileName.indexOf("#") ;
            if (idx != -1) {
                suffix = fileName.substring(idx) ;
                fileName = fileName.substring(0, idx) ;
            }
            final Bundle bundle = Platform.getBundle("org.lamport.tla.toolbox.doc");
            /* 
             * The bundle .tla.toolbox does not explicitly depend on .toolbox.doc.
             * Thus, it's possible that the application is running without documentation
             * which results in the variable bundle being null.
             */
            String urlString = null;
            if (bundle == null) {
                urlString = "http://tla.msr-inria.inria.fr/tlatoolbox/doc/" + file ;
                System.out.println("Could not find local copy of help file.");
            } else {
            	final URL fileURL = bundle.getEntry("html/" + fileName);
            	File theFile = null;
            	try {
            		theFile = new File(FileLocator.resolve(fileURL).getFile());
            	} catch (IOException e1) {
            		e1.printStackTrace();
            	}
            	if (theFile != null) {
            		urlString = theFile.getPath() + suffix;
            	}
            	if ((theFile == null) || (urlString == null)) {
            		urlString = "http://tla.msr-inria.inria.fr/tlatoolbox/doc/" + file ;
            		System.out.println("Could not find local copy of help file.");
            	}
            }
            
            url = urlString;
        }
        
        /**
         * This method is called when the `?' button is clicked. It opens the
         * page in the current help window if there is one, otherwise it raises
         * a new window at the position and with the size of the window the last
         * time it was closed in the current execution of the Toolbox.
         */
        @Override
        public void widgetSelected(final SelectionEvent e) {
            boolean setSize = false;

            /*
             * If the window doesn't already exist, create it and add the
             * browser.
             */
            if (helpShell == null) {
                setSize = true;

                /*
                 * Raise the window without a minimize button because minimizing
                 * puts it as a small window in a corner of the screen, not on
                 * the task bar.
                 */
				helpShell = new Shell(SWT.CLOSE | SWT.TITLE | SWT.RESIZE);
                helpShell.setText("Toolbox Help");
                helpShell.addDisposeListener((event) -> {
                    location = helpShell.getLocation();
                    size = helpShell.getSize();
                    helpShell = null;
                });
                browser = null;
                helpShell.setLayout(new FillLayout());
                final Composite comp = new Composite(helpShell, SWT.NONE);
                comp.setLayout(new GridLayout(1, false));

                /*
                 * Add the "back" and "forward" buttons.
                 */
                final ToolBar navBar = new ToolBar(comp, SWT.NONE);
				navBar.setLayoutData(new GridData(GridData.FILL_HORIZONTAL | GridData.HORIZONTAL_ALIGN_END));
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
                    System.out.println("Could not instantiate Browser: " + e1.getMessage());
                    helpShell.dispose();
                    return;
                }

                final GridData data = new GridData(GridData.FILL_BOTH);
                browser.setLayoutData(data);

                /*
                 * Add the listeners for the "back" and "forward" buttons.
                 */
                back.addListener(SWT.Selection, (event) -> {
                    browser.back();
                });
                forward.addListener(SWT.Selection, (event) -> {
                    browser.forward();
                });
                final LocationListener locationListener = new LocationListener() {
                    public void changed(LocationEvent event) {
                    	final Browser browser = (Browser) event.widget;
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
                if (location != null) {
                    helpShell.setLocation(location);
                }
                if (size != null) {
                    helpShell.setSize(size);
                }
            }
            helpShell.open();
            helpShell.forceFocus();
        }

        @Override
        public void widgetDefaultSelected(final SelectionEvent e) {
            widgetSelected(e);
        }
    }
}
