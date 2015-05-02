/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.ui.view;

import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.resource.ColorDescriptor;
import org.eclipse.jface.resource.FontDescriptor;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.resource.LocalResourceManager;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.help.IWorkbenchHelpSystem;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

/**
 * The toolbox view that is shown when no spec is loaded.
 * @author Daniel Ricketts
 * @version $Id$
 */
public class ToolboxWelcomeView extends ViewPart
{
	public ToolboxWelcomeView() {
	}

    private Composite parentComposite;

    public static final String ID = "toolbox.view.ToolboxWelcomeView";

    public void createPartControl(Composite parent)
    {
        parentComposite = parent;

        createControl(parent);
        
        UIHelper.setHelp(parent, "WelcomeView");
    }
    
    public static void createControl(Composite container) {
        Composite outerContainer = new Composite(container, SWT.NONE);

        // The local resource manager takes care of disposing images, fonts and colors when
        // the outerContainer Composite is disposed.
		final LocalResourceManager localResourceManager = new LocalResourceManager(JFaceResources.getResources(),
				outerContainer);

		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 2;
		outerContainer.setLayout(gridLayout);
		final Color backgroundColor = localResourceManager.createColor(ColorDescriptor.createFrom(new RGB(255, 255, 228)));
		outerContainer.setBackground(backgroundColor);

        /* Logo */
        final Label lblImage = new Label(outerContainer, SWT.NONE);
        lblImage.setText("Invisible text");
		final Bundle bundle = FrameworkUtil.getBundle(ToolboxWelcomeView.class);
		final URL url = FileLocator.find(bundle, new Path("images/splash_small.bmp"), null);
		final ImageDescriptor logoImage = ImageDescriptor.createFromURL(url);
        lblImage.setImage(localResourceManager.createImage(logoImage));
        
        /* Welcome header */
        final Label lblHeader = new Label(outerContainer, SWT.WRAP);
        
        // Double its font size
        final FontDescriptor headerFontDescriptor = JFaceResources.getHeaderFontDescriptor();
        final FontData fontData = headerFontDescriptor.getFontData()[0];
		lblHeader.setFont(localResourceManager.createFont(headerFontDescriptor.setHeight(fontData.getHeight() * 2)));
		
        // Color value (taken from old style.css)
		lblHeader.setForeground(localResourceManager.createColor(new RGB(0, 0, 192)));
        
        lblHeader.setLayoutData(new GridData(SWT.LEFT, SWT.BOTTOM, true, false, 1, 1));
        lblHeader.setText("Welcome to the TLA\u207A Toolbox");
        lblHeader.setBackground(backgroundColor);
        
        /* What is next section */
        
        Label lblSeparator = new Label(outerContainer, SWT.NONE);
        lblSeparator.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, false, false, 2, 1));
        
        final StyledText styledWhatIsNext = new StyledText(outerContainer, SWT.WRAP | SWT.CENTER);
        styledWhatIsNext.setBackground(backgroundColor);
        final String whatIsnext = "There is no specification open. Click on Help if you're not sure what you should do next.";
        styledWhatIsNext.setText(whatIsnext);
        GridData gd_styledWhatIsNext = new GridData( GridData.FILL_HORIZONTAL);
        gd_styledWhatIsNext.horizontalAlignment = SWT.LEFT;
        gd_styledWhatIsNext.horizontalSpan = 2;
        styledWhatIsNext.setLayoutData(gd_styledWhatIsNext);
        
		StyleRange winStyle = new StyleRange();
		winStyle.underline = true;
		winStyle.underlineStyle = SWT.UNDERLINE_LINK;
		
		int[] winRange = {whatIsnext.indexOf("Help"), "Help".length()}; 
		StyleRange[] winStyles = {winStyle};
		styledWhatIsNext.setStyleRanges(winRange, winStyles);

		// link styled text to getting started guide
		styledWhatIsNext.addListener(SWT.MouseDown, new Listener() {
			public void handleEvent(Event event) {
        		IWorkbenchHelpSystem helpSystem = PlatformUI.getWorkbench().getHelpSystem();
        		helpSystem.displayHelpResource("/org.lamport.tla.toolbox.doc/html/contents.html");
			}
		});
        
//        Composite composite = new Composite(outerContainer, SWT.NONE);
//        composite.setLayout(new GridLayout(2, false));
//        composite.setLayoutData(new GridData(SWT.FILL, SWT.TOP, true, true, 2, 1)); //SWT.FILL, SWT.CENTER, false, false, 2, 1));
        
        /* Getting started text */
        
        final StyledText styledGettingStarted = new StyledText(outerContainer, SWT.WRAP | SWT.CENTER);
        styledGettingStarted.setBackground(backgroundColor);
        final String lblString = "If this is the first time you have used the Toolbox, please read the Getting Started guide.";
		styledGettingStarted.setText(lblString);
        GridData gd_styledGettingStarted = new GridData( GridData.FILL_HORIZONTAL);
        gd_styledGettingStarted.horizontalAlignment = SWT.LEFT;
        gd_styledGettingStarted.horizontalSpan = 2;
        styledGettingStarted.setLayoutData(gd_styledGettingStarted);
        new Label(outerContainer, SWT.NONE);
        new Label(outerContainer, SWT.NONE);
        
		StyleRange style = new StyleRange();
		style.underline = true;
		style.underlineStyle = SWT.UNDERLINE_LINK;
		
		int[] range = {lblString.indexOf("Getting Started"), "Getting Started".length()}; 
		StyleRange[] styles = {style};
		styledGettingStarted.setStyleRanges(range, styles);

		// link styled text to getting started guide
		styledGettingStarted.addListener(SWT.MouseDown, new Listener() {
			public void handleEvent(Event event) {
        		IWorkbenchHelpSystem helpSystem = PlatformUI.getWorkbench().getHelpSystem();
        		helpSystem.displayHelpResource("/org.lamport.tla.toolbox.doc/html/gettingstarted/gettingstarted.html");
			}
		});
        
// This shows a help button next to the styled text		
//        final Button helpButton = new Button(composite, SWT.PUSH);
//        helpButton.setLayoutData(new GridData(SWT.CENTER, SWT.CENTER, false, false, 1, 1));
//        helpButton.setSize(36, 36);
//        helpButton.setText ("");
//        helpButton.setImage(PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_LCL_LINKTO_HELP));
//        helpButton.addListener (SWT.Selection, new Listener () {
//        	public void handleEvent (Event event) {
//        		IWorkbenchHelpSystem helpSystem = PlatformUI.getWorkbench().getHelpSystem();
////				helpSystem.displayHelp("org.lamport.tla.toolbox.GettingStarted");
////				helpSystem.displayHelpResource("/org.lamport.tla.toolbox.doc/html/contents.html");
//        		helpSystem.displayHelpResource("/org.lamport.tla.toolbox.doc/html/gettingstarted/gettingstarted.html");
//        	}
//        });
		
		/* Toolbox version */
		final Label verticalFillUp = new Label(outerContainer, SWT.NONE);
		verticalFillUp.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, true, 2, 1));
		verticalFillUp.setBackground(backgroundColor);
		
		final Label horizontalLine = new Label(outerContainer, SWT.SEPARATOR | SWT.HORIZONTAL);
		horizontalLine.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 2, 1));
		
		final Label lblVersion = new Label(outerContainer, SWT.WRAP);
		lblVersion.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 2, 1));
		lblVersion.setText("Version 1.5.0  of 2 May 2015");
		lblVersion.setBackground(backgroundColor);
    }

    public void setFocus()
    {
        if (parentComposite != null)
        {
        	parentComposite.setFocus();
        }
    }

}
