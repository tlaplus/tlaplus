/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
 *   William Schultz - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.SWT;
import org.eclipse.swt.SWTError;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.tool.tlc.model.Model;

/**
 * View for displaying an animated TLC trace.
 * 
 * Consists of an HTML viewer that displays SVG animation frames, along with
 * handlers for arrow key events that allow a user to step backwards and
 * forwards through the animation frames.
 * 
 * @author William Schultz
 */
public class TraceAnimationView extends ViewPart {
    public static final String ID = "toolbox.tool.tlc.view.TraceAnimationView";

    private Model model;
    private List<String> svgAnimationFrames = new ArrayList<String>();
    private int currStateIndex = 0;
    private Text frameCounter;
    Browser browser;

    public TraceAnimationView() {
    }

    public void setSVGAnimationFrames(List<String> svgFrames) {
        svgAnimationFrames = svgFrames;
    }

    /**
     * Displays the first animation frame. If there are no frames, does nothing.
     */
    public void loadInitialFrame() {
        if (svgAnimationFrames.size() > 0) {
            currStateIndex = 0;
            loadFrame(currStateIndex);
        }
    }
    
    /**
     * Produces the text to be displayed by the frame counter for a given frame index.
     */
    private String frameCounterText(int frame) {
        return "State " + frame + " | Total States: " + svgAnimationFrames.size();
    }

    /**
     * Loads the frame at the specified index.
     * 
     * Assumes that the given index is within the bounds of the frame sequence.
     */
    private void loadFrame(int frameIndex) {
        Assert.isTrue(frameIndex < svgAnimationFrames.size(), "Tried to access frame index " + frameIndex
                + " even though there are only " + svgAnimationFrames.size() + " frames.");
        browser.setText(makeHTMLFrame(svgAnimationFrames.get(frameIndex)));
        frameCounter.setText(frameCounterText(frameIndex + 1));
        frameCounter.pack();
    }
    
    /**
     * Step forward or backward a single frame, depending on the value of 'dir', which can 1 or -1.
     */
    private void stepFrame(int inc) {
        
        // Move to the proper frame.
        currStateIndex += inc;

        // Don't step past the last frame.
        currStateIndex = Math.min(currStateIndex, svgAnimationFrames.size() - 1);

        // Don't step behind the first frame.
        currStateIndex = Math.max(0, currStateIndex);

        // Load the new frame.
        loadFrame(currStateIndex);
    }

    /**
     * Wraps a single SVG frame in HTML boilerplate.
     */
    private String makeHTMLFrame(String svgFrame) {
        String html = "<html><head></head><body>";
        html += "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"400\" height=\"400\" version=\"1.1\">";
        html += svgFrame;
        html += "</svg>";
        html += "</body></html>";
        return html;
    }

    /**
     * Listener that handles keypress events to step between animation frames.
     */
    class ArrowKeyListener implements KeyListener {

        // Is one of the left or right arrow keys currently pressed.
        boolean keyDown = false;

        @Override
        public void keyPressed(KeyEvent e) {

            // Do nothing if there are no frames.
            if (svgAnimationFrames.size() == 0) {
                return;
            }

            // Don't allow multiple keys to be pressed simultaneously.
            if (keyDown) {
                return;
            }

            // Step forward or backward in the animation.
            int inc = 0;
            switch (e.keyCode) {
            // Left arrow key.
            case 16777219:
                inc = -1;
                break;
                // Right arrow key.
            case 16777220:
                inc = 1;
                break;
                // Do nothing.
            default:
                return;
            }

            // We have pressed one of the left/right arrow keys.
            keyDown = true;
            
            // Move to the appropriate frame.
            stepFrame(inc);
        }

        @Override
        public void keyReleased(KeyEvent e) {
            // Left/right arrow key released.
            if (e.keyCode == 16777219 || e.keyCode == 16777220) {
                keyDown = false;
            }
        }
    }

    /**
     * Creates the HTML browser component.
     */
    public void createPartControl(Composite parent) {
        
        GridLayout gridLayout = new GridLayout();
        gridLayout.numColumns = 2;
        parent.setLayout(gridLayout);
        
        //
        // Create the browser for viewing the SVG animation frames.
        //
        
        try {
           browser = new Browser(parent, SWT.NONE);
        } catch (SWTError e) {
            System.out.println("Could not instantiate Browser: " + e.getMessage());
            return;
        }

        browser.setText("<html></html>");
        browser.addKeyListener(new ArrowKeyListener());
        
        GridData gridData = new GridData(SWT.FILL, SWT.FILL, true, true);
        gridData.horizontalSpan = 2;
        browser.setLayoutData(gridData);
        
        //
        // Create the frame counter text object.
        //
        
        Text frameCounterText = new Text(parent, SWT.NONE);
        GridData gridDataText = new GridData(SWT.CENTER, SWT.FILL, true, false);
        gridDataText.horizontalSpan = 2;
        frameCounterText.setLayoutData(gridDataText);
        frameCounterText.setText(frameCounterText(1));
        frameCounterText.pack();
        frameCounter = frameCounterText;

        //
        // Create the buttons for stepping forward and backwards through the trace.
        //
        
        final int buttonHeight = 35;
        final Button buttonPrev = new Button(parent, SWT.NONE);
        buttonPrev.setText("Prev State");
        GridData gridDataPrev = new GridData(SWT.FILL, SWT.BEGINNING, true, false);
        gridDataPrev.heightHint = buttonHeight;
        buttonPrev.setLayoutData(gridDataPrev);
        buttonPrev.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent arg0) {
                // Step back a frame.
                stepFrame(-1);
            }
         });
        
        
        final Button buttonNext = new Button(parent, SWT.NONE);
        buttonNext.setText("Next State");    
        GridData gridDataNext = new GridData(SWT.FILL, SWT.BEGINNING, true, false);
        gridDataNext.heightHint = buttonHeight;
        buttonNext.setLayoutData(gridDataNext);
        buttonNext.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent arg0) {
                // Advance the frame.
                stepFrame(1);
            }
         });
        
    }

    public void setFocus() {
        this.browser.setFocus();
    }

    public void dispose() {
    }

    public Model getModel() {
        return model;
    }
}
