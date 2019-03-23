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
import org.eclipse.swt.widgets.Composite;
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
     * Loads the frame at the specified index.
     * 
     * Assumes that the given index is within the bounds of the frame sequence.
     */
    private void loadFrame(int frameIndex) {
        Assert.isTrue(frameIndex < svgAnimationFrames.size(), "Tried to access frame index " + frameIndex
                + " even though there are only " + svgAnimationFrames.size() + " frames.");
        browser.setText(makeHTMLFrame(svgAnimationFrames.get(frameIndex)));
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

            // Advance the frame.
            currStateIndex += inc;

            // Don't step past the last frame.
            currStateIndex = Math.min(currStateIndex, svgAnimationFrames.size() - 1);

            // Don't step behind the first frame.
            currStateIndex = Math.max(0, currStateIndex);

            // Load the new frame.
            loadFrame(currStateIndex);
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
        try {
            browser = new Browser(parent, SWT.RESIZE);
            browser.setBounds(0, 0, 2000, 2000);
            browser.setSize(700, 900);
        } catch (SWTError e) {
            System.out.println("Could not instantiate Browser: " + e.getMessage());
            return;
        }

        browser.setText("<html></html>");
        browser.addKeyListener(new ArrowKeyListener());
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
