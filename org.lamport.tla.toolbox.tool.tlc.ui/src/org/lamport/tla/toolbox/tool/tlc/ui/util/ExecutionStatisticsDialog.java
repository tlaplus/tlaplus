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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.ui.util;

import static org.eclipse.swt.events.SelectionListener.widgetSelectedAdapter;

import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

import util.ExecutionStatisticsCollector;
import util.ExecutionStatisticsCollector.Selection;

public class ExecutionStatisticsDialog extends MessageDialog {

	private static final String KEY = "BUTTON_KEY";
	
	private final ExecutionStatisticsCollector esc = new ExecutionStatisticsCollector();

	private final boolean isUserTriggered;

	public ExecutionStatisticsDialog(boolean isUserTriggered, final Shell parentShell) {
		super(parentShell, "TLA+ execution statistics", (Image) null, "The TLA+ project needs your help!",
				MessageDialog.QUESTION, new String[0], 0);
		this.isUserTriggered = isUserTriggered;
		
		// Do not block the Toolbox's main window.
		setShellStyle(getShellStyle() ^ SWT.APPLICATION_MODAL | SWT.MODELESS);
		setBlockOnOpen(false);
	}

    /* (non-Javadoc)
     * @see org.eclipse.jface.dialogs.MessageDialog#createButtonsForButtonBar(org.eclipse.swt.widgets.Composite)
     */
    @Override
	protected void createButtonsForButtonBar(final Composite parent) {
        final Button[] buttons = new Button[3];
        buttons[0] = createButton(parent, 0, "&Always Share\nExecution Statistics", false);
        buttons[0].setData(KEY, ExecutionStatisticsCollector.Selection.ON);
        buttons[1] = createButton(parent, 1, "Share Without\n&Installation Identifier", false);
        buttons[1].setData(KEY, ExecutionStatisticsCollector.Selection.RANDOM_IDENTIFIER);
        buttons[2] = createButton(parent, 2, "&Never Share\nExecution Statistics", false);
        buttons[2].setData(KEY, ExecutionStatisticsCollector.Selection.NO_ESC);
        
		// Disable the button for the currently active selection to indicate the state
		// if this dialog is (explicitly) triggered by the user due to clicking the menu
		// item.
		// However, if this dialog is automatically opened by a fresh Toolbox install,
		// we don't indicate the state. Technically the state is NO_ESC but the UI gives
		// the impression it is impossible to disable exec stats.
        if (isUserTriggered) {
        	final Selection selection = esc.get();
        	switch (selection) {
        	case ON:
        		buttons[0].setEnabled(false);
        		break;
        	case RANDOM_IDENTIFIER:
        		buttons[1].setEnabled(false);
        		break;
        	case NO_ESC:
        		buttons[2].setEnabled(false);
        	}
        }
        
        setButtons(buttons);
    }
    
	/* (non-Javadoc)
	 * @see org.eclipse.jface.dialogs.MessageDialog#createButton(org.eclipse.swt.widgets.Composite, int, java.lang.String, boolean)
	 */
	protected Button createButton(Composite parent, int id, String label, boolean defaultButton) {
		// increment the number of columns in the button bar
		((GridLayout) parent.getLayout()).numColumns++;
		Button button = new Button(parent, SWT.PUSH | SWT.WRAP); // Need wrap here contrary to Dialog#createButton to wrap button label on Windows and macOS(?).
		button.setText(label);
		button.setFont(JFaceResources.getDialogFont());
		button.setData(Integer.valueOf(id));
		button.addSelectionListener(widgetSelectedAdapter(event -> buttonPressed(((Integer) event.widget.getData()).intValue())));
		if (defaultButton) {
			Shell shell = parent.getShell();
			if (shell != null) {
				shell.setDefaultButton(button);
			}
		}
		setButtonLayoutData(button);
		return button;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.dialogs.MessageDialog#createCustomArea(org.eclipse.swt.widgets.Composite)
	 */
	@Override
    protected Control createCustomArea(Composite parent) {
		final Composite c = new Composite(parent, SWT.BORDER);
		c.setLayout(new GridLayout());
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		final String txt = String.format("%s"
				+ "* Total number of cores and cores assigned to TLC\n"
				+ "* Heap and off-heap memory allocated to TLC\n"
				+ "* TLC's version (git commit SHA)\n"
				+ "* If breadth-first search, depth-first search or simulation mode is active\n"
				+ "* TLC's implementation for the sets of seen and unseen states\n"
				+ "* If TLC has been launched from the TLA Toolbox\n"
				+ "* Name, version, and architecture of your operating system\n"
				+ "* Vendor, version, and architecture of your Java virtual machine\n"
				+ "* The current date and time\n"
				+ "* An installation identifier which allows us to group execution statistics\n\n"
				+ "The execution statistics do not contain personal information. If you wish to revoke\n"
				+ "your consent to share execution statistics at a later point, please chose \n"
				+ "\"Never Share Execution Statistics\" below by re-opening this dialog via\n"
				+ "Help > Opt In/Out Execution Statistics accessible from the Toolbox's main menu.", prettyPrintSelection2(esc));
		
		final StyledText st = new StyledText(c, SWT.SHADOW_NONE | SWT.WRAP);
		st.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		st.setEnabled(true);
		st.setEditable(false);
		st.setText(txt);
		
		final StyleRange[] ranges = new StyleRange[3];
		ranges[0] = new StyleRange(txt.indexOf("(TLC) execution statistics"), "(TLC) execution statistics".length(), null, null);
		ranges[0].underline = true;
		ranges[0].underlineStyle = SWT.UNDERLINE_LINK;
		ranges[0].data = "https://exec-stats.tlapl.us";
		
		ranges[1] = new StyleRange(txt.indexOf("publicly available"), "publicly available".length(), null, null);
		ranges[1].underline = true;
		ranges[1].underlineStyle = SWT.UNDERLINE_LINK;
		ranges[1].data = "https://exec-stats.tlapl.us/tlaplus.csv";
				
		ranges[2] = new StyleRange(txt.indexOf("git commit SHA"), "git commit SHA".length(), null, null);
		ranges[2].underline = true;
		ranges[2].underlineStyle = SWT.UNDERLINE_LINK;
		ranges[2].data = "https://git-scm.com/book/en/v2/Git-Internals-Git-Objects";

		st.setStyleRanges(ranges);
		st.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseUp(final MouseEvent event) {
                final int offset = st.getOffsetAtPoint(new Point(event.x, event.y));
                if (offset < 0 || offset >= st.getCharCount()) {
                	return;
                }
				final StyleRange style = st.getStyleRangeAtOffset(offset);
                if (style != null && style.underline && style.underlineStyle == SWT.UNDERLINE_LINK && style.data instanceof String) {
                    try {
						PlatformUI.getWorkbench().getBrowserSupport().getExternalBrowser().openURL(new URL((String) style.data));
					} catch (PartInitException | MalformedURLException notExpectedToHappen) {
						notExpectedToHappen.printStackTrace();
					}
                }
			}
		});
	
        return c;
    }

	private static String prettyPrintSelection2(final ExecutionStatisticsCollector esc) {
		switch (esc.get()) {
		case ON:
			return String.format(
					"Thank you for sharing (TLC) execution statistics with installation identifier\n%s.\n\nExecution Statistics help us make informed decisions about future research and\ndevelopment directions. Execution statistics are made publicly available on the\nweb and contain the following information:\n\n",
					esc.getIdentifier());
		case RANDOM_IDENTIFIER:
			return "Thank you for sharing (TLC) execution statistics. Execution Statistics help us\nmake informed decisions about future research and development directions.\nExecution statistics are made publicly available on the web and contain the\nfollowing information:\n\n";
		}
		return "Please opt-in and share (TLC) execution statistics. "
				+ "Execution statistics are made\npublicly available on the web "
				+ "and contain the following information:\n\n";
	}

	@Override
	protected void buttonPressed(final int buttonId) {
		final ExecutionStatisticsCollector.Selection col = (Selection) getButton(buttonId).getData(KEY);
		final Job j = new Job("Write Execution Statistics Preference.") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				try {
					esc.set(col);
				} catch (IOException e) {
					return new Status(ERROR, TLCUIActivator.PLUGIN_ID, e.getMessage(), e);
				}
				return Status.OK_STATUS;
			}
		};
		j.schedule();

		super.buttonPressed(buttonId);
	}
}
