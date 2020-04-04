package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results;

import java.util.concurrent.TimeUnit;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.PaintEvent;
import org.eclipse.swt.events.PaintListener;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.lamport.tla.toolbox.tool.tlc.output.data.StateSpaceInformationItem;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * The run method of this class creates a shell (a window) to display a graph of
 * the appropriate State Space Progress information when the user clicks on a
 * column heading. It then adds a PaintListener to that shell, and that listener
 * draws the graph initially and whenever the window is resized or some other
 * event requires it to be redrawn.
 * 
 * The constructor is used to pass the arguments needed by the run method to
 * display the data.
 * 
 * Note: The location at which the shells are displayed is fixed in code buried
 * deeply. There should probably be some thought given to where to pop up the
 * window, and perhaps a window should be popped up in the same place as the
 * last such window was popped--perhaps with a bit of random variation to
 * prevent them all from piling up.
 * 
 * @author lamport
 */
class DataDisplay implements Runnable {
    private final int m_columnNumber;
    private final ResultPage m_resultPage;
    private final String m_graphTitle;

	/**
	 * The constructor returns an object with null data and times arrays if there
	 * are not at least two data points.
	 * 
	 * @param ssInfo
	 * @param columnNumber
	 */
	public DataDisplay(final int columnNumber, final ResultPage resultPage) {
		m_columnNumber = columnNumber;
		m_resultPage = resultPage;
		
		final StateSpaceLabelProvider sslp
			= (StateSpaceLabelProvider)resultPage.getStateSpaceTableViewer().getLabelProvider();
		m_graphTitle = ((columnNumber == StateSpaceLabelProvider.COL_TIME) ? "Number of Progress Reports"
																		   : sslp.getColumnTitle(columnNumber))
				+ " " + ResultPage.getGraphTitleSuffix(resultPage);
	}

	/**
	 * Much of the stuff in this run() method was copied, without much understanding
	 * from Snippet245.java in the Eclipse examples.
	 */
	public void run() {
		/*
		 * The data and times arrays are set to contain the data items to be displayed
		 * and the elapsed time (in milliseconds) at which each item was posted. The
		 * data is obtained from the appropriate column of the ssInfo items. For the
		 * Time column, the number of reports is graphed.
		 */

		// We check if a shell exists with this title, and use it if
		// it does. Otherwise, we get a new shell.
		final Display display = UIHelper.getCurrentDisplay();
		boolean shellExists = false;
		Shell theShell = null;
		for (final Shell shell : display.getShells()) {
			if (shell.getText().equals(m_graphTitle)) {
				theShell = shell;
				shellExists = true;
				break;
			}
		}
		if (!shellExists) {
			theShell = new Shell(display, SWT.SHELL_TRIM);
		}
		
		final Shell shell = theShell;
		shell.setText(m_graphTitle);
		shell.setActive(); // should cause it to pop up to the top.
		if (shellExists) {
			shell.redraw();
			shell.update();
		} else {
			shell.addPaintListener(new PaintListener() {
				public void paintControl(PaintEvent event) {
					final StateSpaceInformationItem[] ssInfo = m_resultPage.getStateSpaceInformation();
					if (ssInfo.length < 2) {
						return;
					}

					final long[] data = new long[ssInfo.length + 1];
					final long[] times = new long[ssInfo.length + 1];
					data[0] = 0;
					times[0] = 0;

					long startTime = m_resultPage.getStartTimestamp();
					TLCUIActivator.getDefault().logDebug(
							"first reported time - starttime = " + (ssInfo[0].getTime().getTime() - startTime));
					if (startTime > ssInfo[0].getTime().getTime() - 1000) {
						startTime = ssInfo[0].getTime().getTime() - 1000;
					}
					for (int i = 1; i < data.length; i++) {
						switch (m_columnNumber) {
							case StateSpaceLabelProvider.COL_TIME:
								data[i] = i - 1;
								break;
							case StateSpaceLabelProvider.COL_DIAMETER:
								data[i] = ssInfo[i - 1].getDiameter();
								break;
							case StateSpaceLabelProvider.COL_FOUND:
								data[i] = ssInfo[i - 1].getFoundStates();
								break;
							case StateSpaceLabelProvider.COL_DISTINCT:
								data[i] = ssInfo[i - 1].getDistinctStates();
								break;
							case StateSpaceLabelProvider.COL_LEFT:
								data[i] = ssInfo[i - 1].getLeftStates();
								break;
							default:
								return;
						}
						times[i] = ssInfo[i - 1].getTime().getTime() - startTime;
					}

					final Rectangle rect = shell.getClientArea();
					// Set maxData to the largest data value;
					long maxData = 0;
					for (int i = 0; i < data.length; i++) {
						if (data[i] > maxData) {
							maxData = data[i];
						}
					}
					
					final long maxTime = times[times.length - 1];
					// event.gc.drawOval(0, 0, rect.width - 1, rect.height - 1);
					if (maxTime > 0) {
						final double maxTimeD = (double) maxTime;
						// In case maxData equals 0, we use 1 instead for computing
						// the coordinates of the points.
						// (Added by LL on 6 July 2011 to fix division by zero bug.)
						final double maxDataVal = (maxData == 0) ? 1 : maxData;
						final double width = (double) (rect.width - 6);
						final double height = (double) (rect.height - 6);
						final int[] pointArray = new int[2 * data.length];
						for (int i = 0; i < data.length; i++) {
							final double tFraction = (double) times[i] / maxTimeD;
							final double dFraction = (double) data[i] / maxDataVal;

							pointArray[2 * i] = (int) (tFraction * width) + 2;
							pointArray[(2 * i) + 1] = rect.height - (int) (dFraction * height) + 2;
						}
						event.gc.drawPolyline(pointArray);
					}
					String stringTime = "Time: ";
					long unreportedTime = maxTime;
					final long days = TimeUnit.MILLISECONDS.toDays(maxTime);
					if (days > 0) {
						unreportedTime = unreportedTime - TimeUnit.DAYS.toMillis(days);
						stringTime = stringTime + days + ((days == 1) ? (" day ") : (" days  "));

					}
					final long hours = TimeUnit.MILLISECONDS.toHours(unreportedTime);
					if (hours > 0) {
						unreportedTime = unreportedTime - TimeUnit.HOURS.toMillis(hours);
						stringTime = stringTime + hours + ((hours == 1) ? (" hour ") : (" hours  "));
					}
					unreportedTime = (unreportedTime + (1000 * 26)) / (1000 * 60);
					stringTime = stringTime + unreportedTime + ((unreportedTime == 1) ? (" minute ") : (" minutes  "));
					event.gc.drawString(stringTime, 0, 0);
					event.gc.drawString("Current: " + data[data.length - 1], 0, 15);
					if (maxData != data[data.length - 1]) {
						event.gc.drawString("Maximum: " + maxData, 0, 30);
					}
				}
			});
		}
		
		if (!shellExists) {
			shell.setBounds(100 + 30 * m_columnNumber, 100 + 30 * m_columnNumber, 400, 300);
		}
		
		shell.open();
		// The following code from the Eclipse example was eliminated.
		// It seems to cause the shell to survive after the Toolbox is
		// killed.
		//
		// while (!shell.isDisposed()) {
		// if (!display.readAndDispatch()) display.sleep();
		// }
	}
}
