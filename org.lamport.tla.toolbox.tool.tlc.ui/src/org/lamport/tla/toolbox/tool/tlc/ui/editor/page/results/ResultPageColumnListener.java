package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results;

import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A ResultPageColumnListener is a listener that handles clicks on
 * the column headers of the "State space progress" region of the
 * Result Page.  The same class is used for all the column
 * headers, with the column number indicating which column header
 * was clicked on.
 * 
 * @author lamport
 */
class ResultPageColumnListener implements SelectionListener {
	private final int m_columnNumber;
	private final ResultPage m_resultPage;

	public ResultPageColumnListener(final int columnNumber, final ResultPage resultPage) {
		m_columnNumber = columnNumber;
		m_resultPage = resultPage;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.
	 * swt.events.SelectionEvent)
	 */
	@Override
	public void widgetDefaultSelected(final SelectionEvent se) { }

	/**
	 * This is called when the user clicks on the header of a column of the "State
	 * space progress" region of the ResultsPage. It raises a window with a graph of
	 * the specified column.
	 */
	@Override
	public void widgetSelected(final SelectionEvent se) {
		UIHelper.runUIAsync(new DataDisplay(m_columnNumber, m_resultPage));
	}
}
