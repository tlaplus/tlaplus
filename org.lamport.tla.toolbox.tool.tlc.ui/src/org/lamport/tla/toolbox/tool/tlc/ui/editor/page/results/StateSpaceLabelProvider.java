package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results;

import java.text.NumberFormat;
import java.util.concurrent.TimeUnit;

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.lamport.tla.toolbox.tool.tlc.output.data.StateSpaceInformationItem;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.util.AbstractTableLabelProvider;

/**
 * This is the <code>LabelProvider</code> for the state space statistics table found on the Results page.
 * 
 * @see org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results.ResultPage
 */
class StateSpaceLabelProvider extends AbstractTableLabelProvider {
	static final int COL_TIME = 0;
	static final int COL_DIAMETER = 1;
	static final int COL_FOUND = 2;
	static final int COL_DISTINCT = 3;
	static final int COL_LEFT = 4;

	private static final String[] COLUMN_TITLES
			= new String[] { "Time", "Diameter", "States Found", "Distinct States", "Queue Size" };
	private static final String NO_DATA_TEXT = "--";
	private static final int[] COLUMN_WIDTHS;
	private static final double[] COLUMN_WIDTH_PERCENTAGES;
	private static final int MIN_WIDTH;

	static {
		final double scale = 1.0; // future functionality: UIHelper.getDisplayScaleFactor();

		COLUMN_WIDTHS = new int[5];
		COLUMN_WIDTHS[0] = (int) (120.0 * scale);
		COLUMN_WIDTHS[1] = (int) (60.0 * scale);
		COLUMN_WIDTHS[2] = (int) (80.0 * scale);
		COLUMN_WIDTHS[3] = (int) (100.0 * scale);
		COLUMN_WIDTHS[4] = (int) (80.0 * scale);

		MIN_WIDTH = COLUMN_WIDTHS[0] + COLUMN_WIDTHS[1] + COLUMN_WIDTHS[2] + COLUMN_WIDTHS[3] + COLUMN_WIDTHS[4];
		
		COLUMN_WIDTH_PERCENTAGES = new double[5];
		for (int i = 0; i < 5; i++) {
			COLUMN_WIDTH_PERCENTAGES[i] = ((double)COLUMN_WIDTHS[i] / (double)MIN_WIDTH);
		}
	}

	private static String formatInterval(final long firstTS, final long secondTS) {
		final long interval = secondTS - firstTS;
		final long hr = TimeUnit.MILLISECONDS.toHours(interval);
		final long min = TimeUnit.MILLISECONDS.toMinutes(interval - TimeUnit.HOURS.toMillis(hr));
		final long sec = TimeUnit.MILLISECONDS
				.toSeconds(interval - TimeUnit.HOURS.toMillis(hr) - TimeUnit.MINUTES.toMillis(min));
		
		return String.format("%02d:%02d:%02d", hr, min, sec);
	}

	
	private boolean m_doHighlight;
	private final ResultPage m_resultPage;

	StateSpaceLabelProvider(final ResultPage resultPage) {
		super(MIN_WIDTH, COLUMN_TITLES, COLUMN_WIDTH_PERCENTAGES);
		
		m_doHighlight = false;
		m_resultPage = resultPage;
	}

	/**
	 * @param stateTable
	 */
	void createTableColumns(final Table stateTable, final ResultPage page) {
		for (int i = 0; i < COLUMN_TITLES.length; i++) {
			final TableColumn column = new TableColumn(stateTable, SWT.NULL);
			column.setWidth(COLUMN_WIDTHS[i]);
			column.setText(COLUMN_TITLES[i]);

			// The following statement attaches a listener to the column header.
			//	See the ResultPageColumnListener comments.
			column.addSelectionListener(new ResultPageColumnListener(i, page));
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnImage(java.lang.Object, int)
	 */
	@Override
	public Image getColumnImage(final Object element, final int columnIndex) {
		return null;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnText(java.lang.Object, int)
	 */
	@Override
	public String getColumnText(final Object element, final int columnIndex) {
		if (element instanceof StateSpaceInformationItem) {
			// the "N/A" values are used for simulation mode
			final NumberFormat nf = NumberFormat.getIntegerInstance();
			final StateSpaceInformationItem item = (StateSpaceInformationItem) element;
			
			switch (columnIndex) {
				case COL_TIME:
					return formatInterval(m_resultPage.getStartTimestamp(), item.getTime().getTime());
				case COL_DIAMETER:
					if (item.getDiameter() >= 0) {
						return nf.format(item.getDiameter());
					} else {
						return NO_DATA_TEXT;
					}
				case COL_FOUND:
					return nf.format(item.getFoundStates());
				case COL_DISTINCT:
					if (item.getDistinctStates() >= 0) {
						return nf.format(item.getDistinctStates());
					} else {
						return NO_DATA_TEXT;
					}

				case COL_LEFT:
					if (item.getLeftStates() >= 0) {
						return nf.format(item.getLeftStates());
					} else {
						return NO_DATA_TEXT;
					}
			}
		}
		
		return null;
	}

	@Override
	public Color getForeground(final Object element, final int columnIndex) {
		return null; // Use default color
	}

	@Override
	public Color getBackground(final Object element, final int columnIndex) {
		final StateSpaceInformationItem ssii = (StateSpaceInformationItem) element;
		if (m_doHighlight && (columnIndex == COL_LEFT) && ssii.isMostRecent()) {
			return TLCUIActivator.getColor(SWT.COLOR_RED);
		}
		return null;
	}

//	Font getFont(final Object element, final int columnIndex) {
//		final StateSpaceInformationItem ssii = (StateSpaceInformationItem) element;
//		if (m_doHighlight && (columnIndex == COL_LEFT) && ssii.isMostRecent()) {
//			return JFaceResources.getFontRegistry().getBold(JFaceResources.DEFAULT_FONT);
//		}
//		return null;
//	}
//
	void setHighlightUnexplored() {
		m_doHighlight = true;
	}

	void unsetHighlightUnexplored() {
		m_doHighlight = false;
	}
}
