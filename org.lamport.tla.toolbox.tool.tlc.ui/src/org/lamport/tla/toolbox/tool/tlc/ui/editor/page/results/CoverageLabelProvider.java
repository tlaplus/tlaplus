package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results;

import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.lamport.tla.toolbox.tool.tlc.output.data.ActionInformationItem;
import org.lamport.tla.toolbox.tool.tlc.ui.util.AbstractTableLabelProvider;

/**
 * This is the <code>LabelProvider</code> for the coverage statistics table found on the Results page.
 * 
 * @see org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results.ResultPage
 */
class CoverageLabelProvider extends AbstractTableLabelProvider {
    static final int COL_MODULE = 0;
    static final int COL_ACTION = 1;

    static final String TOOLTIP = "Click on a row to go to action.";
    
	private static final String[] COLUMN_TITLES = new String[] { "Module", "Action" };
    private static final int[] COLUMN_WIDTHS;
	private static final double[] COLUMN_WIDTH_PERCENTAGES;
    private static final int MIN_WIDTH;
    
    static {
    	final double scale = 1.0;	// future functionality: UIHelper.getDisplayScaleFactor();
    	
    	COLUMN_WIDTHS = new int[2];
    	COLUMN_WIDTHS[0] = (int)(40.0 * scale);
    	COLUMN_WIDTHS[1] = (int)(100.0 * scale);
    	
    	MIN_WIDTH = COLUMN_WIDTHS[0] + COLUMN_WIDTHS[1];
		
		COLUMN_WIDTH_PERCENTAGES = new double[3];
		for (int i = 0; i < COLUMN_WIDTHS.length; i++) {
			COLUMN_WIDTH_PERCENTAGES[i] = ((double)COLUMN_WIDTHS[i] / (double)MIN_WIDTH);
		}
    }

    
    CoverageLabelProvider() {
    	super(MIN_WIDTH, COLUMN_TITLES, COLUMN_WIDTH_PERCENTAGES);
    }

	/**
	 * @param stateTable
	 */
	void createTableColumns(final Table stateTable, final TableColumnLayout layout) {
		for (int i = 0; i < COLUMN_TITLES.length; i++) {
			final TableColumn column = new TableColumn(stateTable, SWT.NULL);
			column.setWidth(COLUMN_WIDTHS[i]);
			column.setText(COLUMN_TITLES[i]);
			column.setToolTipText(TOOLTIP);

			final int weight = (int)(100.0 * COLUMN_WIDTH_PERCENTAGES[i]);
			layout.setColumnData(column, new ColumnWeightData(weight, COLUMN_WIDTHS[i], true));
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
	public String getColumnText(final Object element, final int columnIndex) {
		if (element instanceof ActionInformationItem) {
			final ActionInformationItem item = (ActionInformationItem) element;
			
			switch (columnIndex) {
				case COL_MODULE:
					return item.getModule();
				case COL_ACTION:
					return String.format("%s (%s)", item.getName(), item.getLocation());
			}
		}
		return null;
	}

	public Color getForeground(final Object element, final int columnIndex) {
		return null; // Use default color
	}

	public Color getBackground(final Object element, final int columnIndex) {
		return null;
	}
}
