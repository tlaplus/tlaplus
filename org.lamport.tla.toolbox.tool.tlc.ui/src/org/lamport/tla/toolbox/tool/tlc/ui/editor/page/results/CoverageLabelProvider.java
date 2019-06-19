package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results;

import java.util.Comparator;

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
@SuppressWarnings("unchecked")
class CoverageLabelProvider extends AbstractTableLabelProvider {
    static final String COVERAGE_COMPARATOR = "COVERAGE_COMPARATOR";
    
	static final int COL_MODULE = 0;
    static final int COL_ACTION = 1;

    static final String TOOLTIP = "Click on a row to go to action.";
    
	private static final String[] COLUMN_TITLES = new String[] { "Module", "Action" };
    private static final int[] COLUMN_WIDTHS;
    private static final Comparator<ActionInformationItem>[] COLUMN_COMP;
	private static final double[] COLUMN_WIDTH_PERCENTAGES;
    private static final int MIN_WIDTH;
    
    static {
    	final double scale = 1.0;	// future functionality: UIHelper.getDisplayScaleFactor();
    	
    	int i = 0;
    	COLUMN_WIDTHS = new int[COLUMN_TITLES.length];
    	COLUMN_WIDTHS[i++] = (int)(40.0 * scale);
    	COLUMN_WIDTHS[i++] = (int)(100.0 * scale);
    	
    	int sum = 0;
    	for (i = 0; i < COLUMN_WIDTHS.length; i++) {
    		sum += COLUMN_WIDTHS[i];
    	}
    	MIN_WIDTH = sum;
		
		COLUMN_WIDTH_PERCENTAGES = new double[COLUMN_WIDTHS.length];
		for (i = 0; i < COLUMN_WIDTHS.length; i++) {
			COLUMN_WIDTH_PERCENTAGES[i] = ((double)COLUMN_WIDTHS[i] / (double)MIN_WIDTH);
		}

		i = 0;
		COLUMN_COMP = new Comparator[COLUMN_TITLES.length];
		COLUMN_COMP[i++] = new Comparator<ActionInformationItem>() {
			@Override
			public int compare(ActionInformationItem o1, ActionInformationItem o2) {
				return o1.getModule().compareTo(o2.getModule());
			}
		}; 
		COLUMN_COMP[i++] = new Comparator<ActionInformationItem>() {
			@Override
			public int compare(ActionInformationItem o1, ActionInformationItem o2) {
				return o1.getName().compareTo(o2.getName());
			}
		}; 
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
			column.setData(COVERAGE_COMPARATOR, COLUMN_COMP[i]);

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
