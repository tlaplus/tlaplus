package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.jface.viewers.ITableColorProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;

/**
 * An abstract superclass for label providers.
 */
public abstract class AbstractTableLabelProvider
		extends LabelProvider
		implements ITableLabelProvider, ITableColorProvider {
	private final int m_minimumWidth;
	private final String[] m_columnTitles;
	private final double[] m_columnWidthPercentages;
	
	protected AbstractTableLabelProvider(final int minWidth, final String[] titles, final double[] percentages) {
		m_minimumWidth = minWidth;
		m_columnTitles = titles;
		m_columnWidthPercentages = percentages;
	}
	
	/**
	 * @return the minimum required width of all columns provided
	 */
	public int getMinimumTotalWidth() {
		return m_minimumWidth;
	}

	/**
	 * @param columnIndex the index of the column for which the title is desired
	 * @return the title for the column at the specified index, or null if the index is out of bounds
	 */
	public String getColumnTitle(final int columnIndex) {
		if ((columnIndex >= 0) && (columnIndex < m_columnTitles.length)) {
			return m_columnTitles[columnIndex];
		}
		
		return null;
	}
	
	/**
	 * This method will be invoked when the table's size is changing; the provider should size the columns
	 * 	appropriately.
	 * 
	 * @param newTableWidth the new size for the table
	 */
	public void resizeColumns(final int newTableWidth, final Table table) {
		double tableWidth = (double)newTableWidth;
		int currentWidthSum = 0;
		
		for (int i = 0; i < (m_columnWidthPercentages.length - 1); i++) {
			final TableColumn column = table.getColumn(i);
			final int newWidth = (int)(m_columnWidthPercentages[i] * tableWidth);
			
			column.setWidth(newWidth);
			currentWidthSum += newWidth;
		}
		
		final TableColumn column = table.getColumn(m_columnWidthPercentages.length - 1);
		column.setWidth(newTableWidth - currentWidthSum);
	}
}
