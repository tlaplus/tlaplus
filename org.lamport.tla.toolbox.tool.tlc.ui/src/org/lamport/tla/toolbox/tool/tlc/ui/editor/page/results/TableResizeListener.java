package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results;

import org.eclipse.swt.events.ControlAdapter;
import org.eclipse.swt.events.ControlEvent;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Table;
import org.lamport.tla.toolbox.tool.tlc.ui.util.AbstractTableLabelProvider;

/**
 * We have this listener to allow tables to resize their columns when their parent table changes size.
 */
class TableResizeListener extends ControlAdapter {
	private final AbstractTableLabelProvider m_tableLabelProvider;

	TableResizeListener (final AbstractTableLabelProvider lp) {
		m_tableLabelProvider = lp;
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public void controlResized(final ControlEvent ce) {
		final Table t = (Table)ce.getSource();
		final Rectangle size = t.getClientArea();
		int width = size.width - (2 * t.getBorderWidth());

		m_tableLabelProvider.resizeColumns(width, t);
	}
}
