package org.lamport.tla.toolbox.tool.tlc.ui.editor.provider;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.viewers.ITableFontProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;

public class FormulaLabelProvider extends LabelProvider implements ITableLabelProvider, ITableFontProvider {

	@Override
	public Font getFont(Object element, int columnIndex) {
		// Regardless of the element and its position, we want to use a monospaced font.
		return JFaceResources.getFont(JFaceResources.TEXT_FONT);
	}

	@Override
	public Image getColumnImage(Object element, int columnIndex) {
		return this.getImage(element);
	}

	@Override
	public String getColumnText(Object element, int columnIndex) {
		return this.getText(element);
	}
}
