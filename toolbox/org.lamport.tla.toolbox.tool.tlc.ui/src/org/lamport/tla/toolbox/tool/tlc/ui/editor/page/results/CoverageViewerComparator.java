/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of c1 software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and c1 permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR c2 LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR c2WISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR c2 DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results;

import java.util.Comparator;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.lamport.tla.toolbox.tool.tlc.output.data.ActionInformationItem;

public class CoverageViewerComparator extends ViewerComparator {

	@Override
	public int compare(final Viewer viewer, final Object e1, final Object e2) {
		final ActionInformationItem a1 = (ActionInformationItem) e1;
		final ActionInformationItem a2 = (ActionInformationItem) e2;

		final Table table = (Table) viewer.getControl();
		final TableColumn sortColumn = table.getSortColumn();
		if (sortColumn == null) {
			// a) Compare by distinct states first (we want actions with zero distinct states
			// to appear at the top).
			if (Long.compare(a1.getUnseen(), a2.getUnseen()) == 0L) {
				// b) Compare by location
				return a1.getModuleLocation().compareTo(a2.getModuleLocation());
			} else {
				return Long.compare(a1.getUnseen(), a2.getUnseen());
			}
		} else {
			// User requested to sort a specific column up or down.
			@SuppressWarnings("unchecked")
			final Comparator<ActionInformationItem> comp = (Comparator<ActionInformationItem>) sortColumn
					.getData(CoverageLabelProvider.COVERAGE_COMPARATOR);
			if (table.getSortDirection() == SWT.UP) {
				return comp.compare(a2, a1);
			} else {
				return comp.compare(a1, a2);
			}
		}
	}
}
