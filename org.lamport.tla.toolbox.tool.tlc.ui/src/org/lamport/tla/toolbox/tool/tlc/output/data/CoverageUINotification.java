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
package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.Date;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.resource.ImageDescriptor;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.util.TLCUINotification;

public class CoverageUINotification extends TLCUINotification {

	private static final ImageDescriptor id = TLCUIActivator.getImageDescriptor("/icons/elcl16/quickfix_obj.png");
	
	private final ModelEditor editor;

	public CoverageUINotification(final ModelEditor editor) {
		super("Performance Hint",
				  "TLC is running with profiling enabled.\n"
				+ "Please be advised that profiling\n"
				+ "negatively impacts performance.\n"
				+ "For this reason, please consider\n"
				+ "turning profiling off on the\n"
				+ "advanced TLC options page and\n"
				+ "re-run model checking without it.",
				new Date());
		this.editor = editor;
		Assert.isNotNull(editor);
		
		setKindImage(id.createImage());
	}

	@Override
	public void open() {
		editor.addOrShowAdvancedTLCOptionsPage();
	}
}
