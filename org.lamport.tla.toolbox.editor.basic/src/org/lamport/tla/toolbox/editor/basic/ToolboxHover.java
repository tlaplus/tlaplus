/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.lamport.tla.toolbox.editor.basic.pcal.PCalWordDetector;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper.WordRegion;
import org.lamport.tla.toolbox.tool.ToolboxHandle;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.SymbolNode;

public class ToolboxHover implements ITextHover {
	
	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.ITextHover#getHoverInfo(org.eclipse.jface.text.ITextViewer, org.eclipse.jface.text.IRegion)
	 */
	public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
		// Expand the given region to word (token) and get the token. If it can't get
		// the token, no hover help is provided.
		final WordRegion wordRegion;
		try {
			wordRegion = DocumentHelper.getRegionExpandedBoth(textViewer.getDocument(),
					hoverRegion.getOffset(), new PCalWordDetector());
		} catch (BadLocationException ignore) {
			return null;
		}

		final String hoverInfo = getHoverInfo(textViewer.getDocument(), wordRegion);
		if (hoverInfo != null) {
			return hoverInfo;
		}

		// No keywords, lets look for operator definitions. For that, the spec has to be
		// in parsed state.
		final SpecObj spec = ToolboxHandle.getSpecObj();
		if (spec != null) { // null if spec hasn't been parsed.
			final SymbolNode symbol = EditorUtil.lookupSymbol(spec, textViewer.getDocument(), wordRegion);
			if (symbol == null) {
				return null;
			}
			return symbol.getHumanReadableImage();
		}
		return null;
	}
	
	protected String getHoverInfo(IDocument document, WordRegion wordRegion) {
		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.ITextHover#getHoverRegion(org.eclipse.jface.text.ITextViewer, int)
	 */
	public IRegion getHoverRegion(ITextViewer textViewer, int offset) {
		return new Region(offset, 0);
	}
}
