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
