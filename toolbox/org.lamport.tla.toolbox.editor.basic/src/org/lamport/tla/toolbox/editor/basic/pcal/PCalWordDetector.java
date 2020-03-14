package org.lamport.tla.toolbox.editor.basic.pcal;

import org.eclipse.jface.text.rules.IWordDetector;
import org.lamport.tla.toolbox.editor.basic.tla.TLAWordDetector;

public class PCalWordDetector extends TLAWordDetector implements IWordDetector {

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.editor.basic.tla.TLAWordDetector#isWordPart(char)
	 */
	@Override
	public boolean isWordPart(final char character) {
		if (character == ':' || character == '=') {
			// Detect assignment ":=" as word.
			return true;
		} else if (character == '|') {
			// Detect multi-assignment "||" as word.
			return true;
		}
		return super.isWordPart(character);
	}
}
