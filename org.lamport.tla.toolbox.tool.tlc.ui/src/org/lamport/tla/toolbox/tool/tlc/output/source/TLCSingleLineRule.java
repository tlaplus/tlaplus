package org.lamport.tla.toolbox.tool.tlc.output.source;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.SingleLineRule;

public class TLCSingleLineRule extends SingleLineRule {

	public TLCSingleLineRule(String startSequence, String endSequence, IToken token) {
		super(startSequence, endSequence, token);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.rules.PatternRule#endSequenceDetected(org.eclipse.jface.text.rules.ICharacterScanner)
	 */
	@Override
	protected boolean endSequenceDetected(ICharacterScanner scanner) {
		while(true) {
			scanner.read();
			if(TLCCharScanner.isEOF(scanner)) {
				break;
			} else if (TLCCharScanner.isEOL(scanner)) {
				// EOL has to be consumed
				scanner.read();
				break;
			}
		}
		return true;
	}
}
