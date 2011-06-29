package org.lamport.tla.toolbox.tool.tlc.output.source;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;

public class TLCMultiLineRule implements IPredicateRule {

	private Token successToken;
	
	public TLCMultiLineRule(Token successToken) {
		this.successToken = successToken;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.rules.IRule#evaluate(org.eclipse.jface.text.rules.ICharacterScanner)
	 */
	public IToken evaluate(ICharacterScanner scanner) {
		return evaluate(scanner, false);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.rules.IPredicateRule#getSuccessToken()
	 */
	public IToken getSuccessToken() {
		return successToken;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.rules.IPredicateRule#evaluate(org.eclipse.jface.text.rules.ICharacterScanner, boolean)
	 */
	public IToken evaluate(ICharacterScanner scanner, boolean resume) {
		// impl does not support resume!
		if(resume) {
			throw new UnsupportedOperationException("Not implemented");
		}
		return doEvaluate(scanner);
	}

	/**
	 * Consumes every character except "@" which marks the beginning of a tag line
	 */
	private IToken doEvaluate(ICharacterScanner scanner) {
		// if there is nothing for us to read, just return
		if (TLCCharScanner.isEOF(scanner) || TLCCharScanner.isTag(scanner, TagBasedTLCOutputTokenScanner.HEAD_DELIM)) {
			return Token.UNDEFINED;
		} else {
			while (!TLCCharScanner.isEOF(scanner)
					&& !TLCCharScanner.isTag(scanner, TagBasedTLCOutputTokenScanner.HEAD_DELIM)) {
				scanner.read();
			}
			return successToken;
		}
	}
}
