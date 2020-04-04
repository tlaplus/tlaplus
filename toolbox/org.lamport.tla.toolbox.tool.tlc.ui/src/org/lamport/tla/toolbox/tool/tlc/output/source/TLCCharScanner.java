package org.lamport.tla.toolbox.tool.tlc.output.source;

import org.eclipse.jface.text.rules.ICharacterScanner;

public abstract class TLCCharScanner {
	   

    public static boolean isEOF(final ICharacterScanner scanner) {
    	return isChar(scanner, ICharacterScanner.EOF);
	}
    
    public static boolean isEOL(final ICharacterScanner scanner) {
    	return isChar(scanner, 10);
    }
    
    private  static boolean isChar(final ICharacterScanner scanner, int i) {
		int c = scanner.read();
		scanner.unread();
		return c == i;
    }
    
    public static boolean isTag(final ICharacterScanner scanner, final String tag) {
		final int length = tag.length();
		
		int i = 0;
		for (; i < length; i++) {
			if (tag.charAt(i) != scanner.read() ) {
				unwind(scanner, i + 1);
				return false;
			}
		}
		unwind(scanner, length);
		return true;
	}

	private static void unwind(ICharacterScanner scanner, int i) {
		for (int j = 0; j < i; j++) {
			scanner.unread();
		}
	}
}
