package tlc2;

import java.io.ByteArrayOutputStream;
import java.util.List;

import tlc2.output.AbstractSpecWriter;
import tlc2.output.SpecWriterUtilities;

class REPLSpecWriter extends AbstractSpecWriter {
	private static final String EXPRESSION_OPEN = "\"EXPR_TLATE_BEGIN\"";
	private static final String EXPRESSION_CLOSE = "\"EXPR_TLATE_END\"";
	private static final String ASSUME_PREFIX = "ASSUME PrintT(" + EXPRESSION_OPEN + ") /\\ PrintT(\n";
	private static final String ASSUME_SUFFIX = "\n) /\\ PrintT(" + EXPRESSION_CLOSE + ")\n";

	REPLSpecWriter(final String specName, final List<String> expressions) {
		super(true);
		
		tlaBuffer.append(SpecWriterUtilities.getExtendingModuleContent(specName,
																	   "Naturals", "Reals", "Sequences", "Bags",
																	   "FiniteSets", "TLC"));
		tlaBuffer.append(ASSUME_PREFIX);
		tlaBuffer.append(String.join("\n", expressions));
		tlaBuffer.append(ASSUME_SUFFIX);
	}
	
	
	static class REPLLogConsumerStream extends ByteArrayOutputStream {
		private boolean inResponse;
		private boolean haveCollected;
		private StringBuilder currentLine;
		
		private String collectedContent;
		
		REPLLogConsumerStream() {
			inResponse = false;
			haveCollected = false;
			currentLine = new StringBuilder();
		}
		
		String getCollectedContent() {
			return collectedContent;
		}
		
		// Being wrapped in a Buffer invokes this method, we sub-optimally pass it off to our real digestion below
		@Override
		public void write(final byte b[], final int off, final int len) {
			for (int i = off; i < (off + len); i++) {
				write(b[i]);
			}
		}

		@Override
		public void write(final int b) {
			if (haveCollected) {
				return;
			} else {
				if (b == '\n') {
					if (inResponse) {
						if (EXPRESSION_CLOSE.equals(currentLine.toString())) {
							haveCollected = true;
							
							final String allCollectedContent = toString();
							final int length = allCollectedContent.length();
							collectedContent = allCollectedContent.substring(0, (length - (EXPRESSION_CLOSE.length() + 1)));
						} else {
							super.write(b);
						}
					} else if (EXPRESSION_OPEN.equals(currentLine.toString())) {
						inResponse = true;
					}
					
					currentLine = new StringBuilder();
 				} else {
					if (inResponse) {
						super.write(b);
					}
 					
 					// casting to char is probably not the best thing - suffices for the majority of the presumed cases
 					currentLine.append((char)b);
 				}
			}
		}
	}
}
