package tlc2.input;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import tlc2.model.MCError;
import tlc2.model.MCState;
import tlc2.output.EC;
import tlc2.output.MP;

/**
 * This class provides a parser to extract error & state from an MC.out file; it also provides a public static
 * 	method which does a pretty-print dump to a provided output stream of the collected states in order.
 */
public class MCOutputParser extends AbstractMCOutputConsumer {
	private final File mcOutFile;

	private MCError error;
	
	MCOutputParser(final File outFile) {
		mcOutFile = outFile;
	}
	
	MCError getError() {
		return error;
	}

	List<MCOutputMessage> parse(final boolean returnAllMessages) throws IOException {
		final ArrayList<MCOutputMessage> encounteredMessages = returnAllMessages ? new ArrayList<>() : null;
		
		try (final BufferedReader br = new BufferedReader(new FileReader(mcOutFile))) {
			MCOutputMessage message;
			MCError currentError = null;
			
			while ((message = parseChunk(br, null)) != null) {
				if (returnAllMessages) {
					encounteredMessages.add(message);
				}

				// TODO unclear how - if - nested errors can occur; there is support for them in TLCError
				//			which has [therefore] been mirrored in MCError
				if (message.getType() == MP.ERROR) {
					if (error == null) {
						error = new MCError(null, message.getBody());
						currentError = error;
					} else {
						currentError = new MCError((currentError != null) ? currentError : error, message.getBody());
					}
					
					message = parseChunk(br, null);
					if ((message == null) || (message.getType() != MP.ERROR)) {
						throw new IOException("Expected a useless error message like "
												+ "'The behavior up to this point is...' but didn't find one after"
												+ "[" + currentError.getMessage() + "]");
					}
					
					boolean inStateTrace = true;
					while (inStateTrace) {
						message = parseChunk(br, null);
						if (message == null) {
							throw new IOException("Unexpected end of the log during state consumption for "
													+ "[" + currentError.getMessage() + "]");
						}
						
						if (message.getType() == MP.STATE) {
							currentError.addState(MCState.parseState(message.getBody()));
						} else {
							inStateTrace = false;
							// TODO do we want to process this message?
						}
					}
				} else if (message.getCode() == EC.TLC_FINISHED) {
					break;
				}
			}
		}

		return encounteredMessages;
	}

	
	private static String getPrettyPrintForState(final MCState state) {
		if (state.isStuttering()) {
			return "<Stuttering>";
		} else if (state.isBackToState()) {
			return "<Back to state " + state.getStateNumber() + ">";
		}
		return state.getLabel();
	}
	
	/**
	 * @param os an output stream to send the 'pretty printed' trace to, or a
	 *              notification if the output file contains no error-state
	 *              messages.
	 * @param mcOut
	 * @throws IOException
	 */
	public static void prettyPrintToStream(final OutputStream os, final File mcOut) throws IOException {
		final MCOutputParser parser = new MCOutputParser(mcOut);
		parser.parse(false);
		
		final PrintStream ps;
		if (os instanceof PrintStream) {
			ps = (PrintStream)os;
		} else {
			ps = new PrintStream(os);
		}
		
		final MCError error = parser.getError();
		if (error == null) {
			ps.println("The file at " + mcOut.getAbsolutePath() + " contained no error-state messages.");
		} else {
			for (final MCState state : error.getStates()) {
				ps.println(getPrettyPrintForState(state));
				ps.println(state.getConjunctiveDescription(true, "\t"));
			}
		}
	}
}
