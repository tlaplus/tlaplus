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
	
	MCOutputParser(final File outFile) {
		mcOutFile = outFile;
	}

	List<MCOutputMessage> parse(final boolean returnAllMessages) throws IOException {
		final ArrayList<MCOutputMessage> encounteredMessages = returnAllMessages ? new ArrayList<>() : null;
		
		try (final BufferedReader br = new BufferedReader(new FileReader(mcOutFile))) {
			MCOutputMessage message;
			
			while ((message = parseChunk(br)) != null) {
				if (returnAllMessages) {
					encounteredMessages.add(message);
				}

				if (message.getType() == MP.ERROR) {
					consumeErrorMessageAndStates(br, message);
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
