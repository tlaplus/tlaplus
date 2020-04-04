package tlc2.input;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import tlc2.TraceExpressionExplorerSpecWriter;
import tlc2.model.MCError;
import tlc2.model.MCState;
import tlc2.output.EC;
import tlc2.output.MP;
import util.TLAConstants;

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
	 *              messages, or if there is no output file to be found.
	 * @param sourceDirectory
	 * @param specName
	 * @throws IOException
	 */
	public static void prettyPrintToStream(final OutputStream os, final File sourceDirectory, final String specName)
			throws IOException {
		final File outFile = new File(sourceDirectory, specName + TLAConstants.Files.OUTPUT_EXTENSION);
		final MCOutputParser parser = new MCOutputParser(outFile);
		parser.parse(false);
		
		final File tlaFile = new File(sourceDirectory, specName + TLAConstants.Files.TLA_EXTENSION);
		final HashMap<String, String> variableTraceExpressionMap
									= TraceExpressionExplorerSpecWriter.getVariableExpressionMapFromTLAFile(tlaFile);
		prettyPrintToStream(os, parser.getError(), variableTraceExpressionMap);
	}
	
	/**
	 * @param os an output stream to send the 'pretty printed' trace to, or a
	 *              notification if the error is null
	 *              messages.
	 * @param error
	 * @throws IOException
	 */
	public static void prettyPrintToStream(final OutputStream os, final MCError error) {
		prettyPrintToStream(os, error, null);
	}
	
	/**
	 * @param os an output stream to send the 'pretty printed' trace to, or a
	 *              notification if the error is null
	 *              messages.
	 * @param error
	 * @param variableTraceExpressionMap if non-null; any keys which are variable names will have the expressions
	 * 										substituted for the display.
	 * @throws IOException
	 */
	public static void prettyPrintToStream(final OutputStream os, final MCError error,
										   final HashMap<String, String> variableTraceExpressionMap) {
		final PrintStream ps;
		if (os instanceof PrintStream) {
			ps = (PrintStream)os;
		} else {
			ps = new PrintStream(os);
		}
		
		if (error == null) {
			ps.println("The output log contained no error-state messages; there is nothing to display.");
		} else {
			if (variableTraceExpressionMap != null) {
				error.updateStatesForTraceExpression(variableTraceExpressionMap);
			}
			
			for (final MCState state : error.getStates()) {
				ps.println(getPrettyPrintForState(state));
				ps.println(state.getConjunctiveDescription(true, "\t", true));
			}
		}
	}
}
