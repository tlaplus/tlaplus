package org.lamport.tla.toolbox.tool.tlc.output;

import java.io.IOException;

import org.eclipse.ui.console.IOConsole;
import org.eclipse.ui.console.IOConsoleOutputStream;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.console.ConsoleFactory;

/**
 * A sink writing to a console. In plain English, this causes the Toolbox's
 * console to show TLC's output (stdout/stderr).
 * 
 * @author Simon Zambrovski
 */
public class ConsoleProcessOutputSink implements IProcessOutputSink {

	private final IOConsole console;
	private final IOConsoleOutputStream outputStream;

	public ConsoleProcessOutputSink() {
		this.console = ConsoleFactory.getTLCConsole();
		this.outputStream = this.console.newOutputStream();
	}

	@Override
	public synchronized void appendText(final String text) {
		try {
			this.outputStream.write(text.getBytes());
		} catch (IOException e) {
			TLCUIActivator.getDefault().logError("Error printing a console message: >" + text + "<", e);
		}
	}

	@Override
	public void initializeSink(Model model, int sinkType) {
		// No-op (The why has been lost in time).
	}

	@Override
	public void processFinished() {
		// No-op (The why has been lost in time).
	}
}
