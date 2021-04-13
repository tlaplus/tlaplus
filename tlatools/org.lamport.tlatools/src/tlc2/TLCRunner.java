package tlc2;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import tlc2.output.EC;
import tlc2.output.TeeOutputStream;
import tlc2.tool.fp.FPSetFactory;

/**
 * Originally i was attempting to run the model check in the same JVM in which {@link TraceExplorer} was invoked (and 
 * 	then did its parsing and generating TLA and CFG files.) The model check process would fail with a message of:
 * 
 * 				@!@!@STARTMSG 2233:1 @!@!@
 * 				The initial predicate _TEInit cannot be a constant.
 * 				@!@!@ENDMSG 2233 @!@!@
 * 
 * ... however, running TLC from command line freshly on the same TLA/CFG would not produce this error.  I can only
 * 	surmise that the parsing process is setting some static value somewhere which is not being cleared and which is
 * 	then making the model checking process fail.
 * 
 * In light of that, i've written this class to spin off a new JVM for the model check.
 */
public class TLCRunner {
	public static List<String> JVM_ARGUMENTS;
	private static final String TLC_CLASS = TLC.class.getName();
	
	static {
		JVM_ARGUMENTS = new ArrayList<>();
		JVM_ARGUMENTS.add("-XX:+UseParallelGC");
		JVM_ARGUMENTS.add("-Dfile.encoding=UTF-8");
		JVM_ARGUMENTS.add("-Dtlc2.tool.fp.FPSet.impl=" + FPSetFactory.getImplementationDefault());
	}
	
	
	private final File outputLogfile;
	private final OutputStream outputOutputStream;
	private final List<String> arguments;
	
	private boolean silenceStdOut;

	public TLCRunner(final List<String> tlcArguments, final File logfileDestination) {
		outputLogfile = logfileDestination;
		outputOutputStream = null;
		arguments = tlcArguments;
		
		silenceStdOut = false;
	}

	public TLCRunner(final List<String> tlcArguments, final OutputStream logfileOutputStream) {
		outputLogfile = null;
		outputOutputStream = logfileOutputStream;
		arguments = tlcArguments;
		
		silenceStdOut = false;
	}
	
	/**
	 * @param flag if true, no output from the TLC process will be sent to System.out
	 */
	void setSilenceStdOut(final boolean flag) {
		silenceStdOut = flag;
	}
	
	/**
	 * This will not return until the process has finished.
	 * @return the exit value of the TLC process
	 * @throws IOException
	 */
	public int run() throws IOException {
		final ProcessBuilder processBuilder = createProcess();
		final Process p = processBuilder.start();
		final BufferedInputStream stdOutReader = new BufferedInputStream(p.getInputStream());
		final BufferedInputStream stdErrReader = new BufferedInputStream(p.getErrorStream());
		final BufferedOutputStream logfileOutputStream;
		if (outputOutputStream != null) {
			if (outputOutputStream instanceof BufferedOutputStream) {
				logfileOutputStream = (BufferedOutputStream)outputOutputStream;
			} else {
				logfileOutputStream = new BufferedOutputStream(outputOutputStream);
			}
		} else {
			final FileOutputStream fos = new FileOutputStream(outputLogfile);
			logfileOutputStream = new BufferedOutputStream(fos);
		}
		final OutputStream stdOutPumpOutput;
		if (silenceStdOut) {
			stdOutPumpOutput = logfileOutputStream;
		} else {
			stdOutPumpOutput = new TeeOutputStream(System.out, logfileOutputStream);
		}
		final StreamPump stdOutPump = new StreamPump(stdOutReader, stdOutPumpOutput);
		final StreamPump stdErrPump = new StreamPump(stdErrReader, null);
		
		try {
			(new Thread(stdOutPump)).start();
			(new Thread(stdErrPump)).start();
			
			p.waitFor();
			
			return p.exitValue();
		} catch (final InterruptedException ie) {
			// TODO improve logging here
			System.out.println("TLC process was interrupted: " + ie.getMessage());
		} finally {
			stdOutPump.stop();
			stdErrPump.stop();
			
			try {
				logfileOutputStream.close();
			} catch (final Exception e) { }
		}
		
		return EC.ExitStatus.ERROR_SYSTEM;
	}

	private ProcessBuilder createProcess() {
		final boolean isWindows = System.getProperty("os.name").toLowerCase().startsWith("windows");
		final String jvm = System.getProperty("java.home")
								+ File.separator
								+ "bin"
								+ File.separator
								+ "java"
								+ (isWindows ? ".exe" : "");
		final List<String> command = new ArrayList<String>();
		command.add(jvm);
		command.addAll(JVM_ARGUMENTS);
		command.add(TLC_CLASS);
		command.addAll(arguments);

		final ProcessBuilder processBuilder = new ProcessBuilder(command);
		final Map<String, String> environment = processBuilder.environment();
		environment.put("CLASSPATH", System.getProperty("java.class.path"));
		
		return processBuilder;
	}

	
	private static class StreamPump implements Runnable {
	    private static final int WAIT_SLEEP = 125;

	    
	    private final InputStream inputStream;
	    private final OutputStream outputStream;

	    private volatile boolean shouldStop;

	    /**
	     * @param is
	     * @param os pass null to simply drain the input stream
	     */
	    StreamPump(final InputStream is, final OutputStream os) {
	        this.inputStream = is;
	        this.outputStream = os;
	        this.shouldStop = false;
	    }

		public void run() {
			try {
				while (!shouldStop) {
					while ((inputStream.available() > 0) && !shouldStop) {
						if (outputStream != null) {
							outputStream.write(inputStream.read());
						} else {
							inputStream.read();
						}
					}
					if (outputStream != null) {
						outputStream.flush();
					}

					try {
						Thread.sleep(WAIT_SLEEP);
					} catch (final Exception e) { }
				}
			} catch (final Exception e) { }
		}

		void stop() {
	        shouldStop = true;
	    }
	}
}
