/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.jcloud;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Properties;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJobFactory;

import tlc2.TLCGlobals;

public class Application implements IApplication {

	/* (non-Javadoc)
	 * @see org.eclipse.equinox.app.IApplication#start(org.eclipse.equinox.app.IApplicationContext)
	 */
	public Object start(IApplicationContext context) throws Exception {
		Object argObject = context.getArguments().get(
				IApplicationContext.APPLICATION_ARGS);
		if (argObject == null || !(argObject instanceof String[]) || ((String[]) argObject).length < 1) {
			//TODO print usage
			System.exit(1);
		}
		
		final String[] args = (String[]) argObject;
		final String modelDirectory = args[0];
		
		final Properties props = initializeFromFile(modelDirectory);
		props.put(TLCJobFactory.MAIN_CLASS, tlc2.TLC.class.getName());

		// Optional parameters
		final String cloud = args.length >= 2 ? args[1] : "aws-ec2";

		if (args.length >= 3) {
			props.put(TLCJobFactory.MODEL_NAME, args[2]);
		}
		if (args.length >= 4) {
			props.put(TLCJobFactory.SPEC_NAME, args[3]);
		}
		if (args.length >= 5) {
			props.put(TLCJobFactory.MAIL_ADDRESS, args[4]);
		}

		// The parameters below are the only one currently useful with CloudDistributedTLC
		final StringBuffer tlcParams = new StringBuffer();
		
        // fp seed offset (decrease by one to map from [1, 64] interval to [0, 63] array address
        final int fpSeedOffset = 1;
        tlcParams.append("-fp ");
        tlcParams.append(String.valueOf(fpSeedOffset - 1));
    	tlcParams.append(" ");
        
        int maxSetSize = TLCGlobals.setBound;
		if (maxSetSize != TLCGlobals.setBound) {
        	tlcParams.append("-maxSetSize ");
        	tlcParams.append(String.valueOf(maxSetSize));
        	tlcParams.append(" ");
        }
        
		boolean checkDeadlock = false;
		if (!checkDeadlock) {
			tlcParams.append("-deadlock");
        	tlcParams.append(" ");
		}
		
		// https://github.com/tlaplus/tlaplus/issues/92#issuecomment-339989087
		final int coverage = Integer.getInteger("coverage", 0);
		if (coverage > 0) {
			tlcParams.append("-coverage ");
        	tlcParams.append(String.valueOf(coverage));
		}
		
		final TLCJobFactory factory = new CloudTLCJobFactory();
		final CloudDistributedTLCJob job = (CloudDistributedTLCJob) factory.getTLCJob(cloud, new File(modelDirectory), 1, props, tlcParams.toString());
		job.setIsCLI(true);
		job.setDoJfr(true);
		final IStatus status = job.run(new MyProgressMonitor(9));
		// Show error message if any such as invalid credentials.
		if (status.getSeverity() == IStatus.ERROR) {
			System.err.println(status.getMessage());
			final Throwable exception = status.getException();
			if (exception instanceof CloudDistributedTLCJob.ScriptException) {
				System.err.printf("\n###############################\n\n%s\n###############################\n",
						exception.getMessage());
			}
			// Signal unsuccessful execution.
			return new Integer(1);
		}
		
		return IApplication.EXIT_OK;
	}

	private Properties initializeFromFile(final String modelDirectory) throws IOException, FileNotFoundException {
		final Properties props = new Properties();
		final File file = new File(modelDirectory + File.separator + "cloud.properties");
		if (file.exists()) {
			props.load(new FileInputStream(file));
		}
		return props;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.equinox.app.IApplication#stop()
	 */
	public void stop() {
	}
	
	private static class MyProgressMonitor implements IProgressMonitor {
		private final DateFormat formatter = new SimpleDateFormat( "YYYY-MM-dd HH:mm:ss.SSS" );
		private final int totalSteps;
		private int steps = 1;

		public MyProgressMonitor(int totalSteps) {
			this.totalSteps = totalSteps;
		}

		public void subTask(String str) {
			System.out.printf("%s (%s of %s): %s\n", formatter.format(new Date()), Integer.toString(steps),
					Integer.toString(totalSteps), str);
			steps++;
		}

		public void beginTask(String str, int totalWork) {
			subTask(str);
		}

		public void done() {}

		public void internalWorked(double work) {}

		public boolean isCanceled() {return false;}

		public void setCanceled(boolean value) {}

		public void setTaskName(String name) {}

		public void worked(int work) {}
	}
}
