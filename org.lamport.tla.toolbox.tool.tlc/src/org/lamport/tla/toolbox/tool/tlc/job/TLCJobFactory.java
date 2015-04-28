package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.File;
import java.util.Properties;

import org.eclipse.core.runtime.jobs.Job;

public interface TLCJobFactory {

	final String MAIN_CLASS = "mainClass";
	final String MAIL_ADDRESS = "result.mail.address";
	
	Job getTLCJob(String aName, File aModelFolder, int numberOfWorkers, Properties props, String string);
}
