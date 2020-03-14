package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.File;
import java.util.Properties;

import org.eclipse.core.runtime.jobs.Job;

import util.MailSender;

public interface TLCJobFactory {

	final String MAIN_CLASS = "mainClass";
	final String MAIL_ADDRESS = MailSender.MAIL_ADDRESS;
	final String SPEC_NAME = MailSender.SPEC_NAME;
	final String MODEL_NAME = MailSender.MODEL_NAME;
	
	Job getTLCJob(String aName, File aModelFolder, int numberOfWorkers, Properties props, String string);
}
