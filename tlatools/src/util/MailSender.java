package util;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Properties;
import java.util.Scanner;

import javax.activation.DataHandler;
import javax.activation.FileDataSource;
import javax.mail.Message;
import javax.mail.MessagingException;
import javax.mail.Multipart;
import javax.mail.Session;
import javax.mail.Transport;
import javax.mail.internet.AddressException;
import javax.mail.internet.InternetAddress;
import javax.mail.internet.MimeBodyPart;
import javax.mail.internet.MimeMessage;
import javax.mail.internet.MimeMultipart;
import javax.naming.NamingException;
import javax.naming.directory.Attribute;
import javax.naming.directory.Attributes;
import javax.naming.directory.InitialDirContext;

import model.ModelInJar;
import tlc2.output.MP;

// Requires Java >=6 due to javax.activation only part starting with 6
public class MailSender {

	public static final String MODEL_NAME = "modelName";
	public static final String SPEC_NAME = "specName";
	public static final String MAIL_ADDRESS = "result.mail.address";

	/**
	 * @param from "Foo bar <foo@bar.com>"
	 * @param to An email address _with_ domain part (foo@bar.com)
	 * @param domain domain part (bar.com). Used to lookup mx records
	 * @param subject
	 * @param messages
	 */
	private static boolean send(final String from, final String to,
			final String domain, final String subject, final String body, final File[] files) {
		
		final Properties properties = System.getProperties();
		//properties.put("mail.debug", "true");
		
		try {
			final List<MXRecord> mailhosts = getMXForDomain(domain);
				
			// retry all mx host
			for (MXRecord mxRecord : mailhosts) {
				properties.put("mail.smtp.host", mxRecord.hostname);
				
				final Session session = Session.getDefaultInstance(properties);
				final Message msg = new MimeMessage(session);
				msg.setFrom(new InternetAddress(from));
				msg.addRecipient(Message.RecipientType.TO, new InternetAddress(to));
				msg.setSubject(subject);
				
				// not sure why the extra body part is needed here
				MimeBodyPart messageBodyPart = new MimeBodyPart();

				final Multipart multipart = new MimeMultipart();
				
				// The main body part. Having a main body appears to have a very
				// positive effect on the spam score compared to emails with
				// just attachments. It is also visually more appealing to e.g.
				// Outlook users who otherwise see an empty mail.
				messageBodyPart = new MimeBodyPart();
				messageBodyPart.setContent(body, "text/plain");
				multipart.addBodyPart(messageBodyPart);

				// attach file(s)
				for (File file : files) {
					if (file == null) {
						continue;
					}
					messageBodyPart = new MimeBodyPart();
					messageBodyPart.setDataHandler(new DataHandler(
							new FileDataSource(file)));
					messageBodyPart.setFileName(file.getName());
					messageBodyPart.setHeader("Content-Type", "text/plain");
					multipart.addBodyPart(messageBodyPart);
				}
		        msg.setContent(multipart);
				
		        Transport.send(msg);
				return true;
			}
		} catch (NamingException e) {
			e.printStackTrace();
		} catch (AddressException e) {
			e.printStackTrace();
		} catch (MessagingException e) {
			e.printStackTrace();
		}
		return false;
	}

	private static List<MXRecord> getMXForDomain(String aDomain) throws NamingException {
		final InitialDirContext ctx = new InitialDirContext();
		final Attributes attributes = ctx.getAttributes("dns:/" + aDomain,
				new String[] { "MX" });
		final Attribute attr = attributes.get("MX");

		final List<MXRecord> list = new ArrayList<MXRecord>();
		
		// RFC 974
		if (attr == null) {
			list.add(new MXRecord(0, aDomain));
		} else {
			// split pref from hostname
			for (int i = 0; i < attr.size(); i++) {
				Object object = attr.get(i);
				if (object != null && object instanceof String) {
					String[] split = ((String) object).split("\\s+");
					if (split != null && split.length == 2) {
						Integer weight = Integer.parseInt(split[0]);
						list.add(new MXRecord(weight, split[1]));
					}
				}
			}
		}
		
		// sort (according to weight of mxrecord)
		Collections.sort(list);
		
		return list;
	}
	
	private static class MXRecord implements Comparable<MXRecord> {
		public Integer weight;
		public String hostname;
		
		public MXRecord(int aWeight, String aHostname) {
			weight = aWeight;
			hostname = aHostname;
		}

		public int compareTo(MXRecord o) {
			return weight.compareTo(o.weight);
		}
	}

	// if null, no Mail is going to be send
	private final String mailto;
	
	private String modelName = "unknown model";
	private String specName = "unknown spec";
	private File err;
	private File out;
	private String from;
	private String domain;

	public MailSender() throws FileNotFoundException, UnknownHostException {
		ModelInJar.loadProperties(); // Reads result.mail.address and so on.
		mailto = System.getProperty(MAIL_ADDRESS);
		if (mailto != null) {
			domain = mailto.split("@")[1];
			
			from = "TLC - The friendly model checker <"
					+ System.getProperty("user.name") + "@"
					+ InetAddress.getLocalHost().getHostName() + ">";
			
			// Record/Log output to later send it by email
			final String tmpdir = System.getProperty("java.io.tmpdir");
			out = new File(tmpdir + File.separator + "MC.out");
			ToolIO.out = new LogPrintStream(out);
			err = new File(tmpdir + File.separator + "MC.err");
			ToolIO.err = new LogPrintStream(err);
		}
	}
	
	public MailSender(String mainFile) throws FileNotFoundException, UnknownHostException {
		this();
		setModelName(mainFile);
	}
	
	public void setModelName(String modelName) {
		this.modelName = modelName;
	}

	public void setSpecName(String specName) {
		this.specName = specName;
	}

	public boolean send() {
		return send(new ArrayList<File>());
	}

	public boolean send(List<File> files) {
		if (mailto != null) {
			files.add(0, out);
			// Only add the err file if there is actually content 
			if (err.length() != 0L) {
				files.add(0, err);
			}
			// Try sending the mail with the model checking result to the receiver 
			return send(from, mailto, domain, "Model Checking result for " + modelName + " with spec " + specName,
					extractBody(out), files.toArray(new File[files.size()]));
		} else {
			// ignore, just signal everything is fine
			return true;
		}
	}	
    
	/**
	 * @return The human readable lines in the log file. 
	 */
	private String extractBody(File out) {
		StringBuffer result = new StringBuffer();
		try {
			final Scanner scanner = new Scanner(out);
			while (scanner.hasNext()) {
				final String line = scanner.nextLine();
				if (line != null && !line.startsWith(MP.DELIM)) {
					result.append(line);
					result.append("\n");
				}
			}
			scanner.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
			result.append("Failed to find file " + out.getAbsolutePath()); 
		}
		return result.toString();
	}

	/**
	 * A LogPrintStream writes the logging statements to a file _and_ to
	 * System.out.
	 */
    private static class LogPrintStream extends PrintStream {

    	public LogPrintStream(File file) throws FileNotFoundException  {
    		super(new FileOutputStream(file));
		}

    	/* (non-Javadoc)
    	 * @see java.io.PrintStream#println(java.lang.String)
    	 */
    	public void println(String str) {
    		System.out.println(str);
    		super.println(str);
    	}
    }
}
