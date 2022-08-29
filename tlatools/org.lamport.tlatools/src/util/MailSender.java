package util;

import model.ModelInJar;
import tlc2.output.MP;

import javax.mail.*;
import javax.mail.internet.*;
import javax.naming.NamingException;
import javax.naming.directory.Attribute;
import javax.naming.directory.Attributes;
import javax.naming.directory.InitialDirContext;
import java.io.*;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.*;

public class MailSender {

    public static final String MODEL_NAME = "modelName";
    public static final String SPEC_NAME = "specName";
    public static final String MAIL_ADDRESS = "result.mail.address";
    private String modelName = "unknown model";
    private String specName = "unknown spec";
    private File err;
    private File out;
    // if null, no Mail is going to be send
    private InternetAddress[] toAddresses;
    private InternetAddress from;
    private InternetAddress fromAlt;
    public MailSender() throws FileNotFoundException, UnknownHostException, AddressException {
        ModelInJar.loadProperties(); // Reads result.mail.address and so on.
        final String mailto = System.getProperty(MAIL_ADDRESS);
        if (mailto != null) {
            this.toAddresses = InternetAddress.parse(mailto);

            this.from = new InternetAddress("TLC - The friendly model checker <"
                    + toAddresses[0].getAddress() + ">");
            this.fromAlt = new InternetAddress("TLC - The friendly model checker <"
                    + System.getProperty("user.name") + "@"
                    + InetAddress.getLocalHost().getHostName() + ">");

            // Record/Log output to later send it by email
            final String tmpdir = System.getProperty("java.io.tmpdir");
            this.out = new File(tmpdir + File.separator + TLAConstants.Files.MODEL_CHECK_OUTPUT_FILE);
            ToolIO.out = new LogPrintStream(out);
            this.err = new File(tmpdir + File.separator + TLAConstants.Files.MODEL_CHECK_ERROR_FILE);
            ToolIO.err = new ErrLogPrintStream(err);
        }
    }
    public MailSender(final String mainFile) throws FileNotFoundException, UnknownHostException, AddressException {
        this();
        setModelName(mainFile);
    }

    /**
     * @param from "Foo bar <foo@bar.com>"
     * @param to   An email address _with_ domain part (foo@bar.com)
     */
    private static boolean send(final InternetAddress from, final InternetAddress to, final String subject, final String body, final File[] files) {

        // https://javaee.github.io/javamail/docs/api/com/sun/mail/smtp/package-summary.html
        final Properties properties = System.getProperties();
        //properties.put("mail.debug", "true");

        if (!to.getAddress().contains("@")) {
            // no domain, no MX record to lookup
            return false;
        } else if (!to.getAddress().endsWith("localhost")) {
            // Prefer email to be delivered encrypted (assumes to lower likelihood of SMTP
            // rejection or classification as spam too). Falls back to plain text if SMTP
            // server does not support starttls. Only activate unless sending to localhost
            // which is the (postfix) SMTP running locally which only has a self-signed
            // certificate which gets rejected by java mail.
            properties.put("mail.smtp.starttls.enable", "true");
        }

        final List<MXRecord> mailhosts;
        try {
            mailhosts = getMXForDomain(to.getAddress().split("@")[1]);
        } catch (final NamingException e) {
            e.printStackTrace();
            return false;
        }

        // retry all mx host
        for (int i = 0; i < mailhosts.size(); i++) {
            final MXRecord mxRecord = mailhosts.get(i);
            properties.put("mail.smtp.host", mxRecord.hostname);
            try {
                final Session session = Session.getDefaultInstance(properties);
                final Message msg = new MimeMessage(session);
                msg.setFrom(from);
                msg.addRecipient(Message.RecipientType.TO, to);
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
                for (final File file : files) {
                    if (file == null) {
                        continue;
                    }
                    messageBodyPart = new MimeBodyPart();
                    messageBodyPart.attachFile(file);
                    messageBodyPart.setFileName(file.getName());
                    messageBodyPart.setHeader("Content-Type", "text/plain");
                    multipart.addBodyPart(messageBodyPart);
                }
                msg.setContent(multipart);

                Transport.send(msg);
                return true;
            } catch (final SendFailedException e) {
                final Exception next = e.getNextException();
                if (next != null && next.getMessage() != null && next.getMessage().toLowerCase().contains("greylist")
                        && !properties.containsKey(properties.get("mail.smtp.host") + ".greylisted")) {
                    // mark receiver as greylisted to not retry over and over again.
                    properties.put(properties.get("mail.smtp.host") + ".greylisted", "true");
                    throttleRetry(String.format(
                            "%s EMail Report: Detected greylisting when sending to %s at %s, will retry in %s minutes...",
                            new Date(), to.getAddress(), mxRecord.hostname, 10L), 10L);
                    i = i - 1;
                } else {
                    throttleRetry(String.format(
                            "%s EMail Report: Slowing down due to errors when sending to %s at %s, will continue in %d minute...",
                            new Date(), to.getAddress(), mxRecord.hostname, 1L), 1L);
                }
            } catch (final IOException | MessagingException e) {
                e.printStackTrace();
            }
        }
        return false;
    }

    private static void throttleRetry(final String msg, final long minutes) {
        try {
            System.err.println(msg);
            System.out.println(msg);
            Thread.sleep(minutes * 60L * 1000L);
        } catch (final InterruptedException e1) {
            e1.printStackTrace();
        }
    }

    private static List<MXRecord> getMXForDomain(final String aDomain) throws NamingException {
        final InitialDirContext ctx = new InitialDirContext();
        final Attributes attributes = ctx.getAttributes("dns:/" + aDomain,
                new String[]{"MX"});
        final Attribute attr = attributes.get("MX");

        final List<MXRecord> list = new ArrayList<>();

        // RFC 974
        if (attr == null) {
            list.add(new MXRecord(0, aDomain));
        } else {
            // split pref from hostname
            for (int i = 0; i < attr.size(); i++) {
                final Object object = attr.get(i);
                if (object instanceof String) {
                    final String[] split = ((String) object).split("\\s+");
                    if (split.length == 2) {
                        final int weight = Integer.parseInt(split[0]);
                        list.add(new MXRecord(weight, split[1]));
                    }
                }
            }
        }

        // sort (according to weight of mxrecord)
        Collections.sort(list);

        return list;
    }

    // For testing only.
    public static void main(final String[] args) throws AddressException, FileNotFoundException, UnknownHostException {
        final MailSender mailSender = new MailSender();
        mailSender.send();
    }

    public void setModelName(final String modelName) {
        this.modelName = modelName;
    }

    public void setSpecName(final String specName) {
        this.specName = specName;
    }

    public boolean send() {
        return send(new ArrayList<>());
    }

    public boolean send(final List<File> files) {
        if (toAddresses != null) {
            files.add(0, out);
            // Only add the err file if there is actually content
            if (err.length() != 0L) {
                files.add(0, err);
            }
            // Try sending the mail with the model checking result to the receivers. Returns
            // true if a least one email was delivered successfully.
            boolean success = false;
            for (final InternetAddress toAddress : toAddresses) {
                if (send(from, toAddress, "Model Checking result for " + modelName + " with spec " + specName,
                        extractBody(out), files.toArray(new File[0]))) {
                    success = true;
                } else if (send(fromAlt, toAddress, "Model Checking result for " + modelName + " with spec " + specName,
                        extractBody(out), files.toArray(new File[0]))) {
                    // Try with alternative from address which some receivers might actually accept.
                    success = true;
                }
            }
            return success;
        } else {
            // ignore, just signal everything is fine
            return true;
        }
    }

    /**
     * @return The human readable lines in the log file.
     */
    private String extractBody(final File out) {
        final StringBuilder result = new StringBuilder();
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
        } catch (final FileNotFoundException e) {
            e.printStackTrace();
            result.append("Failed to find file ").append(out.getAbsolutePath());
        }
        return result.toString();
    }

    private static class MXRecord implements Comparable<MXRecord> {
        public final Integer weight;
        public final String hostname;

        public MXRecord(final int aWeight, final String aHostname) {
            weight = aWeight;
            hostname = aHostname;
        }

        @Override
        public int compareTo(final MXRecord o) {
            return weight.compareTo(o.weight);
        }
    }

    /**
     * A LogPrintStream writes the logging statements to a file _and_ to
     * System.out.
     */
    private static class LogPrintStream extends PrintStream {

        public LogPrintStream(final File file) throws FileNotFoundException {
            super(new FileOutputStream(file));
        }

        /* (non-Javadoc)
         * @see java.io.PrintStream#println(java.lang.String)
         */
        @Override
        public void println(final String str) {
            System.out.println(str);
            super.println(str);
        }
    }

    private static class ErrLogPrintStream extends PrintStream {
        public ErrLogPrintStream(final File file) throws FileNotFoundException {
            super(new FileOutputStream(file));
        }

        /* (non-Javadoc)
         * @see java.io.PrintStream#println(java.lang.String)
         */
        @Override
        public void println(final String str) {
            System.err.println(str);
            super.println(str);
        }
    }
}
