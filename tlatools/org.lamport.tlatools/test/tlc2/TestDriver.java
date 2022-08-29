package tlc2;

import util.SimpleFilenameToStream;
import util.ToolIO;

public class TestDriver {
    private static final int COUNT = 3;

    private static final long TIMEOUT = 1000 * 5;

    private static int reported;
    private static TLCThread tlcThread;

    // runs TLC twice, to control the side effects
    public static void main(final String[] args) {
        for (int i = 0; i < COUNT; i++) {
            System.out.println("Run " + (i + 1) + " ----------------------------------------------");
            callTLC(args);
            System.out.println("---------------------------------------- complete.\n");
        }
        System.exit(0);
    }

    private static void callTLC(final String[] args) {
        report("entering callTLC()");
        ToolIO.reset();
        ToolIO.setMode(ToolIO.TOOL);
        ToolIO.setUserDir(args[5]);

        reported = 0;
        final TLC tlc = new TLC();
        report("tlc created " + tlc);
        // handle parameters
        if (tlc.handleParameters(args)) {
            tlc.setResolver(new SimpleFilenameToStream());

            // call the actual processing method
            tlcThread = new TLCThread(tlc);
            tlcThread.setName("TLC Thread");

            report("tlcThread created " + tlcThread.getId());
            tlcThread.start();
            report("tlcThread " + tlcThread.getId() + "started ");

            while (checkAndSleep()) {
                report("begin report");
                reportProgress();
                report("finished report");
            }
            report("after while");

            reportProgress();
        }
        report("leaving callTLC()");
    }

    // decrement the number and sleep
    private static boolean checkAndSleep() {
        report("entering checkAndSleep()");
        try {
            // go sleep
            report("go to sleep " + System.currentTimeMillis());
            Thread.sleep(TIMEOUT);
            report("wake up " + System.currentTimeMillis());

        } catch (final InterruptedException e) {
            // nothing to do
            e.printStackTrace();
        }
        // return true if the tlc is still calculating

        final boolean isRunning = tlcThread.isRunning();
        report("leaving checkAndSleep() with " + isRunning);
        return isRunning;
    }

    private static void reportProgress() {
        // report progress
        report("entering reportProgress()");
        final String[] messages = ToolIO.getAllMessages();
        for (; reported < messages.length; reported++) {
            System.out.println(messages[reported]);
        }
        report("leaving reportProgress()");
    }

    public static void report(final String message) {
        // System.out.println(Thread.currentThread().getId() + "\t" + message);
    }

    /**
     * Thread to run TLC in
     */
    static class TLCThread extends Thread {
        private final TLC tlc;
        private boolean isRunning;

        public TLCThread(final TLC tlc) {
            this.tlc = tlc;
            synchronized (this) {
                this.isRunning = false;
            }
        }

        @Override
        public void run() {
            synchronized (this) {
                System.out.println("TLC Thread: ------------ {START}");
                isRunning = true;
            }

            // start TLC
            this.tlc.process();

            synchronized (this) {
                System.out.println("TLC Thread: ------------ {FINISHED}");
                isRunning = false;
            }
        }

        /**
         *
         */
        public synchronized boolean isRunning() {
            return isRunning;
        }
    }

}
