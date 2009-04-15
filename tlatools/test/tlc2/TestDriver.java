package tlc2;

import util.SimpleFilenameToStream;
import util.ToolIO;

public class TestDriver
{
    private static final int COUNT = 3;

    private static final long TIMEOUT = 1000 * 5;
    private static final int STEP = 30;

    private static int reported;
    private static TLCThread tlcThread;

    // runs TLC twice, to control the side effects
    public static void main(String[] args)
    {
        for (int i = 0; i < COUNT; i++)
        {
            System.out.println("Run " + (i + 1) + " ----------------------------------------------");
            callTLC(args);
            System.out.println("---------------------------------------- complete.\n");
        }
        System.exit(0);
    }

    private static void callTLC(String[] args)
    {
        report("entering callTLC()");
        ToolIO.reset();
        ToolIO.setMode(ToolIO.TOOL);
        ToolIO.setUserDir(args[5]);
        
        reported = 0;
        TLC tlc = new TLC();
        report("tlc created " + tlc.toString());
        // handle parameters
        if (tlc.handleParameters(args))
        {
            tlc.setResolver(new SimpleFilenameToStream());

            // call the actual processing method
            tlcThread = new TLCThread(tlc);
            tlcThread.setName("TLC Thread");

            report("tlcThread created " + tlcThread.getId());
            tlcThread.start();
            report("tlcThread " + tlcThread.getId() + "started ");
            
            while (checkAndSleep())
            {
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
    private static boolean checkAndSleep()
    {
        report("entering checkAndSleep()");
        try
        {
            // go sleep
            report("go to sleep " + System.currentTimeMillis());
            Thread.sleep(TIMEOUT);
            report("wake up " + System.currentTimeMillis());

        } catch (InterruptedException e)
        {
            // nothing to do
            e.printStackTrace();
        }
        // return true if the tlc is still calculating

        boolean isRunning = tlcThread.isRunning();
        report("leaving checkAndSleep() with " + isRunning);
        return isRunning;
    }

    private static void reportProgress()
    {
        // report progress
        report("entering reportProgress()");
        String[] messages = ToolIO.getAllMessages();
        for (; reported < messages.length; reported++)
        {
            System.out.println(messages[reported]);
        }
        report("leaving reportProgress()");
    }

    public static void report(String message)
    {
        // System.out.println(Thread.currentThread().getId() + "\t" + message);
    }

    /**
     * Thread to run TLC in
     */
    static class TLCThread extends Thread
    {
        private boolean isRunning;
        private final TLC tlc;

        public TLCThread(TLC tlc)
        {
            this.tlc = tlc;
            synchronized (this)
            {
                this.isRunning = false;
            }
        }

        public void run()
        {
            synchronized (this)
            {
                System.out.println("TLC Thread: ------------ {START}");
                isRunning = true;
            }

            // start TLC
            this.tlc.process();

            synchronized (this)
            {
                System.out.println("TLC Thread: ------------ {FINISHED}");
                isRunning = false;
            }
        }

        public synchronized void setIsRunning(boolean value)
        {
            isRunning = value;
        }

        /**
         * 
         * @return
         */
        public synchronized boolean isRunning()
        {
            return isRunning;
        }
    }

}
