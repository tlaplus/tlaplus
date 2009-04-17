package tlc2;

import java.io.File;

import util.SimpleFilenameToStream;
import util.ToolIO;

public class TestDriver2
{

    /**
     * @author Simon Zambrovski
     * @version $Id: TLCJob.java 638 2009-04-10 04:08:14Z simonzam $
     */
    private static final long TIMEOUT = 1000 * 5;
    private static final int REPEATS = 10;

    private String rootModule;
    private String cfgFile;
    private String projectDir;

    private TLCThread tlcThread;
    private int workers = 2;

    private int reported;

    
    public static void main(String[] args) 
    {
        if (args.length < 6 ) 
        {
            // -workers 2 -config AtomicBakery_MC_1.cfg -metadir C:\org.zambrovski\download\AtomicBakery_MC_1.toolbox AtomicBakery_MC_1
            System.out.println("Call with: -workers <num> -config <name-of-config.cfg> -metadir <dir-to-put-states> <name-of-module>");
        }
        TestDriver2 testDriver2 = new TestDriver2(args[6], args[3], args[5]);
        testDriver2.setWorkers(Integer.parseInt(args[1]));

        for (int i = 0 ; i < REPEATS; i++)
        {
            testDriver2.reported = 0;
            testDriver2.run();
        }
        System.exit(0);
    }
    /**
     * @param name
     */
    public TestDriver2(String rootModule, String cfgFile, String projectDir)
    {

        this.rootModule = rootModule;
        this.cfgFile = cfgFile;
        this.projectDir = projectDir;

        // initialize the progress reporting variable
        this.reported = 0;

    }

    /**
     * Sets the number of workers
     * @param workers number of threads to be run in parallel
     */
    public void setWorkers(int workers)
    {
        this.workers = workers;
    }

    protected int run()
    {
        report("entering run");

        // setup tool IO
        // Reset the tool output messages.
        ToolIO.reset();
        ToolIO.setMode(ToolIO.TOOL);
        ToolIO.setUserDir(new File(rootModule).getParent());

        // create a TLC instance
        TLC tlc = new TLC();
        report("tlc created " + tlc.toString());
        
        // setup name resolver
        // in RCP FS model use:
        // tlc.setResolver(new RCPNameToFileIStream(null));

        // for simple FS model:
        tlc.setResolver(new SimpleFilenameToStream());

        // setup SpecObj from parser
        // SpecObj specObj = ToolboxHandle.getSpecObj();
        // tlc.setSpecObject(specObj);

        // handle parameters
        String[] params = new String[] { 
                "-config", cfgFile,
                // "-coverage", "0.1",
                "-workers", "" + workers, 
                "-metadir", projectDir, 
                rootModule };
        boolean status = tlc.handleParameters(params);

        // report errors in parameters
        if (!status)
        {
            return -1;
        }

        // create thread for TLC running
        tlcThread = new TLCThread(tlc);
        tlcThread.setName("TLC Thread");
        report("tlcthread created " + tlcThread.getId());

        // Start the TLC thread
        tlcThread.start();
        report("tlcthread started");

        while (this.checkAndSleep())
        {
            // report the messages created since last reporting
            // check the cancellation status
            if (isCancelled())
            {
                // cancel the TLC
                tlc.setCanceledFlag(true);

                // report the messages created since last reporting
                reportProgress();

                // abnormal termination
                return -1;
            }
        }
        // report progress
        reportProgress();

        // successful termination
        return 1;
    }

    /**
     * Method for external cancellation
     */
    private boolean isCancelled()
    {
        return false;
    }
    
    
    // check if TLC is ready and sleep
    private boolean checkAndSleep()
    {
        report("entering checkAndSleep()");
        try
        {
            report("Go sleep \t" + System.currentTimeMillis());
            // go sleep
            Thread.sleep(TIMEOUT);

            report("Wake up \t" + System.currentTimeMillis());

        } catch (InterruptedException e)
        {
            // nothing to do
            e.printStackTrace();
        }

        // return true if the tlc is still calculating
        boolean result = tlcThread.isRunning();
        report("leaving checkAndSleep() with " + result);
        return result;
    }

    /**
     * Report progress to the monitor 
     */
    protected void reportProgress()
    {
        // report progress
        String[] messages = ToolIO.getAllMessages();
        for (; reported < messages.length; reported++)
        {
            System.out.println(messages[reported]);
        }
    }

    /**
     * Thread to run TLC in
     */
    class TLCThread extends Thread
    {
        private boolean isRunning = false;
        private TLC tlc;

        public TLCThread(TLC tlc)
        {
            this.tlc = tlc;
        }

        public void run()
        {
            synchronized (this)
            {
                report("TLC Thread: {STARTED}");
                isRunning = true;
            }
            // start TLC
            this.tlc.process();

            synchronized (this)
            {
                isRunning = false;
                report("TLC Thread: {FINISHED}");
            }
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

    public void report(String message)
    {
        // System.err.println("" + Thread.currentThread().getId() + "\t" + message);
    }

}
