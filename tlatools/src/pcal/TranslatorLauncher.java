package pcal;

import java.io.PrintStream;

import util.ToolIO;

/**
 * Launcher for the PCal Translator
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TranslatorLauncher
{
    /**
     * delegates the call to the {@link trans#main()}
     * @param args
     */
    public static int runPcalTranslation(String[] args)
    {
        ToolIO.reset();
        ToolIO.setMode(ToolIO.TOOL);
        PrintStream outputStr = ToolIO.err;
        int status = trans.runMe(args);
        return status;
    }
}
