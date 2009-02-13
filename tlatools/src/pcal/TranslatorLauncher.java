package pcal;

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
        
        int status = -1;
        
        try {
            status = trans.runMe(args);
            
        } catch (PCalUnrecoverableErrorRuntimeException e) 
        {
            e.printStackTrace();
        }

        String[] messages = ToolIO.getAllMessages();
        for (int i = 0; i < messages.length; i++)
        {
            System.out.println(messages[i]);
        }
        
        return status;
    }
}
