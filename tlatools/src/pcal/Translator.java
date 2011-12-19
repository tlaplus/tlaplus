package pcal;

import java.util.List;
import java.util.Vector;

import util.ToolIO;

/**
 * Launcher for the PCal Translator for running out-of-the-tool
 * @author Simon Zambrovski
 * @version $Id$
 */
public class Translator
{
    /**
     * Resets the Tool IO
     */
    public void init()
    {
        ToolIO.reset();
        ToolIO.setMode(ToolIO.TOOL);
    }

    /**
     * delegates the call to the {@link trans#main()}
     * @param args
     */
//    public int runTranslation(String[] args)
    public TLAtoPCalMapping runTranslation(String[] args) 
    {
        init();
//        int status = trans.runMe(args);
        TLAtoPCalMapping status = trans.runMe(args);  
        return status;
    }

    /**
     * Retrieves the errors recorded during the execution
     * @return
     */
    public List getErrorMessages()
    {
        String[] messages = ToolIO.getAllMessages();
        Vector errorMessages = new Vector();
        System.out.println("Found " + messages.length + " messages");
        int position;
        String cleanMessage = null;
        for (int i = 0; i < messages.length; i++)
        {
            position = messages[i].indexOf(PcalDebug.UNRECOVERABLE_ERROR);
            if (position != -1)
            {
                cleanMessage = messages[i].substring(position, messages[i].length() - PcalDebug.ERROR_POSTFIX.length());
                errorMessages.add(cleanMessage);
            } else
            {
                cleanMessage = messages[i];
                // unknown error format
                System.out.println(cleanMessage);
            }
        }
        return errorMessages;
    }
}
