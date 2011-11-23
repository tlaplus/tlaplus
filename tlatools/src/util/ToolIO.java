package util;

import java.io.PipedOutputStream;
import java.io.PrintStream;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import tla2sany.semantic.SemanticNode;

/***************************************************************************
* SANY and TLC were written to communicate only by calling the             *
* System.out or System.err println() or print() methods.  The GUI needs    *
* to call the tools directly so it can access data produced by the tool    *
* but not output directly--for example, the ModuleNode objects produced    *
* by SANY. However, it also needs to capture the information contained     *
* in the printed output.  The easiest way to do that would be simply to    *
* attach System.out and System.err to a PipedInputStream and read the      *
* output from it.  Unfortunately, I haven't been able to figure out how    *
* to do that robustly.  The PipedInputStream seems to get broken when it   *
* has stopped receiving output for a while, and I don't know how to        *
* reattach it.  Moreover, I don't know how to detach System.{out,err}      *
* from the PipedInputStream and attach it to another one.                  *
*                                                                          *
* So, I am planning to replace all instances of System.out and             *
* System.err by ToolIO.out and ToolIO.err.  What this does will depend     *
* on the mode, which can currently have one of two values:                 *
*                                                                          *
*   SYSTEM : ToolIO.out and ToolIO.err will be equal to System.out         *
*            and System.err.  This is the default value.                   *
*                                                                          *
*   TOOL   : Output produced by calling ToolIO.out.println, etc.,          *
*             buffered and delivered on calls to the class's methods.      *
***************************************************************************/
public class ToolIO
{
    /**
     * In this mode, print() and println() write to System.out.             
     */
    public static final int SYSTEM = 0;

    /**
     * In this mode, print() and println() write to System.err.             
     */
    public static final int TOOL = 1;

    /**
     * MODE HANDLING                                                            
     *                                                                          
     * The two public methods are the obvious ones for setting and reading the  
     * mode:                                                                    
     *                                                                          
     *    boolean setMode(int mode)                                             
     *    int     getMode()                                                     
     */
    private static int mode = SYSTEM;

    /**
     * Default resolver is responsible for the resolution from module name to
     * input stream. It is used only if no resolver is specified. 
     */
    private static FilenameToStream defaultResolver;

    /**
     * The GUI needs to change the user directory--the default path for     
     * looking up files.  This seems to be impossible with Java.  So, when  
     * this value is non-null, tools should use it for looking up file      
     * names--looking up a file named filename with                         
     *                                                                      
     *    new File(userDir, filename)                                       
     */
    private static String userDir = null;

    public static PrintStream out = System.out;
	/**
	 * Care must be taken with out and err not being synchronized. Concurrent
	 * writes will cause interleaved output.
	 * 
	 * @see https://bugzilla.tlaplus.net/show_bug.cgi?id=221
	 */
    public static PrintStream err = System.err;

    // = 1 for testing. Should be set to reasonable value like 1000.
    private static final int InitialMaxLength = 1;

    /**
     * List of semantic nodes which are used by tools
     * @see ToolIO#registerSemanticNode() 
     */
    private static List semanticNodes = new LinkedList();

    /**
     * The current sequence of messages is messages[0] ...                  
     * messages[length-1] A single message may contain \n characters.       
     * There will be one message for every call of println().               
     */
    static String[] messages = new String[InitialMaxLength];
    static int length = 0;

    /**
     * The portion of the next message written by invocations of print()    
     * not followed by an invocation of println().                          
     */
    static String nextMessage = "";

    public static String getUserDir()
    {
        return userDir;
    }

    public static void setUserDir(String dir)
    {
        userDir = dir;
    }

    /**
     * Returns the mode of the ToolIO
     * @return one of {@link ToolIO#SYSTEM},{@link ToolIO#TOOL} 
     */
    public static int getMode()
    {
        return mode;
    }

    /**
     * Set the mode and returns true if the mode argument is legal,         
     * otherwise does nothing and returns false.
     * @param m - the mode, use {@link ToolIO#SYSTEM},{@link ToolIO#TOOL}
     */
    public static boolean setMode(int m)
    {
        if (m == SYSTEM)
        {
            mode = m;
            out = System.out;
            err = System.err;
            return true;
        } else if (m == TOOL)
        {
            mode = m;
            out = new ToolPrintStream();
            err = new ToolPrintStream();
            return true;
        }
        return false;
    }

    /**
     * Resets the ToolIO and deletes the messages   
     * the mode and user directory are not changed 
     */
    public static synchronized void reset()
    {
        /*
         * Throws away all messages obtained so far.                            
         */
        messages = new String[InitialMaxLength];
        length = 0;
        nextMessage = "";
    }

    /**
     * Retrieves the messages send to the err and out streams
     */
    public static synchronized String[] getAllMessages()
    {

        // System.out.println("getAllMessages called with length = " + length) ;
        // for (int i = 0 ; i < messages.length; i++) {
        // System.out.println("GetAllMessages: "+ i + ":") ;
        // System.out.println(messages[i]) ;
        // };

        int retLen = length;
        if (!nextMessage.equals(""))
        {
            retLen++;
        }
        String[] ret = new String[retLen];
        System.arraycopy(messages, 0, ret, 0, retLen);
        if (!nextMessage.equals(""))
        {
            ret[length] = nextMessage;
        }
        return ret;
    } // getAllMessages

    /**
     * Prints all messages to system out
     */
    public static synchronized void printAllMessages()
    {
        /*
         * For debugging use.                                                   
         */
        System.out.println("---- Begin all messages");
        String[] msgs = getAllMessages();
        for (int i = 0; i < msgs.length; i++)
        {
            System.out.println("Msg " + i + ":");
            System.out.println(msgs[i]);
        }
        System.out.println("---- End all messages");
    }

    /**
     * Retrieves the default resolver
     * @return always not null
     */
    public static FilenameToStream getDefaultResolver()
    {
        if (defaultResolver == null)
        {
            setDefaultResolver(null);
        }
        return defaultResolver;
    }

    /**
     * Sets default resolver
     * @param resolver
     */
    public static void setDefaultResolver(FilenameToStream resolver)
    {
        if (resolver == null)
        {
            resolver = new SimpleFilenameToStream();
        }
        ToolIO.defaultResolver = resolver;
    }

    /**
     * Registers the semantic node
     * @param node the node containing tool specific information
     * @param toolId the id of the tool (currently not used)
     * 
     * <br><b>Note:</b><br>
     * This method is called from {@link SemanticNode#setToolObject(int, Object)} 
     * and identifies the semantic node that carries tool specific information. 
     * This information can be deleted using {@link ToolIO#cleanToolObjects(int)} 
     */
    public static void registerSemanticNode(SemanticNode node, int toolId)
    {
        if (!semanticNodes.contains(node)) 
        {
            semanticNodes.add(node);
        }
    }

    /**
     * Sets the tool-specific object for all listed semantic nodes to <code>null</code>
     * @param toolId the Id of the tool to reset the tool specific information
     */
    public static void cleanToolObjects(int toolId)
    {
        Iterator iter = semanticNodes.iterator();
        while(iter.hasNext())
        {
            SemanticNode node = (SemanticNode) iter.next();
            node.setToolObject(toolId, null);
        }
    }

    /**
     * Deletes the information about semantic nodes used with tool-specific information
     */
    public static void unregisterSemanticNodes()
    {
        semanticNodes = new LinkedList();
    }

} // class ToolIO

class ToolPrintStream extends PrintStream
{
    /**
     * Constructor
     */
    public ToolPrintStream()
    {
        super(new PipedOutputStream());
        ToolIO.out = this;
        ToolIO.err = this;
    }

    /**
     * Prints a string in to the ToolIO buffer in a separate line
     * @param str String to be printed
     */
    public void println(String str)
    {
        // SZ February 20 2009:
        // This is equivalent to
        // synchronized (this.getClass())
        // but is better to understand
        // that the actual synchronization is
        // performed on the static class object
        synchronized (ToolPrintStream.class)
        {
            // System.out.println("Println called with string:") ;
            // System.out.println(str) ;
            String thisMessage = ToolIO.nextMessage + str;
            ToolIO.nextMessage = "";
            /*****************************************************************
             * Enlarge the array if necessary.                                *
             *****************************************************************/
            if (ToolIO.messages.length == ToolIO.length)
            {
                String[] newMessages = new String[2 * ToolIO.messages.length];
                System.arraycopy(ToolIO.messages, 0, newMessages, 0, ToolIO.messages.length);
                ToolIO.messages = newMessages;
            }
            ToolIO.messages[ToolIO.length] = thisMessage;
            ToolIO.length++;

            // SZ February 20 2009:
            // This is a bug: Class.forName("ToolOutput").notifyAll();
            // throws an exception on every invocation
            // and has an empty catch this is a performance killer
            // 
            // The class has been renamed and the synchronization
            // is executed on another object.
            // In order to avoid this kind of bugs in future
            // just changed to another way of doing this
            // try { Class.forName("ToolOutput").notifyAll(); }
            // catch (Exception e) {
            // /*******************************************************************
            // * I have no idea why this exception could be thrown, or what to do *
            // * with it if it is. *
            // *******************************************************************/
            // } ; // catch

            /* **********************************************************************
             * Notify anyone who's waiting for a message.                           *
             * **********************************************************************/
            ToolPrintStream.class.notifyAll();
        } // synchronized
    } // println

    /**
     * Prints a string to the ToolIO message buffer.
     *
     * @param str The <code>String</code> to be printed
     */
    public synchronized void print(String str)
    {
        // SZ February 20 2009:
        // This is equivalent to the next line, but
        // it is better visible, that
        // the synchronization is executed on the static class
        // instance itself
        // synchronized (this.getClass()) {
        synchronized (ToolPrintStream.class)
        {
            // SZ February 20 2009:
            // printing bug fixed instead of printing the string str
            // the string "str" has been printed
            ToolIO.nextMessage += str;
            // SZ February 20 2009:
            // This is a bug: Class.forName("ToolOutput").notifyAll();
            // since the class has been renamed
            // this method throws an exception on every invocation
            // and has an empty catch this is a performance killer
            //
            // try { Class.forName("ToolOutput").notifyAll(); }
            // catch (Exception e) {
            // /******************************************************************
            // * I have no idea why this exception could be thrown, or what to *
            // * do with it if it is. *
            // ******************************************************************/
            // } ;

            /* *********************************************************************
             * Notify anyone who's waiting for a message.                          *
             * *********************************************************************/
            ToolPrintStream.class.notifyAll();
        } // synchronized
    } // print
} // class ToolPrintStream
