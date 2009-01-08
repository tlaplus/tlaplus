package util ;

import java.io.* ;


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
*   TOOL   : Output produced by calling ToolIO.out.println, etc.,         *
*             buffered and delivered on calls to the class's methods.      *
***************************************************************************/

public class ToolIO {

/***************************************************************************
* MODE HANDLING                                                            *
*                                                                          *
* The two public methods are the obvious ones for setting and reading the  *
* mode:                                                                    *
*                                                                          *
*    boolean setMode(int mode)                                             *
*    int     getMode()                                                     *
***************************************************************************/
  public static final int SYSTEM = 0 ;
    /***********************************************************************
    * In this mode, print() and println() write to System.out.             *
    ***********************************************************************/
  public static final int TOOL = 1 ;
    /***********************************************************************
    * In this mode, print() and println() write to System.err.             *
    ***********************************************************************/
  private static int mode = SYSTEM ;
    /***********************************************************************
    * Set the mode and returns true if the mode argument is legal,         *
    * otherwise does nothing and returns false.                            *
    ***********************************************************************/

  private static String userDir = null ;
    /***********************************************************************
    * The GUI needs to change the user directory--the default path for     *
    * looking up files.  This seems to be impossible with Java.  So, when  *
    * this value is non-null, tools should use it for looking up file      *
    * names--looking up a file named filename with                         *
    *                                                                      *
    *    new File(userDir, filename)                                       *
    ***********************************************************************/
  public static String getUserDir(){ return userDir; };
  public static void   setUserDir(String dir){ userDir = dir; };

  public static int getMode() { return mode ; } ;
  public static boolean setMode(int m) {
    /***********************************************************************
    * Set the mode and returns true if the mode argument is legal,         *
    * otherwise does nothing and returns false.                            *
    ***********************************************************************/
    if (m == SYSTEM) { mode = m ;
                       out  = System.out ;
                       err  = System.err ;
                       return true ;
                      } 
    else if (m == TOOL) { mode = m ;
                          out  = new ToolPrintStream() ;
                          err  = new ToolPrintStream() ;
                       return true ;
                        } ;
    return false ;
   } // setMode

  public static synchronized void reset() {
    /***********************************************************************
    * Throws away all messages obtained so far.                            *
    ***********************************************************************/
    messages    = new String[InitialMaxLength] ;
    length      = 0 ;
    nextMessage = "" ;
   } // Reset

  public static PrintStream out = System.out ;
  public static PrintStream err = System.err ;

  private static final int InitialMaxLength = 1 ;
    // = 1 for testing.  Should be set to reasonable value like 1000.
  static String[] messages = new String[InitialMaxLength] ;
  static int length = 0 ;
    /***********************************************************************
    * The current sequence of messages is messages[0] ...                  *
    * messages[length-1] A single message may contain \n characters.       *
    * There will be one message for every call of println().               *
    ***********************************************************************/

  static String nextMessage = "" ;
    /***********************************************************************
    * The portion of the next message written by invocations of print()    *
    * not followed by an invocation of println().                          *
    ***********************************************************************/

  public static synchronized String[] getAllMessages() {
// System.out.println("getAllMessages called with length = " + length) ;
// for (int i = 0 ; i < messages.length; i++) {
//  System.out.println("GetAllMessages: "+ i + ":") ;
//  System.out.println(messages[i]) ;
// };

     int retLen = length ;
     if (!nextMessage.equals("")) {retLen++;} ;
     String[] ret = new String[retLen] ;
     System.arraycopy(messages, 0, ret, 0, retLen) ;
     if (!nextMessage.equals("")) {ret[length] = nextMessage ;} ;
     return ret ;
   } // getAllMessages

  public static synchronized void printAllMessages() {
    /***********************************************************************
    * For debugging use.                                                   *
    ***********************************************************************/
    System.out.println("---- Begin all messages") ;
    String[] msgs = getAllMessages() ;
    for (int i = 0 ; i < msgs.length; i++) {
      System.out.println("Msg " + i + ":") ;
      System.out.println(msgs[i]) ; 
      }
    System.out.println("---- End all messages") ;
   }
 } // class ToolIO

class ToolPrintStream extends PrintStream {

  public ToolPrintStream () { super(new PipedOutputStream()) ; 
                         ToolIO.out = this ;
                         ToolIO.err = this ;
                        } 
     
    public void println(String str) {
      synchronized (this.getClass()) {
// System.out.println("Println called with string:") ;
// System.out.println(str) ;
          String thisMessage = ToolIO.nextMessage + str ;
          ToolIO.nextMessage = "" ;
          /*****************************************************************
          * Enlarge the array if necessary.                                *
          *****************************************************************/
          if (ToolIO.messages.length == ToolIO.length) {
            String[] newMessages = new String[2*ToolIO.messages.length] ;
            System.arraycopy(ToolIO.messages, 0, newMessages, 
                             0, ToolIO.messages.length) ;
            ToolIO.messages = newMessages ;
           } ;
          ToolIO.messages[ToolIO.length] = thisMessage ;
          ToolIO.length++ ;

      /***********************************************************************
      * Notify anyone who's waiting for a message.                           *
      ***********************************************************************/
      try { Class.forName("ToolOutput").notifyAll(); }
      catch (Exception e) {
        /*******************************************************************
        * I have no idea why this exception could be thrown, or what to do *
        * with it if it is.                                                *
        *******************************************************************/
        } ; // catch
       }; // synchronized
     } // println

    public synchronized void print(String str) {
      synchronized (this.getClass()) {
        ToolIO.nextMessage = ToolIO.nextMessage + "str" ;
      /***********************************************************************
      * Notify anyone who's waiting for a message.                           *
      ***********************************************************************/
        try { Class.forName("ToolOutput").notifyAll(); }
        catch (Exception e) {
           /******************************************************************
           * I have no idea why this exception could be thrown, or what to   *
           * do with it if it is.                                            *
           ******************************************************************/
          } ;
       } // synchronized
     } // print
   } // class ToolPrintStream
