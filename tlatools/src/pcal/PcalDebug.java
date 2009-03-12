package pcal;

import java.util.Vector;

import pcal.exception.UnrecoverableException;
import pcal.exception.UnrecoverablePositionedException;
import util.ToolIO;

/***************************************************************************
* This class provides methods called when an error is encountered,         
* methods for printing debugging output, and methods for measuring and     
* reporting elapsed time.                                                  
* @author Leslie Lamport
* @version $Id$
***************************************************************************/
public class PcalDebug
{
    public static final String UNRECOVERABLE_ERROR = "\nUnrecoverable error:\n -- ";
    public static final String WARNING = "Warning: ";
    public static final String ERROR_POSTFIX = ".\n";

    /**
     * Printer for the exceptions
     * @param exception containing the message to print
     */
    public static void reportError(UnrecoverableException e)
    {
        if (e instanceof UnrecoverablePositionedException)
        {
            reportError(e.getMessage(), ((UnrecoverablePositionedException) e).getPosition());
        } else
        {
            reportError(e.getMessage());
        }
    };

    /**
     * Reports a warning 
     * @param warningText text to be reported
     */
    public static void reportWarning(String warningText)
    {
        ToolIO.out.println(new StringBuffer(WARNING).append(warningText));
    }

    /**
     * Reports a information for the user
     * @param infoText text to be reported
     */
    public static void reportInfo(String infoText)
    {
        ToolIO.out.println(infoText);
    }

    /**
     * Report error message 
     * @param message message to report
     */
    public static void reportError(String message)
    {
        ToolIO.out.println(new StringBuffer(UNRECOVERABLE_ERROR).append(message).append(ERROR_POSTFIX).toString());
    }

    /**
     * Reports an error
     * @param message message to report
     * @param ast the AST-object identifying the error location
     */
    public static void reportError(String message, AST ast)
    {
        if (ast == null || ast.line == 0)
        {
            reportError(message);
        } else {
            reportError(message + "\n    at " + ast.location());
        }
    }

    public static void Assert(boolean val)
    /*********************************************************************
    * Why doesn't java provide an Assert statement?                      *
    *********************************************************************/
    {
        if (!val)
        {
            ReportBug("Assertion failure");
        }
        ;
    };

    public static void Assert(boolean val, String msg)
    /*********************************************************************
    * An Assert with an error message.                                   *
    *********************************************************************/
    {
        if (!val)
        {
            ReportBug("Failure of assertion: " + msg);
        }
        ;
    };

    public static void ReportBug(String msg)
    /*********************************************************************
    * This method is called to report a bug in the program and abort.    *
    *********************************************************************/
    {
        ToolIO.out.println("");
        ToolIO.out.println("You have discovered a bug in pcal.trans.");
        ToolIO.out.println("Send the following information and the");
        ToolIO.out.println("input file to the current maintainer(s).");
        ToolIO.out.println("");
        ToolIO.out.println(" -- " + msg + ".");
        ToolIO.out.println("");
        throw new Error();
    };

    public static void printObjectArray(Object[] array, String name)
    /*********************************************************************
    * This method prints to standard output the contents of the array    *
    * argument, where name is the name of the array.                     *
    *********************************************************************/
    {
        if (array == null)
        {
            ToolIO.out.println(name + " == null");
            return;
        }
        ;
        int i = 0;
        while (i < array.length)
        {
            if (array[i] == null)
            {
                ToolIO.out.println(name + "[" + i + "] = null");
            } else
            {
                ToolIO.out.println(name + "[" + i + "] = " + array[i].toString());
            }
            i = i + 1;
        }
        ;
        if (array.length == 0)
        {
            ToolIO.out.println(name + " = zero-length array");
        }
        ;
    };

    public static void printIntArray(int[] array, String name)
    /*********************************************************************
    * This method prints to standard output the contents of the array    *
    * argument, where name is the name of the array.                     *
    *********************************************************************/
    {
        if (array == null)
        {
            ToolIO.out.println(name + " == null");
            return;
        }
        ;
        int i = 0;
        while (i < array.length)
        {
            ToolIO.out.println(name + "[" + i + "] = " + array[i]);
            i = i + 1;
        }
        ;
        if (array.length == 0)
        {
            ToolIO.out.println(name + " = zero-length array");
        }
        ;
    };

    public static void print2DArray(Object[][] array, String name)
    /*********************************************************************
    * This method prints to standard output the contents of the array    *
    * argument, where name is the name of the array.                     *
    *********************************************************************/
    {
        if (array == null)
        {
            ToolIO.out.println(name + " == null");
            return;
        }
        ;
        int i = 0;
        while (i < array.length)
        {
            int j = 0;
            while (j < array[i].length)
            {
                ToolIO.out.println(name + "[" + i + "][" + j + "] = " + array[i][j].toString());
                j = j + 1;
            }
            ;
            if (array[i].length == 0)
            {
                ToolIO.out.println(name + "[" + i + "] = null");
            }
            ;
            i = i + 1;
        }
        ;
        if (array.length == 0)
        {
            ToolIO.out.println(name + " = zero-length array");
        }
        ;
    };

    public static void printVector(Vector vec, String name)
    /*********************************************************************
    * This method prints to standard output the contents of the vector   *
    * argument, where name is the name of the vector.                    *
    *********************************************************************/
    {
        if (vec == null)
        {
            ToolIO.out.println(name + " == null");
            return;
        }
        ;
        int i = 0;
        while (i < vec.size())
        {
            if (vec.elementAt(i) == null)
            {
                ToolIO.out.println(name + "[" + i + "] = null");
            } else
            {
                ToolIO.out.println(name + "[" + i + "] = " + vec.elementAt(i).toString());
            }
            i = i + 1;
        }
        ;
        if (vec.size() == 0)
        {
            ToolIO.out.println(name + " = zero-length vec");
        }
        ;
    };

    public static void print2DVector(Vector vec, String name)
    /*********************************************************************
    * This method prints to standard output the contents of its vector   *
    * argument, which is a vector of vectors, where name is the name of  *
    * the vector.                                                        *
    *********************************************************************/
    {
        if (vec == null)
        {
            ToolIO.out.println(name + " == null");
            return;
        }
        ;
        int i = 0;
        while (i < vec.size())
        {
            if (vec.elementAt(i) == null)
            {
                ToolIO.out.println(name + "[" + i + "] = null");
            } else
            {
                printVector((Vector) vec.elementAt(i), name + "[" + i + "]");
            }
            ;
            i = i + 1;
        }
        ;
        if (vec.size() == 0)
        {
            ToolIO.out.println(name + " = zero-length vec");
        }
        ;
    };

    public static String pair(int i, int j)
    /*********************************************************************
    * Just a convenient little function.                                 *
    *********************************************************************/
    {
        return "(" + i + ", " + j + ")";
    };

    public static void printPair(int i, int j)
    /*********************************************************************
    * Just prints "(i, j)".                                              *
    *********************************************************************/
    {
        ToolIO.out.println(pair(i, j));
    }

}
/* last modified on Sat  4 Mar 2006 at 10:15:03 PST by lamport */
