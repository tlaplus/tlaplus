package pcal;

import java.util.Vector;
import util.ToolIO;

/***************************************************************************
* This class provides methods called when an error is encountered,         
* methods for printing debugging output, and methods for measuring and     
* reporting elapsed time.                                                  
* @author Leslie Lamport
* @version Id
***************************************************************************/
public class PcalDebug
{
    public static void ReportError(String msg)
    /*********************************************************************
    * This method is called to report an error and abort.                *
    *********************************************************************/
    {
        ToolIO.out.println("");
        ToolIO.out.println("Unrecoverable error:");
        ToolIO.out.println("");
        ToolIO.out.println(" -- " + msg + ".");
        ToolIO.out.println("");
        throw new PCalUnrecoverableErrorRuntimeException("Report error has been called");
    };

    public static void ReportErrorAt(String msg, AST ast)
    /*********************************************************************
    * This method is called to report an error in the object ast and     *
    * abort.                                                             *
    *                                                                    *
    * Corrected 4 Mar 2006 by LL to use AST.location.                    *
    *********************************************************************/
    {
        if (ast.line == 0)
            ReportError(msg);
        ReportError(msg + "\n    at " + ast.location());
    };

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
    };

}
/* last modified on Sat  4 Mar 2006 at 10:15:03 PST by lamport */
