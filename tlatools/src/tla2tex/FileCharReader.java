// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS FileCharReader EXTENDS CharReader                                  *
*                                                                          *
* This class provides a CharReader for a file, using the                   *
* java.io.BufferedReader class.  (See the CharReader class.)               *
***************************************************************************/
package tla2tex;
import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;

public class FileCharReader extends CharReader
  { private BufferedReader bufferedReader ;
      /*********************************************************************
      * This is the BufferedReader object providing the input characters.  *
      *********************************************************************/

    public FileCharReader(String fileName) 
      /*********************************************************************
      * The class constructor.  The fileName argument is the name of the   *
      * file.  It exits TLATeX if the file cannot be found.                *
      *********************************************************************/
      { try { bufferedReader = 
                  new BufferedReader(new InputStreamReader(
                                          new FileInputStream(fileName))) ;
            }
        catch (FileNotFoundException e)
           { /**************************************************************
             * File fileName could not be found.                           *
             **************************************************************/
             Debug.ReportError("Input file " + fileName + " not found.");
           } ;
      } ;

    public String innerGetNextLine()
      /*********************************************************************
      * The abstract innerGetNextLine method of CharReader is implemented  *
      * with the readLine method of java.io.BufferedReader.  It aborts     *
      * TLATeX if there is an IOException.                                 *
      *********************************************************************/
      { try {return bufferedReader.readLine();}
        catch (IOException e)
          { Debug.ReportError("Error reading file: " + e.getMessage());
          };

        /*******************************************************************
        * The following return statement is silly, since it is never       *
        * reached.  But the compiler isn't clever enough to notice that    *
        * it's not needed.                                                 *
        *******************************************************************/
        return null ;

      } ;

    public void close()
      /*********************************************************************
      * Implements CharReader's abstract close() method.                   *
      *********************************************************************/
      { try {bufferedReader.close();}
        catch (IOException e)
          { Debug.ReportError("Error trying to close file: " + e.getMessage());
          };
      };
  }
