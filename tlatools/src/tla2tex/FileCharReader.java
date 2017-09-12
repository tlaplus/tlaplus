// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS FileCharReader EXTENDS CharReader                                  *
*                                                                          *
* This class provides a CharReader for a file, using the                   *
* java.io.BufferedReader class.  (See the CharReader class.)               *
***************************************************************************/
package tla2tex;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;

public class FileCharReader extends InputStreamCharReader
  { 
    public FileCharReader(String fileName) 
      /*********************************************************************
      * The class constructor.  The fileName argument is the name of the   *
      * file.  It exits TLATeX if the file cannot be found.                *
      *********************************************************************/
      { super(openFile(fileName));
      }
      
      private static InputStream openFile(String fileName) {
    	  try { return new FileInputStream(fileName) ;
          } catch (FileNotFoundException e)
           { /**************************************************************
             * File fileName could not be found.                           *
             **************************************************************/
             Debug.ReportError("Input file " + fileName + " not found.");
             throw new AssertionError(); // appease the compiler;
           }
      }
  }
