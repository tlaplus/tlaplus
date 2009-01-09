// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS ResourceFileReader                                                 *
*                                                                          *
* A ResourceFileReader returns an object for reading a resource file,      *
* which is a file kept in the same directory as the tlatex.Token class.    *
* The constructor takes a file name as argument.  The object's two public  *
* methods are                                                              *
*                                                                          *
*   getLine() : Returns the next line of the file as a string.  Returns    *
*               null after the last line.                                  *
*                                                                          *
*   close()   : Closes the file.                                           *
***************************************************************************/
package tla2tex;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;

public class ResourceFileReader
  { public ResourceFileReader(String fileName)
      /*********************************************************************
      * The constructor, where fileName is the name of a file that's       *
      * in the same directory as tlatex.Token.                             *
      *********************************************************************/
     { name = fileName ;
       Class cl = null ;
       try { cl = Class.forName("tla2tex.Token"); }
       catch (ClassNotFoundException e)
           { Debug.ReportError( 
               "Java could not find class tla2tex.Token.  There \n"
             + "    is probably something wrong with the way\n"
             + "    TLA2TeX is installed");
           } ;             
       InputStream input = cl.getResourceAsStream(fileName) ; 
       if (input == null)
         { Debug.ReportError( 
               "TLATeX could not find its resource file " + fileName + ".\n"
             + "    There is probably something wrong with the way\n"
             + "    TLA2TeX is installed");
         } ;  
       inputReader = new BufferedReader(new InputStreamReader(input)) ;
      };

    public String getLine()
      /*********************************************************************
      * Returns the next line of input.  After it returns the last line    *
      * of input, it returns null.                                         *
      *********************************************************************/
      { try { return inputReader.readLine();
            }
        catch (java.io.IOException e)
          { Debug.ReportError( 
                   "Error reading the TLATeX resource file " + name + ".\n"
                 + "    You may be having file system problems");
          } ; 
        return null ;
      }
    private boolean done = false;
      /*********************************************************************
      * If the last line of input doesn't end with a '\n', then getLine()  *
      * returns that line and sets done to true.                           *
      *********************************************************************/

    private BufferedReader inputReader ;
      /*********************************************************************
      * The actual reader for the resource file.                           *
      *********************************************************************/

    private String name ;
      /*********************************************************************
      * A copy of the resource file name, kept for error messages.         *
      *********************************************************************/
      
    public void close()
      { try { inputReader.close(); }
        catch (java.io.IOException e)
          { Debug.ReportError( 
               "Error trying to close the TLATeX resource file " + name + ".\n"
             + "    You may be having file system problems");
          } ;
      } ;


  }      


/* Last modified on Tue 18 Sep 2007 at  6:59:51 PST by lamport */
