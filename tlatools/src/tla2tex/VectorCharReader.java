// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS VectorCharReader EXTENDS CharReader                                *
*                                                                          *
* This class turns a vector of strings into a CharReader.  (See the        *
* CharReader class.)                                                       *
***************************************************************************/
package tla2tex;
import java.util.Vector;

public class VectorCharReader extends CharReader
  { private Vector vec ;
      /*********************************************************************
      * This is the vector providing the input characters.                 *
      *********************************************************************/

    private int nextLine = 0 ;
      /*********************************************************************
      * The next element of vec to be returned by innerGetNextLine.        *
      *********************************************************************/
      
    public VectorCharReader(Vector vector, int firstLine) 
      /*********************************************************************
      * The class constructor.  The fileName argument is the name of the   *
      * file.  It exits TLATeX if the file cannot be found.                *
      *********************************************************************/
      { this.line = firstLine ;
        this.vec = vector ;
      } ;

    public String innerGetNextLine()
      /*********************************************************************
      * The abstract innerGetNextLine method of CharReader is implemented  *
      * with the readLine method of java.io.BufferedReader.  It aborts     *
      * TLATeX if there is an IOException.                                 *
      *********************************************************************/
      { if (nextLine == vec.size())
         { return null ; } ;
        nextLine = nextLine + 1;
        return (String) vec.elementAt(nextLine - 1);
      } ;

    public void close()
      /*********************************************************************
      * Implements CharReader's abstract close() method.                   *
      *********************************************************************/
      { 
      };
  }
