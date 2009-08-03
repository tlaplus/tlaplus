// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.st;

import util.UniqueString;

/**
 *  A location specifies the position of a syntactic unit in the source.
 *  A location consists of beginning and ending line and column numbers 
 *  and a source name--usually the name of the file from which the input
 *  comes.                                                              
 */

public final class Location {
  protected UniqueString name; 
  protected int bLine, bColumn, eLine, eColumn;

  static private UniqueString unknown = UniqueString.uniqueStringOf( "--unknown--" );

  /* Constructors */ 
  public Location(int bl, int bc, int el, int ec) {
    name = unknown;
    bLine = bl;
    bColumn = bc;
    eLine = el;
    eColumn = ec;
  }
  public Location(UniqueString fName, int bl, int bc, int el, int ec) {
    name = fName;
    bLine = bl;
    bColumn = bc;
    eLine = el;
    eColumn = ec;
  } 

  public static final Location nullLoc = new Location(0,0,0,0);

  /**
   * Factory method to create unknown locations in a given module
   * @param moduleName, string representation of the module name
   * @return
   */
  public static final Location moduleLocation(String moduleName) 
  {
      return new Location(UniqueString.uniqueStringOf(moduleName), 0,0,0,0);
  }
  
  /** gets the begin line number of this location. */
  public final int beginLine() { return this.bLine; }

  /** gets the begin column number of this location. */
  public final int beginColumn() { return this.bColumn; } 

  /** gets the end line number of this location. */
  public final int endLine() { return this.eLine; }
 
  /** gets the end column number of this location. */
  public final int endColumn() { return this.eColumn; }

  /** gets the file name of this location. */
  public final String source() { return name.toString(); }

  /**
   * This method should be called by all tools to print the location, so
   * users see a consistent method of identifying a location.  I        
   * recommend something like                                           
   *                                                                    
   *   line 17, col 22 to line 18, col 13 of module Foo                   
   *                                                                    
   * where source() = "Foo".                                       
   */
  public final String toString() 
  {
      if (this == nullLoc) 
      {
          return "Unknown location";
      } else if (!this.name.equals(unknown) && (this.bColumn == 0 && this.eColumn == 0 && this.bLine == 0 && this.eLine == 0)) 
      {
          return "Unknown location in module " + name; 
      } else 
      {
          return ("line " + bLine + ", col " + bColumn + " to line " + eLine + 
                  ", col " + eColumn + " of module " + name);
      }
  }
}  
