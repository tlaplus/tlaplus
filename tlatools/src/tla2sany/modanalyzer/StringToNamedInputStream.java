// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import java.io.*;

/**
 * This interface contains a single method toIStream that maps a name to
 * a NamedInputStream.  (See the FrontEnd class's parseStream method for 
 * how it is used.)                                                      
 */
public interface StringToNamedInputStream {
  public NamedInputStream toIStream(String name);
}
