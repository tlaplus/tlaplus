// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

public interface ExternalSortable /* extends Comparable -- eliminated 12 Jan 09 because it creates an error in Java 1.6 */ {
  public BigInt read(InputStream in) throws IOException;
  public void write(OutputStream out) throws IOException;
}

