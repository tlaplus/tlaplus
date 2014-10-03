// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;

/**
 * an interface for being able to export XML content
 */

import org.w3c.dom.Element;
import org.w3c.dom.Document;

public interface XMLExportable {
  /** an object extending this interface is exported into an XML element using these two methods.
   * These are wrapper methods calling the getElement in order to generate the actual element
   * and wrapping it inside general information such as location, which is common to all elements
   * @param doc is the Document used to generate elements
   */
  public Element export(Document doc);
}
