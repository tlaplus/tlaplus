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
   * @param expandDefinitions is used to tell nested node if we want to expand definitions. For example, we want to expand them when they are defined but only use their names when we use them.
   */
  public Element export(Document doc, boolean expandDefinitions);
  public Element export(Document doc);
}
