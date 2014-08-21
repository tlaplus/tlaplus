// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;

/**
 * an interface for being able to export XML content
 */

import org.w3c.dom.Element;
import org.w3c.dom.Document;

public interface XMLExportable {
  public Element export(Document doc, boolean expandDefinitions);
  public Element export(Document doc);

  // this two are internal and should not be called.
  public Element getElement(Document doc, boolean expandDefinitions);
  public Element getElement(Document doc);
}
