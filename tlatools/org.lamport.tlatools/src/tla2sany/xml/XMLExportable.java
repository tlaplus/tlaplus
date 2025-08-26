// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;

import java.util.function.BiPredicate;

import org.w3c.dom.Document;

/**
 * an interface for being able to export XML content
 */

import org.w3c.dom.Element;

import tla2sany.semantic.SemanticNode;

public interface XMLExportable {

  /** an object extending this interface is exported into an XML element using these two methods.
   * These are wrapper methods calling the getElement in order to generate the actual element
   * and wrapping it inside general information such as location, which is common to all elements
   * @param doc is the Document used to generate elements
   */
  public Element export(Document doc, SymbolContext context, BiPredicate<SemanticNode, SemanticNode> filter);
  
  default public Element export(Document doc, SymbolContext context) {
	  return this.export(doc, context, (a, b) -> true);
  }
}
