package tla2sany.xml;

import tla2sany.semantic.SymbolNode;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

/* TL
 * This class is used to track the occurrence of SymbolNodes
 * nodes which have a context (modules, nonleafproofs, etc.)
 * create a new instance of this class and pass it over
 * to be populated with values.
 * The oldKeys set is used in order to prevent entering the
 * same def twice
 */
public class SymbolContext {
  private java.util.Map<Integer,Element> context;
  private java.util.Set<Integer> keys; // we need this set since the generated element might spawn new keys

  public SymbolContext() {
    context = new java.util.HashMap<Integer,Element>();
    keys = new java.util.HashSet<Integer>();
  }

  public void put(SymbolNode nd, Document doc) {
    Integer k = new Integer(nd.myUID);
    if (!keys.contains(k)) {
      // first add the key as it might be mentioned again inside the definition
      keys.add(k);
      context.put(k,nd.exportDefinition(doc,this));
    }
  }

  public Element getContextElement(Document doc) {
    Element ret = doc.createElement("context");
    for (java.util.Map.Entry<Integer, Element> entry : context.entrySet()) {
      Element e = doc.createElement("entry");
      Element id = doc.createElement("UID");
      id.appendChild(doc.createTextNode(entry.getKey().toString()));
      e.appendChild(id);
      e.appendChild(entry.getValue());
      ret.appendChild(e);
    }
    return ret;
  }
}
