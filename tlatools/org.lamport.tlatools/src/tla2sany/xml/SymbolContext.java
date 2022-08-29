package tla2sany.xml;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.TheoremNode;

/* TL
 * This class is used to track the occurrence of SymbolNodes
 * nodes which have a context (modules, nonleafproofs, etc.)
 * create a new instance of this class and pass it over
 * to be populated with values.
 * The oldKeys set is used in order to prevent entering the
 * same def twice
 */
public class SymbolContext {
    // flags list
    public static final int OTHER_BUG = 0;
    private final java.util.Map<Integer, Element> context;
    private final java.util.Set<Integer> keys; // we need this set since the generated element might spawn new keys
    // only set in put() and reset in SymbolNode.getDefinitionElement
    // some semantic objects are represented using null. this flags array
    // is used to tell nodes to expect them so xml exporting will be done properly
    private final boolean[] flagArray;
    private boolean top_level_entry;  // used to detect if a symbol is exported twice.

    public SymbolContext() {
        context = new java.util.HashMap<>();
        keys = new java.util.HashSet<>();
        flagArray = new boolean[1];
        top_level_entry = false;
    }

    // copy concstructor
    public SymbolContext(final SymbolContext other) {
        context = other.context;
        keys = other.keys;
        flagArray = other.flagArray;
        top_level_entry = other.top_level_entry;
    }

    public void setFlag(final int flag) {
        flagArray[flag] = true;
    }

    public boolean hasFlag(final int flag) {
        return flagArray[flag];
    }

    public void put(final SymbolNode nd, final Document doc) {
        final Integer k = nd.myUID;
        if (!keys.contains(k)) {
            // first add the key as it might be mentioned again inside the definition
            keys.add(k);
            setTop_level_entry();
            context.put(k, nd.exportDefinition(doc, this));
        }
    }

    public void put(final TheoremNode nd, final Document doc) {
        final Integer k = nd.myUID;
        if (!keys.contains(k)) {
            // first add the key as it might be mentioned again inside the definition
            keys.add(k);
            setTop_level_entry();
            context.put(k, nd.exportDefinition(doc, this));
        }
    }

    public void put(final AssumeNode nd, final Document doc) {
        final Integer k = nd.myUID;
        if (!keys.contains(k)) {
            // first add the key as it might be mentioned again inside the definition
            keys.add(k);
            setTop_level_entry();
            context.put(k, nd.exportDefinition(doc, this));
        }
    }

    public Element getContextElement(final Document doc) {
        final Element ret = doc.createElement("context");
        for (final java.util.Map.Entry<Integer, Element> entry : context.entrySet()) {
            final Element e = doc.createElement("entry");
            final Element id = doc.createElement("UID");
            id.appendChild(doc.createTextNode(entry.getKey().toString()));
            e.appendChild(id);
            e.appendChild(entry.getValue());
            ret.appendChild(e);
        }
        return ret;
    }

    public int getContextSize() {
        return context.size();
    }

    public boolean isTop_level_entry() {
        return top_level_entry;
    }

    public void setTop_level_entry() {
        top_level_entry = true;
    }

    public void resetTop_level_entry() {
        top_level_entry = false;
    }

}
