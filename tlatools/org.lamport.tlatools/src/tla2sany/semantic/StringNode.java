// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.xml.SymbolContext;
import util.UniqueString;

import java.util.Hashtable;


/**
 * This node represents a string literal in the specification--for
 * example "abc".  The only information added to the SemanticNode
 * superclass is the level information and the UniqueString
 * representation of the string.
 */

public class StringNode extends ExprNode implements ExploreNode {

    private UniqueString value;

    public StringNode(final TreeNode stn, final boolean strip) {
        super(StringKind, stn);

        this.value = stn.getUS();
        if (strip) {
            // Strip off quote marks from image in stn
            String str = this.value.toString();
            str = str.substring(1, str.length() - 1);
            this.value = UniqueString.uniqueStringOf(str);
            /*********************************************************************
             * Setting levelChecked shouldn't be necessary.                       *
             *********************************************************************/
//      this.levelChecked = 99 ;
        }
    }

    /**
     * Returns the UniqueString representation of the string.
     */
    public final UniqueString getRep() {
        return this.value;
    }

    /* Level Checking */
    @Override
    public final boolean levelCheck(final int iter) {
        levelChecked = iter;
        /*********************************************************************
         * Set it just to show that levelCHeck was called.                    *
         *********************************************************************/
        return true;
    }

    /**
     * toString, levelDataToString, & walkGraph methods to implement
     * ExploreNode interface
     */

    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        final Integer uid = myUID;
        if (semNodesTable.get(uid) != null) return;

        semNodesTable.put(uid, this);
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    final String PrintVersion(final String str) {
        final StringBuilder buf = new StringBuilder(str.length());
        for (int i = 0; i < str.length(); i++) {
            switch (str.charAt(i)) {
                case '\"' -> buf.append("\\\"");
                case '\\' -> buf.append("\\\\");
                case '\t' -> buf.append("\\t");
                case '\n' -> buf.append("\\n");
                case '\f' -> buf.append("\\f");
                case '\r' -> buf.append("\\r");
                default -> buf.append(str.charAt(i));
            } // switch
        }// for
        return buf.toString();
    }

    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";
        return "\n*StringNode: " + super.toString(depth)
                + "Value: '" + PrintVersion(value.toString()) +
                "'" + " Length: " + value.length();
    }

    @Override
    protected Element getLevelElement(final Document doc, final SymbolContext context) {
        final Element e = doc.createElement("StringValue");
        final Node n = doc.createTextNode(value.toString());
        e.appendChild(n);
        return appendElement(doc, "StringNode", e);
        // return appendText(doc,"StringNode",value.toString());
    }
}
