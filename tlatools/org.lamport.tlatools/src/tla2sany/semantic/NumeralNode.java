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

import java.math.BigInteger;
import java.util.Hashtable;

/**
 * Describes a numeral like 4095.  This number is represented by the
 * values
 * <p>
 * int val()          = 4095
 * BigInteger bigVal() = null
 * <p>
 * However, if the number is too big to be represented as an
 * integer, then its value is bigVal() and the value of val() is
 * meaningless.
 */
public class NumeralNode extends ExprNode {

    private final String image;
    private int value;
    private BigInteger bigValue = null;

    /**
     * The following method was modified by LL on 20 Jul 2011 to handle
     * \b, \o, and \h numbers.
     */
    public NumeralNode(final String s, final TreeNode stn) throws AbortException {
        super(NumeralKind, stn);
        this.image = s;
        String num = s.toLowerCase();
        int radix = 10;
        if (num.charAt(0) == '\\') {
            if (num.charAt(1) == 'b') {
                radix = 2;
            } else if (num.charAt(1) == 'o') {
                radix = 8;
            } else if (num.charAt(1) == 'h') {
                radix = 16;
            } else {
                throw new AbortException();  // This shouldn't happen.
            }
            num = num.substring(2);
        }
        try {

            this.value = Integer.parseInt(num, radix);
        } catch (final NumberFormatException e) {
            this.bigValue = new BigInteger(s, radix);
        }
    }

    public final int val() {
        return this.value;
    }

    public final BigInteger bigVal() {
        return this.bigValue;
    }


    /**
     * Returns the value as a string--for example, "4095".  This string
     * reflects how the value appeared in the input, so it should be
     * "\O7777" if that's what appears in the source.
     */
    @Override
    public final String toString() {
        return this.image;
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
     * toString, levelDataToString, and walkGraph methods to implement
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

    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";

        return ("\n*NumeralNode: " + super.toString(depth) + " Value: " + value +
                (bigValue != null ? ("; big value: " + bigValue) : "") +
                "; image: " + image);
    }

    @Override
    protected Element getLevelElement(final Document doc, final SymbolContext context) {
        final String v = (bigValue != null) ? bigValue.toString() : (Integer.toString(value));
        final Element e = doc.createElement("IntValue");
        final Node n = doc.createTextNode(v);
        e.appendChild(n);
        return appendElement(doc, "NumeralNode", e);
        //return appendText(doc,"NumeralNode",(bigValue != null) ? bigValue.toString() : (Integer.toString(value)));
    }
}

