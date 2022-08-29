// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.xml.SymbolContext;

import java.math.BigDecimal;
import java.util.Hashtable;

/**
 * Describes a decimal like 1347.052.  This number is represented by the
 * values
 * <p>
 * long mantissa() = 1347052
 * int  exponent() = -3
 * BigDecimal bigVal() = null
 * <p>
 * so its value is mantissa() * 10^(exponent).  However, if the number
 * can't be represented in this way, then bigVal() is the value as a
 * BigDecimal and the other fields are meaningless.
 * <p>
 * If bigVal() equals null, then mantissa() is either a positive integer
 * not divisible by 10, or else it equals 0 and exponent() equals 0.
 */
public class DecimalNode extends ExprNode {

    private final String image;
    private long mantissa;
    private int exponent;
    private BigDecimal bigVal = null;

    // Bug: should remove trailing 0's from b ?
    public DecimalNode(final String a, final String b, final TreeNode stn) {
        super(DecimalKind, stn);
        image = a + "." + b;
        try {
            this.mantissa = Long.parseLong(a + b);
            this.exponent = -b.length();
        } catch (final NumberFormatException e) {
            this.bigVal = new BigDecimal(image);
        }
    }

    /**
     * Returns the mantissa of the decimal number, i.e its value after scaling
     * by a power of 10 until the fractional part is zero; e.g. the mantissa of
     * 1.23 is 123.
     */
    public final long mantissa() {
        return this.mantissa;
    }

    /**
     * The power of 10 which, when multiplied by the mantissa, yields the original number,
     * e.g. the exponent of 1.23 is -2.
     */
    public final int exponent() {
        return this.exponent;
    }

    /**
     * Returns the number in BigDecimal form
     */
    public final BigDecimal bigVal() {
        return this.bigVal;
    }

    /**
     * Returns the value as a string, exactly the way the user typed it--e.g.,
     * without any normalization, removal of leading or trailing zero's, etc.
     */
    @Override
    public final String toString() {
        return this.image;
    }

    /* Level checking */
    @Override
    public final boolean levelCheck(final int iter) {
        levelChecked = iter;
        /*********************************************************************
         * Set it just to show that levelCHeck was called.                    *
         *********************************************************************/
        return true;
    }

/**
 *  toString, levelDataToString(), and walkGraph methods to implement
 *  ExploreNode interface
 */

    /**
     * walkGraph finds all reachable nodes in the semantic graph and
     * inserts them in the Hashtable semNodesTable for use by the
     * Explorer tool.
     */
    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        final Integer uid = myUID;
        if (semNodesTable.get(uid) != null) return;

        semNodesTable.put(uid, this);
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    /**
     * Displays this node as a String, implementing ExploreNode
     * interface; depth parameter is a bound on the depth of the portion
     * of the tree that is displayed.
     */
    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";
        return ("\n*DecimalNode" + super.toString(depth) + "Mantissa: "
                + mantissa + "; exponent: " + exponent
                + "; big value: " + (bigVal != null ? bigVal.toString() : "<null>")
                + "\n; image = " + image
        );
    }

    @Override
    protected Element getLevelElement(final Document doc, final SymbolContext context) {
        final Element e = doc.createElement("DecimalNode");
        if (bigVal != null) {
            e.appendChild(appendText(doc, "mantissa", bigVal.unscaledValue().toString()));
            e.appendChild(appendText(doc, "exponent", Integer.toString(bigVal.scale())));
        } else {
            e.appendChild(appendText(doc, "mantissa", Long.toString(mantissa)));
            e.appendChild(appendText(doc, "exponent", Integer.toString(exponent)));
        }
        return e;
    }
}
