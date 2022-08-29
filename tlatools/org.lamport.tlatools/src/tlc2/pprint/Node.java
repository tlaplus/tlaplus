// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:20:57 PST by lamport
//      modified on Fri Jun 11 17:51:46 PDT 1999 by yuanyu
//      modified on Thu Jun 10 14:52:19 EDT 1999 by tuttle

package tlc2.pprint;

public class Node {

    public static final int CONSTANT = 1;
    public static final int SET = 2;
    public static final int SEQUENCE = 3;
    public static final int RECORD = 4;
    public static final int RECORDPAIR = 5;
    public static final int FUNCTION = 6;
    public static final int FUNCTIONPAIR = 7;
    public static final int SUBSET = 8;

    private int type;
    private int first;
    private int last;
    private Node children;
    private Node next;
    private String string;
    private String formatted;

    /***************************************************************************/

    Node(final String str, final int s, final int t) {
        string = str;
        type = t;
        first = s;
        last = 0;
        children = null;
        next = null;
        formatted = null;
    }

    Node(final String str, final int s, final int e, final int t) {
        string = str;
        type = t;
        first = s;
        last = e;
        children = null;
        next = null;
        formatted = null;
    }

    /***************************************************************************/

    public int type() {
        return type;
    }

    public int first() {
        return first;
    }

    public int last() {
        return last;
    }

    public Node children() {
        return children;
    }

    public Node next() {
        return next;
    }

    public String string() {
        return string;
    }

    public String formatted() {
        return formatted;
    }

    /***************************************************************************/

    public void type(final int t) {
        type = t;
    }

    public void first(final int s) {
        first = s;
    }

    public void last(final int e) {
        last = e;
    }

    public void children(final Node c) {
        children = c;
    }

    public void next(final Node n) {
        next = n;
    }

    public void string(final String s) {
        string = s;
    }

    public void formatted(final String s) {
        formatted = s;
    }

    /***************************************************************************/

    public String value() {
        return string.substring(first, last + 1);
    }

    public int length() {
        return last - first + 1;
    }

    public void appendChild(final Node n) {
        Node ch = this.children();

        if (ch == null) {
            this.children(n);
            return;
        }

        while (ch.next() != null) {
            ch = ch.next();
        }
        ch.next(n);
    }

    public String toString() {
        final StringBuilder s = new StringBuilder();

        for (Node ch = children(); ch != null; ch = ch.next()) {
            s.append(ch);
        }
        return s.toString() + first() + " " + last() + " " + value() + "\n";
    }

/***************************************************************************/

}
