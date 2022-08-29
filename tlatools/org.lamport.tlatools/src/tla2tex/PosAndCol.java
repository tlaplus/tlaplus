// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
 * CLASS PosAndCol                                                          *
 *                                                                          *
 * A PosAndCol object is a Position extended by a column field.  It has a   *
 * the method:                                                              *
 *                                                                          *
 *   void sort(PosAndCol[] array)                                           *
 *                                                                          *
 *      Sorts the array first by column and, within column, by line.        *
 ***************************************************************************/
package tla2tex;

public class PosAndCol extends Position implements Comparable<PosAndCol> {
    public final int column;

    public PosAndCol(final int l, final int i, final int c) {
        item = i;
        line = l;
        column = c;
    }


    @Override
    public String toString() {
        return "[line |-> " + line + ", item |-> " + item
                + ", col |-> " + column + "]";
    }

    @Override
    public int compareTo(final PosAndCol other) {
        if (column == other.column) {
            return Integer.compare(line, other.line);
        }
        return Integer.compare(column, other.column);
    }
}

/* Last modified on Tue 18 Sep 2007 at  6:51:12 PST0by lamport */
