/**
 * A Location is a line, column pair of integers.  It represents
 * a location in the .tla file.  The column is a Java position
 * (starting from 0); a line may be relative to some anchoring
 * line.
 */
package pcal;

import java.io.Serializable;

/**
 * @author lamport
 *
 */
public class PCalLocation implements Serializable {

    private static final long serialVersionUID = 5224570720345403320L;
    private final int column;
    private int line;

    public PCalLocation(final int line, final int column) {
        this.line = line;
        this.column = column;
    }

    public int getLine() {
        return line;
    }

    public void adjustLineBy(final int l) {
        line -= l;
    }

    public int getColumn() {
        return column;
    }

    public int getOffset() {
        return line + column;
    }

    public String toString() {
//		return "[line |-> " + line + ", column |-> " + column + "]" ;
        return "(" + line + ", " + column + ")";
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + column;
        result = prime * result + line;
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        final PCalLocation other = (PCalLocation) obj;
        if (column != other.column)
            return false;
        return line == other.line;
    }

}
