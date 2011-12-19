/**
 * A Location is a line, column pair of integers.  It represents 
 * a location in the .tla file.  The column is a Java position
 * (starting from 0); a line may be relative to some anchoring 
 * line.
 *
 */
package pcal;

/**
 * @author lamport
 *
 */
public class PCalLocation {
	
	private int line;
	
	private int column;
	
	public PCalLocation(int line, int column) {
		this.line = line;
		this.column = column;
	}

	public int getLine() {
		return line;
	}

	public int getColumn() {
		return column;
	}
	
	public String toString() {
//		return "[line |-> " + line + ", column |-> " + column + "]" ;
		return "(" + line + ", " + column +")" ;
	}

}
