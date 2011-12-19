/**
 *  
 */
package pcal;

import java.util.Vector;

/**
 * A MappingObject is an element in the mapping field of a TLAtoPCalMapping object.
 * It describes either a region in the TLA+ translation or the start or end of a 
 * region in the PlusCal code.  See the TLAToPCal.tla module for a TLA+ specification
 * of what these objects mean.  The correspondence between MappingObject classes and
 * sets in the TLAToPCal spec is:
 * 
 * LeftParen / RightParen :
 *   Elements of Paren with type field  "begin" / "end"
 * 
 * BeginTLAToken / EndTLAToken : 
 *   Represent the beginning and end locations of elements of TLAToken with
 *   inExpr field FALSE.  The line field of the TLAToken element is implicit
 *   in the location of the BeginTLAToken or EndTLAToken object in the mapping.  
 *   Since the TLAToken's regions can span multiple lines, this requires that 
 *   its Java representation be split into these two Java objects.
 *   
 * SourceToken :
 *   Represents an element of TLAToken with inExpr field TRUE, together with
 *   the Parens that surround it.   (The region 
 *   of a TLAToken occupies a single line, so there is no need to split the
 *   Java object.)  Again, the line of the TLAToken is implict in the position
 *   of the ExprToken object in the mapping, so only the token's position and
 *   length is needed in the object
 *   
 * Break :
 *   Represents an element of Break.
 * 
 * @author lamport
 *
 */
public class MappingObject {
    
    /*
     * The type field tells what subclass the MappingObject belongs to
     */
    private int type ;
    
    /*
     * The following are the types of MappingObjects.
     */
    public static final int LEFT_PAREN     = 0;
    public static final int RIGHT_PAREN    = 1;
    public static final int BEGIN_TLATOKEN = 2 ;
    public static final int END_TLATOKEN   = 3 ;
    public static final int SOURCE_TOKEN   = 4 ;
    public static final int BREAK          = 5 ;

    public int getType() {
        return type;
    }

    public void setType(int type) {
        this.type = type;
    }
    
    public MappingObject(int type) {
        this.type = type ;
    }
    
    public static class LeftParen extends MappingObject {
//        private int column ;
        private PCalLocation location ;
        public LeftParen(PCalLocation location) {
           super(LEFT_PAREN) ;
//           this.column = column;
           this.location = location;
        }
        
        public String toString() {
            return "((-" + this.location.toString();
        }

//        public int getColumn() {
//            return column;
//        }

        public PCalLocation getLocation() {
            return location;
        }
    }
    
    public static class RightParen extends MappingObject {
//        private int column ;
        private PCalLocation location ;
        public RightParen(PCalLocation location) {
           super(RIGHT_PAREN) ;
//           this.column = column;
           this.location = location;
        }
        
        public String toString() {
            return this.location.toString() + "-))";
        }

//        public int getColumn() {
//            return column;
//        }

        public PCalLocation getLocation() {
            return location;
        }
    }
    
    public static class BeginTLAToken extends MappingObject {
        private int column ;

        public int getColumn() {
            return column;
        }
        public void setColumn(int column) {
            this.column = column ;
        }
        
        public BeginTLAToken(int column) {
            super(BEGIN_TLATOKEN) ;
            this.column = column ;
        }
        
        public String toString() {
            return "[" + this.column;
        }
    }
    
    public static class EndTLAToken extends MappingObject {
        private int column ;

        public int getColumn() {
            return column;
        }
        public void setColumn(int column) {
            this.column = column ;
        }
        
        public EndTLAToken(int column) {
            super(END_TLATOKEN) ;
            this.column = column ;
        }
        
        public String toString() {
            return this.column + "]";
        }
    }
    
    public static class SourceToken extends MappingObject {
        private int beginColumn ;
        private int endColumn ;
        private Region origin ;
        
        public int getBeginColumn() {
            return beginColumn;
        }

        public void setBeginColumn(int beginColumn) {
            this.beginColumn = beginColumn;
        }

        public int getEndColumn() {
            return endColumn;
        }

        public void setEndColumn(int endColumn) {
            this.endColumn = endColumn;
        }

        public Region getOrigin() {
            return origin;
        }

//        public void setOrigin(Region origin) {
//            this.origin = origin;
//        }

        public SourceToken(int beginCol, int endCol, Region origin) {
            super(SOURCE_TOKEN) ;
            this.setBeginColumn(beginCol) ;
            this.setEndColumn(endCol) ;
            this.origin = origin ;
        }
        
        public String toString() {
            return "((-" + this.origin.getBegin().toString() +
                    "[" + this.beginColumn + "--" + this.endColumn + "]" 
                    + this.origin.getEnd().toString() + "-))";
        }
        
    }
    public static class Break extends MappingObject{
        private int depth ;

        public int getDepth() {
            return depth;
        }
        
        public Break(int depth) {
            super(BREAK) ;
            this.depth = depth;
        }

    }
    
    /**
     * A mapping vector is a vector of vectors of MappingObject
     * objects.  This transforms a mapping vector obtained from a
     * TLAExpr object by a call of toMappingVector to produce the
     * mapping vector that would have resulted from that call if the
     * entire expression had been moved  to the right by `shift'
     * characters.
     *  
     * @param mvec  A mapping vector.
     * @param shift The distance to shift to the right.
     */
    public static void shiftMappingVector(Vector mvec, int shift) {
        for (int i = 0; i < mvec.size(); i++) {
            Vector line = (Vector) mvec.elementAt(i);
            for (int j = 0; j < line.size(); j++) {
                MappingObject mobj = (MappingObject) line.elementAt(j);
                if (mobj.type == BEGIN_TLATOKEN) {
                    BeginTLAToken obj = (BeginTLAToken) mobj;
                    obj.setColumn(obj.getColumn()+shift) ;
                } else if (mobj.type == END_TLATOKEN) {
                    EndTLAToken obj = (EndTLAToken) mobj;
                    obj.setColumn(obj.getColumn()+shift) ;
                } else if (mobj.type == SOURCE_TOKEN) {
                    SourceToken obj = (SourceToken) mobj;
                    obj.setBeginColumn(obj.getBeginColumn()+shift) ;
                    obj.setEndColumn(obj.getEndColumn()+shift) ;
                }
            }
        }
    }
    
    /**
     * For debugging.
     * @param mvec
     */
    public static void printMappingVector(Vector mvec) {
        for (int i = 0; i < mvec.size(); i++) {
            Vector line = (Vector) mvec.elementAt(i);
            System.out.print("line " + i + ":");
            for (int j = 0; j < line.size(); j++) {
                MappingObject mobj = (MappingObject) line.elementAt(j) ;
                System.out.print("  " + mobj.toString());
            }
            System.out.println("");
        }
    }
    
    public static void printMapping(MappingObject[][] mapping) {
        for (int i = 0; i < mapping.length; i++) {
            MappingObject[] line = mapping[i];
            System.out.print("line " + i + ":");
            for (int j = 0; j < line.length; j++) {
                MappingObject mobj = line[j] ;
                System.out.print("  " + mobj.toString());
            }
            System.out.println("");
        }
    }
}
