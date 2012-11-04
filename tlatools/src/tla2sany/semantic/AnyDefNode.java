/**
 * The AnyDefNode interface is implemented by OpDefNode and ThmOrAssumpDefNode.
 * It was added by LL on 24 Oct 2012 to fix a bug in the level-checking of
 * ThmOrAssumpDefNode objects.  When a module containing a theorem or assumption 
 * such as 
 * 
 *    THEOREM Fab == ...
 *    
 * is instantiated with parameters in a statement like
 * 
 *     I(x, y) == INSTANCE M WITH ...
 *     
 * then level checking of the expression I(e1, e2)!Fab did not check that
 * the levels of e1 and e2 were appropriate for the instantiation.  This was
 * because the levelCheck method of OpApplNode treated an operator like Fab
 * defined with a ThmOrAssumpDefNode differently from one defined with an 
 * OpDefNode.  To solve this problem, level checking of ThmOrAssumpDefNode was 
 * changed to be essentially the same as for OpDefNode.  The levelCheck method
 * of OpApplNode was changed to handle ThmOrAssumpDefNode and OpDefNode operators
 * the same by changing OpDefNode to AnyDefNode in a couple of places, and by 
 * replacing one access to an OpDefNode field by a call of a new method that
 * returns the value of that field.    
 */
package tla2sany.semantic;

import java.util.HashSet;

import util.UniqueString;

/**
 * @author lamport
 *
 */
public interface AnyDefNode {
    public boolean levelCheck(int itr) ;
    public int getMaxLevel(int i) ;
    public UniqueString getName() ;
    public int getMinMaxLevel(int i, int j) ;
    public boolean getOpLevelCond(int i, int j, int k) ;
    public int getLevel() ;
    public int getWeight(int i) ;
    public HashSet getLevelParams() ;
    public HashSet getAllParams() ;
    public HashSet getNonLeibnizParams() ;
    public int getArity() ;
    public boolean[] getIsLeibnizArg() ;
    public boolean getIsLeibniz() ;
    public SetOfLevelConstraints getLevelConstraints() ;
    public HashSet getArgLevelParams() ;
    public SetOfArgLevelConstraints getArgLevelConstraints() ;
    public FormalParamNode[] getParams() ;
}
