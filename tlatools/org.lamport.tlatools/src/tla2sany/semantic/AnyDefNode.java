/**
 * The AnyDefNode interface is implemented by OpDefNode and ThmOrAssumpDefNode.
 * It was added by LL on 24 Oct 2012 to fix a bug in the level-checking of
 * ThmOrAssumpDefNode objects.  When a module containing a theorem or assumption
 * such as
 * <p>
 * THEOREM Fab == ...
 * <p>
 * is instantiated with parameters in a statement like
 * <p>
 * I(x, y) == INSTANCE M WITH ...
 * <p>
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

import util.UniqueString;

import java.util.HashSet;

/**
 * @author lamport
 *
 */
public interface AnyDefNode {
    boolean levelCheck(int itr);

    int getMaxLevel(int i);

    UniqueString getName();

    int getMinMaxLevel(int i, int j);

    boolean getOpLevelCond(int i, int j, int k);

    int getLevel();

    int getWeight(int i);

    HashSet<SymbolNode> getLevelParams();

    HashSet<SymbolNode> getAllParams();

    HashSet<SymbolNode> getNonLeibnizParams();

    int getArity();

    boolean[] getIsLeibnizArg();

    boolean getIsLeibniz();

    SetOfLevelConstraints getLevelConstraints();

    HashSet<ArgLevelParam> getArgLevelParams();

    SetOfArgLevelConstraints getArgLevelConstraints();

    FormalParamNode[] getParams();

    AnyDefNode getSource();
}
