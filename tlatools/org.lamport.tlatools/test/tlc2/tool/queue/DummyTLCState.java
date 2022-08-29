package tlc2.tool.queue;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import util.UniqueString;

import java.util.HashSet;
import java.util.Set;

@SuppressWarnings("serial")
public class DummyTLCState extends TLCState {

    private final long fp;

    public DummyTLCState(OpDeclNode[] vars) {
        super(vars);
        uid = 0;
        this.fp = 0L;
    }

    public DummyTLCState(OpDeclNode[] vars, final long fp) {
        super(vars);
        uid = 0;
        this.fp = fp;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#bind(util.UniqueString, tlc2.value.Value, tla2sany.semantic.SemanticNode)
     */
    @Override
    public TLCState bind(final UniqueString name, final IValue value) {
        return null;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#bind(tla2sany.semantic.SymbolNode, tlc2.value.Value, tla2sany.semantic.SemanticNode)
     */
    @Override
    public TLCState bind(final SymbolNode id, final IValue value) {
        return null;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#unbind(util.UniqueString)
     */
    @Override
    public TLCState unbind(final UniqueString name) {
        return null;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#lookup(util.UniqueString)
     */
    @Override
    public IValue lookup(final UniqueString var) {
        return null;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#containsKey(util.UniqueString)
     */
    @Override
    public boolean containsKey(final UniqueString var) {
        return false;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#copy()
     */
    @Override
    public TLCState copy() {
        return null;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#deepCopy()
     */
    @Override
    public TLCState deepCopy() {
        return null;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#addToVec(tlc2.tool.StateVec)
     */
    @Override
    public StateVec addToVec(final StateVec states) {
        return null;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#deepNormalize()
     */
    @Override
    public void deepNormalize() {

    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#fingerPrint()
     */
    @Override
    public long fingerPrint() {
        return this.fp;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#allAssigned()
     */
    @Override
    public boolean allAssigned() {
        return false;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#getUnassigned()
     */
    @Override
    public final Set<OpDeclNode> getUnassigned() {
        return new HashSet<>();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#createEmpty()
     */
    @Override
    public TLCState createEmpty() {
        return this;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#toString()
     */
    public String toString() {
        return "Dummy#" + uid + ":" + fp;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.TLCState#toString(tlc2.tool.TLCState)
     */
    @Override
    public String toString(final TLCState lastState) {
        return null;
    }

    @Override
    public TLCState createNewFromValueStream(final IValueInputStream vis) {
        return this;
    }
}
