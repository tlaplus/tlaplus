package tlc2.tool.queue;

import java.util.HashSet;
import java.util.Set;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.value.IValue;
import util.UniqueString;

@SuppressWarnings("serial")
public class DummyTLCState extends TLCState {

	private final long fp;

	public DummyTLCState() {
		uid = 0;
		TLCState.Empty = this;
		this.fp = 0L;
	}
	
	public DummyTLCState(long fp) {
		this.fp = fp;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#bind(util.UniqueString, tlc2.value.Value, tla2sany.semantic.SemanticNode)
	 */
	public TLCState bind(UniqueString name, IValue value) {
		return null;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#bind(tla2sany.semantic.SymbolNode, tlc2.value.Value, tla2sany.semantic.SemanticNode)
	 */
	public TLCState bind(SymbolNode id, IValue value) {
		return null;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#unbind(util.UniqueString)
	 */
	public TLCState unbind(UniqueString name) {
		return null;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#lookup(util.UniqueString)
	 */
	public IValue lookup(UniqueString var) {
		return null;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#containsKey(util.UniqueString)
	 */
	public boolean containsKey(UniqueString var) {
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#copy()
	 */
	public TLCState copy() {
		return null;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#deepCopy()
	 */
	public TLCState deepCopy() {
		return null;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#addToVec(tlc2.tool.StateVec)
	 */
	public StateVec addToVec(StateVec states) {
		return null;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#deepNormalize()
	 */
	public void deepNormalize() {
		
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#fingerPrint()
	 */
	public long fingerPrint() {
		return this.fp;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#allAssigned()
	 */
	public boolean allAssigned() {
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#getUnassigned()
	 */
	public final Set<OpDeclNode> getUnassigned() {
		return new HashSet<OpDeclNode>();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.TLCState#createEmpty()
	 */
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
	public String toString(TLCState lastState) {
		return null;
	}
}
