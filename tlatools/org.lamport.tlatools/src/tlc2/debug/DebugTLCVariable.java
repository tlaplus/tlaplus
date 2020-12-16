package tlc2.debug;

import java.util.List;
import java.util.Random;

import org.eclipse.lsp4j.debug.Variable;

import tlc2.value.impl.Enumerable;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.TLCVariable;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;

public class DebugTLCVariable extends Variable implements tlc2.value.impl.TLCVariable {
	
	private transient Value value;
	
	public DebugTLCVariable(String lhs) {
		this.setName(lhs);
	}
	
	public DebugTLCVariable(Value value) {
		this.setName(value.toString());
	}

	public DebugTLCVariable[] getNested(Random rnd) {
		final List<TLCVariable> tlcVariables = this.value.getTLCVariables(this, rnd);
		return tlcVariables.toArray(new DebugTLCVariable[tlcVariables.size()]);
	}

	public void setInstance(Value v) {
		this.value = v;
	}

	@Override
	public TLCVariable newInstance(final String name, Value v, Random rnd) {
		DebugTLCVariable variable = new DebugTLCVariable(name);
		variable.setInstance(v);
		if (v instanceof Enumerable || v instanceof FcnRcdValue || v instanceof RecordValue || v instanceof TupleValue) {
			variable.setVariablesReference(rnd.nextInt(Integer.MAX_VALUE-1)+ 1);
		}
		return v.toTLCVariable(variable, rnd);
	}

	@Override
	public TLCVariable newInstance(Value value, Random rnd) {
		return newInstance(value.toString(), value, rnd);
	}
}