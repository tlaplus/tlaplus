// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 15:30:08 PST by lamport
//      modified on Thu Feb  8 21:23:55 PST 2001 by yuanyu

package tlc2.value.impl;

import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.FingerprintException;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import util.Assert;
import util.ToolIO;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

public class LazyValue extends Value {
    private static final long serialVersionUID = -6829055787675377238L;
    /**
     * Allow to completely disable LazyValue by passing a VM property/system
     * property to the Java VM with "-Dtlc2.value.LazyValue.off=true". This is meant
     * for debug purposes only and can be removed at any time. This is not API.
     * <p>
     * This property was added 01/12/2018 by Markus Kuppe in the process of fixing a
     * bug where TLC generates and incorrect set of states with certain statements.
     * More details can be found at <a href="https://github.com/tlaplus/tlaplus/issues/113">...</a>.
     */
    private static final boolean LAZYEVAL_OFF = Boolean.getBoolean(tlc2.value.impl.LazyValue.class.getName() + ".off");

    static {
        // Indicate if LazyValue will be disabled in this TLC run.
        if (LAZYEVAL_OFF) {
            ToolIO.out.println("LazyValue is disabled.");
        }
    }

    /**
     * The field val is the result of evaluating expr in context con and
     * a pair of states.  If val is null, then the value has not been
     * computed, but when computed, the value can be cached in the field
     * val. If val is ValUndef, then the value has not been computed,
     * and when computed, it can not be cached in the field val.
     */

    public SemanticNode expr;
    public Context con;
    private Value val;

    public LazyValue(final SemanticNode expr, final Context con, final CostModel cm) {
        this(expr, con, true, coverage ? cm.get(expr) : cm);
    }

    public LazyValue(final SemanticNode expr, final Context con, final boolean cachable, final CostModel cm) {
        this.expr = expr;
        this.con = con;
        this.cm = coverage ? cm.get(expr) : cm;
        this.val = null;
        // See comment on cachable's meager performance in Tool.java on line 1408.
        // See other note about a bug that surfaced with LazyValue in Tool.java on line ~1385.
        if (LAZYEVAL_OFF || !cachable) {
            this.val = UndefValue.ValUndef;
        }
    }

    public final boolean isUncachable() {
        return this.val == UndefValue.ValUndef;
    }

    public final Value getValue() {
        // cache hit on (this.val != null && !isUncachable)
        // cache miss on (this.val == null)
        return this.val;
    }

    public final void setValue(final Value aValue) {
        assert !isUncachable();
        this.val = aValue;
    }

    @Override
    public final byte getKind() {
        return LAZYVALUE;
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to compare lazy values.", getSource());
            }
            return this.val.compareTo(obj);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    public final boolean equals(final Object obj) {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to check equality of lazy values.", getSource());
            }
            return this.val.equals(obj);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final boolean member(final Value elem) {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to check set membership of lazy values.", getSource());
            }
            return this.val.member(elem);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final boolean isFinite() {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to check if a lazy value is a finite set.", getSource());
            }
            return this.val.isFinite();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value takeExcept(final ValueExcept ex) {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to apply EXCEPT construct to lazy value.", getSource());
            }
            return this.val.takeExcept(ex);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value takeExcept(final ValueExcept[] exs) {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to apply EXCEPT construct to lazy value.", getSource());
            }
            return this.val.takeExcept(exs);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final int size() {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to compute size of lazy value.", getSource());
            }
            return this.val.size();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    private void readObject(final ObjectInputStream ois) throws IOException, ClassNotFoundException {
        this.val = (Value) ois.readObject();
    }

    private void writeObject(final ObjectOutputStream oos) throws IOException {
        if (this.val == null || this.val == UndefValue.ValUndef) {
            Assert.fail("Error(TLC): Attempted to serialize lazy value.", getSource());
        }
        oos.writeObject(this.val);
    }

    /* Nothing to normalize. */
    @Override
    public final boolean isNormalized() {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to normalize lazy value.", getSource());
            }
            return this.val.isNormalized();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value normalize() {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to normalize lazy value.", getSource());
            }
            this.val.normalize();
            return this;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final boolean isDefined() {
        return true;
    }

    @Override
    public final IValue deepCopy() {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) return this;
            return this.val.deepCopy();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final boolean assignable(final Value val) {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to call assignable on lazy value.", getSource());
            }
            return this.val.assignable(val);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /* The fingerprint method */
    @Override
    public final long fingerPrint(final long fp) {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to fingerprint a lazy value.", getSource());
            }
            return this.val.fingerPrint(fp);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final IValue permute(final IMVPerm perm) {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                Assert.fail("Error(TLC): Attempted to apply permutation to lazy value.", getSource());
            }
            return this.val.permute(perm);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /* The string representation of the value. */
    @Override
    public final StringBuilder toString(final StringBuilder sb, final int offset, final boolean swallow) {
        try {
            if (this.val == null || this.val == UndefValue.ValUndef) {
                return sb.append("<LAZY ").append(this.expr).append(">");
            }
            return this.val.toString(sb, offset, swallow);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    public IValue eval(final Tool tool) {
        return eval(tool, tool.EmptyState);
    }

    public IValue eval(final Tool tool, final TLCState s0) {
        return eval(tool, s0, null);
    }

    public IValue eval(final Tool tool, final TLCState s0, final TLCState s1) {
        final Value eval = tool.eval(expr, con, s0, s1, EvalControl.Clear, cm);
        if (!eval.hasSource()) {
            // See comment at tlc2.debug.TLCStackFrame.getVariable(IValue, SymbolNode)
            eval.setSource(this.expr);
        }
        return eval;
    }
}
