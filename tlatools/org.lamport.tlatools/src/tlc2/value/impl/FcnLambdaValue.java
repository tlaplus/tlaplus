// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Wed  4 Jul 2007 at 17:31:23 PST by lamport
//      modified on Thu Dec  6 21:46:34 PST 2001 by yuanyu

package tlc2.value.impl;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.TLCGlobals;
import tlc2.tool.*;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.*;
import util.Assert;
import util.UniqueString;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Objects;

public class FcnLambdaValue extends Value implements Applicable, IFcnLambdaValue {
    private static final long serialVersionUID = -1519055048140855139L;
    public final FcnParams params;       // the function formals
    public final SemanticNode body;      // the function body
    public final ITool tool;
    public final TLCState state;
    public final TLCState pstate;
    public ValueExcept[] excepts;  // the EXCEPTs
    public Context con;
    public int control;
    public FcnRcdValue fcnRcd;

    /*
     * Constructor: E.g. [ s \in {"A", "B", "C"} |-> "foo" ] where s \in {"A", "B",
     * "C"} is FcnLambdaValue and body is the expression "foo".
     */
    public FcnLambdaValue(final FcnParams params, final SemanticNode body, final ITool tool,
                          final Context c, final TLCState s0, final TLCState s1, final int control) {
        this.params = params;
        this.body = body;
        this.excepts = null;
        this.tool = tool;
        this.con = c;
        this.state = s0.copy();  // copy() added 12 Mar 2010 by Yuan Yu.
        if (s1 != null) {        // see SetPredValue constructor.
            this.pstate = s1.copy();
        } else {
            this.pstate = null;
        }

        this.control = control;
        this.fcnRcd = null;
    }

    public FcnLambdaValue(final FcnParams params, final SemanticNode body, final ITool tool,
                          final Context c, final TLCState s0, final TLCState s1, final int control, final CostModel cm) {
        this(params, body, tool, c, s0, s1, control);
        this.cm = cm;
    }

    public FcnLambdaValue(final FcnLambdaValue fcn, final ITool tool) {
        this.params = fcn.params;
        this.body = fcn.body;
        this.excepts = fcn.excepts;
        this.tool = tool;
        this.con = fcn.con;
        this.state = fcn.state;
        this.pstate = fcn.pstate;
        this.control = fcn.control;
        this.fcnRcd = fcn.fcnRcd;
    }

    public FcnLambdaValue(final FcnLambdaValue fcn) {
        this(fcn, fcn.tool);
    }

    @Override
    public final byte getKind() {
        return FCNLAMBDAVALUE;
    }

    public final void makeRecursive(final SymbolNode fname) {
        try {
            this.con = this.con.cons(fname, this);
            this.control = EvalControl.setKeepLazy(this.control);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            final FcnRcdValue fcn = (FcnRcdValue) this.toFcnRcd();
            return fcn.compareTo(obj);
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
            final FcnRcdValue fcn = (FcnRcdValue) this.toFcnRcd();
            return fcn.equals(obj);
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
            Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
                    "\nis an element of the function " + Values.ppr(this.toString()), getSource());
            return false;   // make compiler happy
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
            Assert.fail("Attempted to check if the function:\n" + Values.ppr(this.toString()) +
                    "\nis a finite set.", getSource());
            return false;   // make compiler happy
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /* Apply this function to the arguments given by args.  */
    @Override
    public final Value apply(final Value args, final int control) throws EvalException {
        try {

            if (this.fcnRcd != null) {
                return this.fcnRcd.apply(args, control);
            }

            // First, find all the excepts that match args.
            Value res = null;
            int num = 0;
            ValueExcept[] excepts1 = null;
            if (this.excepts != null) {
                final int exlen = this.excepts.length;
                for (int i = exlen - 1; i >= 0; i--) {
                    final ValueExcept ex = this.excepts[i];
                    final Value arg = ex.current();
                    boolean inExcept;
                    inExcept = arg.equals(args);
                    if (inExcept) {
                        if (ex.isLast()) {
                            res = ex.value;
                            break;
                        }
                        if (excepts1 == null) excepts1 = new ValueExcept[exlen];
                        excepts1[num++] = new ValueExcept(ex, ex.idx + 1);
                    }
                }
            }

            // Second, evaluate the function application.
            if (res == null) {
                Context c1 = this.con;
                final FormalParamNode[][] formals = this.params.formals;
                final Value[] domains = this.params.domains;
                final boolean[] isTuples = this.params.isTuples;
                final int plen = this.params.length();

                if (plen == 1) {
                    if (!domains[0].member(args)) {
                        Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                                ",\nthe first argument is:\n" + Values.ppr(args.toString()) +
                                "\nwhich is not in its domain.\n", getSource());
                    }
                    if (isTuples[0]) {
                        final FormalParamNode[] ids = formals[0];
                        final TupleValue argVal = (TupleValue) args.toTuple();
                        if (argVal == null) {
                            Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                                    ",\nthe first argument is:\n" + Values.ppr(args.toString()) +
                                    "\nwhich does not match its formal parameter.\n", getSource());
                        }
                        if (Objects.requireNonNull(argVal).size() != ids.length) return null;
                        final Value[] elems = argVal.elems;
                        for (int i = 0; i < ids.length; i++) {
                            c1 = c1.cons(ids[i], elems[i]);
                        }
                    } else {
                        c1 = c1.cons(formals[0][0], args);
                    }
                } else {
                    final TupleValue tv = (TupleValue) args.toTuple();
                    if (tv == null) {
                        Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                                ",\nthe argument list is:\n" + Values.ppr(args.toString()) +
                                "\nwhich does not match its formal parameter.\n", getSource());
                    }
                    final Value[] elems = Objects.requireNonNull(tv).elems;
                    int argn = 0;
                    for (int i = 0; i < formals.length; i++) {
                        final FormalParamNode[] ids = formals[i];
                        final Value domain = domains[i];
                        if (isTuples[i]) {
                            if (!domain.member(elems[argn])) {
                                Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                                        ",\nthe argument number " + (argn + 1) + " is:\n" +
                                        Values.ppr(elems[argn].toString()) +
                                        "\nwhich is not in its domain.\n", getSource());
                            }
                            final TupleValue tv1 = (TupleValue) elems[argn++].toTuple();
                            if (tv1 == null || tv1.size() != ids.length) {
                                Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                                        ",\nthe argument number " + argn + " is:\n" +
                                        Values.ppr(elems[argn - 1].toString()) +
                                        "\nwhich does not match its formal parameter.\n", getSource());
                            }
                            final Value[] avals = Objects.requireNonNull(tv1).elems;
                            for (int j = 0; j < ids.length; j++) {
                                c1 = c1.cons(ids[j], avals[j]);
                            }
                        } else {
                            for (final FormalParamNode id : ids) {
                                if (!domain.member(elems[argn])) {
                                    Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                                            ",\nthe argument number " + (argn + 1) + " is:\n" +
                                            Values.ppr(elems[argn].toString()) + "\nwhich is not in the function's domain " + this.getDomain().toString() + ".\n", getSource());
                                }
                                c1 = c1.cons(id, elems[argn++]);
                            }
                        }
                    }
                }
                res = (Value) this.tool.eval(this.body, c1, this.state, this.pstate, control);
            }

            // Finally, apply the matching excepts on the result.
            if (num == 0) return res;
            final ValueExcept[] excepts2 = new ValueExcept[num];
            for (int i = 0; i < num; i++) {
                excepts2[num - 1 - i] = excepts1[i];
            }
            return res.takeExcept(excepts2);

        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /* This one does not seem to be needed anymore.  */
    @Override
    public final Value apply(final Value[] args, final int control) throws EvalException {
        try {
            return this.apply(new TupleValue(args), control);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value select(final Value arg) {
        try {

            if (this.fcnRcd != null) {
                return this.fcnRcd.select(arg);
            }

            // First, find all the excepts that match arg.
            Value res = null;
            int num = 0;
            ValueExcept[] excepts1 = null;
            if (this.excepts != null) {
                final int exlen = this.excepts.length;
                for (int i = exlen - 1; i >= 0; i--) {
                    final ValueExcept ex = this.excepts[i];
                    final Value exArg = ex.current();
                    final boolean inExcept = exArg.equals(arg);
                    if (inExcept) {
                        if (ex.isLast()) {
                            res = ex.value;
                            break;
                        }
                        if (excepts1 == null) excepts1 = new ValueExcept[exlen];
                        excepts1[num++] = new ValueExcept(ex, ex.idx + 1);
                    }
                }
            }

            // Second, evaluate the function application.
            if (res == null) {
                Context c1 = this.con;
                final FormalParamNode[][] formals = this.params.formals;
                final Value[] domains = this.params.domains;
                final boolean[] isTuples = this.params.isTuples;
                final int plen = this.params.length();

                if (plen == 1) {
                    if (!domains[0].member(arg)) return null;
                    if (isTuples[0]) {
                        final FormalParamNode[] ids = formals[0];
                        final TupleValue argVal = (TupleValue) arg.toTuple();
                        /*
                         * SZA: Changed from argVal.toString() to arg.toString() to prevent a NullPointerException
                         */
                        if (argVal == null) {
                            Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                                    ",\nthe first argument is:\n" + Values.ppr(arg.toString()) +
                                    "\nwhich does not match its formal parameter.\n", getSource());
                        }
                        if (Objects.requireNonNull(argVal).size() != ids.length) return null;
                        final Value[] elems = argVal.elems;
                        for (int i = 0; i < ids.length; i++) {
                            c1 = c1.cons(ids[i], elems[i]);
                        }
                    } else {
                        c1 = c1.cons(formals[0][0], arg);
                    }
                } else {
                    final TupleValue tv = (TupleValue) arg.toTuple();
                    if (tv == null) {
                        Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                                ",\nthe argument list is:\n" + Values.ppr(arg.toString()) +
                                "\nwhich does not match its formal parameter.\n", getSource());
                    }
                    final Value[] elems = Objects.requireNonNull(tv).elems;
                    int argn = 0;
                    for (int i = 0; i < formals.length; i++) {
                        final FormalParamNode[] ids = formals[i];
                        final Value domain = domains[i];
                        if (isTuples[i]) {
                            if (!domain.member(elems[argn])) return null;
                            final TupleValue tv1 = (TupleValue) elems[argn++].toTuple();
                            if (tv1 == null) {
                                Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                                        ",\nthe argument number " + argn + " is:\n" +
                                        Values.ppr(elems[argn - 1].toString()) +
                                        "\nwhich does not match its formal parameter.\n", getSource());
                            }
                            if (Objects.requireNonNull(tv1).size() != ids.length) return null;
                            final Value[] avals = tv1.elems;
                            for (int j = 0; j < ids.length; j++) {
                                c1 = c1.cons(ids[j], avals[j]);
                            }
                        } else {
                            for (final FormalParamNode id : ids) {
                                if (!domain.member(elems[argn])) return null;
                                c1 = c1.cons(id, elems[argn++]);
                            }
                        }
                    }
                }
                res = (Value) this.tool.eval(this.body, c1, this.state, this.pstate, this.control);
            }

            // Finally, apply the matching excepts on the result.
            if (num == 0) return res;
            final ValueExcept[] excepts2 = new ValueExcept[num];
            for (int i = 0; i < num; i++) {
                excepts2[num - 1 - i] = excepts1[i];
            }
            return res.takeExcept(excepts2);

        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /* This method returns a new function value by taking except. */
    @Override
    public final Value takeExcept(final ValueExcept ex) {
        try {

            if (ex.idx >= ex.path.length) return ex.value;

            if (this.fcnRcd != null) {
                return this.fcnRcd.takeExcept(ex);
            }
            final FcnLambdaValue fcn = new FcnLambdaValue(this);
            if (this.excepts == null) {
                fcn.excepts = new ValueExcept[1];
                fcn.excepts[0] = ex;
            } else {
                final int exlen = this.excepts.length;
                fcn.excepts = new ValueExcept[exlen + 1];
                System.arraycopy(this.excepts, 0, fcn.excepts, 0, exlen);
                fcn.excepts[exlen] = ex;
            }
            return fcn;

        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /* This method returns a new function value by taking excepts. */
    @Override
    public final Value takeExcept(final ValueExcept[] exs) {
        try {

            if (this.fcnRcd != null) {
                return this.fcnRcd.takeExcept(exs);
            }
            final FcnLambdaValue fcn = new FcnLambdaValue(this);
            final int exslen = exs.length;
            if (exslen != 0) {
                int i;
                for (i = exs.length - 1; i >= 0; i--) {
                    if (exs[i].idx >= exs[i].path.length) break;
                }
                if (i >= 0) {
                    final int xlen = exslen - i - 1;
                    fcn.excepts = new ValueExcept[xlen];
                    System.arraycopy(exs, i + 1, fcn.excepts, 0, xlen);
                } else if (this.excepts == null) {
                    fcn.excepts = new ValueExcept[exslen];
                    System.arraycopy(exs, 0, fcn.excepts, 0, exslen);
                } else {
                    final int len = this.excepts.length;
                    fcn.excepts = new ValueExcept[len + exslen];
                    System.arraycopy(this.excepts, 0, fcn.excepts, 0, len);
                    System.arraycopy(exs, 0, fcn.excepts, len, exslen);
                }
            }
            return fcn;

        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value getDomain() {
        try {

            if (this.fcnRcd != null) {
                return this.fcnRcd.getDomain();
            }
            final int len = this.params.length();
            if (len == 1) {
                return this.params.domains[0];
            }
            final Value[] sets = new Value[len];
            final int dlen = this.params.domains.length;
            final boolean[] isTuples = this.params.isTuples;
            int idx = 0;
            for (int i = 0; i < dlen; i++) {
                final FormalParamNode[] formal = this.params.formals[i];
                final Value domain = this.params.domains[i];
                if (isTuples[i]) {
                    sets[idx++] = domain;
                } else {
                    for (int j = 0; j < formal.length; j++) {
                        sets[idx++] = domain;
                    }
                }
            }
            return new SetOfTuplesValue(sets);

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
            if (this.fcnRcd == null) {
                return this.params.size();
            }
            return this.fcnRcd.size();
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
            final FcnLambdaValue fcn = new FcnLambdaValue(this);
            // A bug occured when printing a function whose domain is a Cartesian product because this.fcnRcd
            // is null at this point.  On 5 Mar 2012, LL wrapped the following null test around the assignment.
            if (this.fcnRcd != null) {
                fcn.fcnRcd = (FcnRcdValue) this.fcnRcd.deepCopy();
            }
            return fcn;
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
            return (val instanceof FcnLambdaValue);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    private void readObject(final ObjectInputStream ois) throws IOException, ClassNotFoundException {
        this.fcnRcd = (FcnRcdValue) ois.readObject();
    }

    private void writeObject(final ObjectOutputStream oos) throws IOException {
        final FcnRcdValue res = (FcnRcdValue) this.toFcnRcd();
        oos.writeObject(res);
    }

    @Override
    public final boolean isNormalized() {
        try {
            if (this.fcnRcd == null) {
                return false;
            }
            return this.fcnRcd.isNormalized();
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
            if (this.fcnRcd != null) {
                this.fcnRcd.normalize();
            }
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
    public final void deepNormalize() {
        try {
            if (fcnRcd == null) {
                if (excepts != null) {
                    for (final ValueExcept except : excepts) {
                        except.value.deepNormalize();
                        for (int j = 0; j < except.path.length; j++) {
                            except.path[j].deepNormalize();
                        }
                    }
                }
                final IValue[] paramDoms = params.domains;
                for (final IValue paramDom : paramDoms) {
                    paramDom.deepNormalize();
                }
            } else {
                fcnRcd.deepNormalize();
            }
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value toTuple() {
        if (this.params.length() != 1) return null;
        final Value dom = this.params.domains[0];
        final SymbolNode var = this.params.formals[0][0];
        if (dom instanceof final IntervalValue intv) {
            if (intv.low != 1) return null;
            final Value[] elems = new Value[intv.high];
            for (int i = 1; i <= intv.high; i++) {
                final Context c1 = this.con.cons(var, IntValue.gen(i));
                elems[i - 1] = (Value) this.tool.eval(this.body, c1, this.state, this.pstate, this.control);
            }
            if (coverage) {
                cm.incSecondary(elems.length);
            }
            return new TupleValue(elems, cm);
        } else {
            final SetEnumValue eSet = (SetEnumValue) dom.toSetEnum();
            if (eSet == null)
                Assert.fail("To convert a function of form [x \\in S |-> f(x)] " +
                        "to a tuple, the set S must be enumerable.", getSource());
            Objects.requireNonNull(eSet).normalize();
            final int len = eSet.size();
            final Value[] elems = new Value[len];
            for (int i = 0; i < len; i++) {
                final Value argVal = eSet.elems.get(i);
                if (!(argVal instanceof IntValue)) return null;
                if (((IntValue) argVal).val != i + 1) return null;
                final Context c1 = this.con.cons(var, argVal);
                elems[i] = (Value) this.tool.eval(this.body, c1, this.state, this.pstate, this.control);
            }
            cm.incSecondary(elems.length);
            return new TupleValue(elems, cm);
        }
    }

    @Override
    public final Value toRcd() {
        final FcnRcdValue fcn = (FcnRcdValue) this.toFcnRcd();
        if (fcn == null || fcn.domain == null) {
            return null;
        }
        fcn.normalize();
        final UniqueString[] vars = new UniqueString[fcn.domain.length];
        for (int i = 0; i < fcn.domain.length; i++) {
            if (fcn.domain[i] instanceof StringValue sv) {
                vars[i] = sv.getVal();
            } else {
                return null;
            }

        }
        if (coverage) {
            cm.incSecondary(vars.length);
        }
        return new RecordValue(vars, fcn.values, fcn.isNormalized(), cm);
    }

    @Override
    public final Value toFcnRcd() {
        try {

            if (this.fcnRcd == null) {
                final int sz = this.params.size();
                final FormalParamNode[][] formals = this.params.formals;
                final boolean[] isTuples = this.params.isTuples;

                final Value[] domain = new Value[sz];
                final Value[] values = new Value[sz];
                int idx = 0;
                final ValueEnumeration Enum = this.params.elements();
                Value arg;
                if (this.params.length() == 1) {
                    while ((arg = Enum.nextElement()) != null) {
                        domain[idx] = arg;
                        Context c1 = this.con;
                        if (isTuples[0]) {
                            final FormalParamNode[] ids = formals[0];
                            final Value[] avals = ((TupleValue) arg).elems;
                            for (int j = 0; j < ids.length; j++) {
                                c1 = c1.cons(ids[j], avals[j]);
                            }
                        } else {
                            c1 = c1.cons(formals[0][0], arg);
                        }
                        values[idx++] = (Value) this.tool.eval(this.body, c1, this.state, this.pstate, this.control);
                    }
                    if (this.params.domains[0] instanceof final IntervalValue iv) {
                        this.fcnRcd = new FcnRcdValue(iv, values, cm);
                    } else {
                        this.fcnRcd = new FcnRcdValue(domain, values, false, cm);
                    }
                } else {
                    while ((arg = Enum.nextElement()) != null) {
                        domain[idx] = arg;
                        final Value[] argList = ((TupleValue) arg).elems;
                        int argn = 0;
                        Context c1 = this.con;
                        for (int i = 0; i < formals.length; i++) {
                            final FormalParamNode[] ids = formals[i];
                            if (isTuples[i]) {
                                final Value[] avals = ((TupleValue) argList[argn++]).elems;
                                for (int j = 0; j < ids.length; j++) {
                                    c1 = c1.cons(ids[j], avals[j]);
                                }
                            } else {
                                for (final FormalParamNode id : ids) {
                                    c1 = c1.cons(id, argList[argn++]);
                                }
                            }
                        }
                        values[idx++] = (Value) this.tool.eval(this.body, c1, this.state, this.pstate, this.control);
                    }
                    this.fcnRcd = new FcnRcdValue(domain, values, false, cm);
                }
                if (coverage) {
                    cm.incSecondary(sz);
                }
                if (this.excepts != null) {
                    // TODO:
                    // tlc2.tool.simulation.NQSpecTest is the only test in our test suite that
                    // exercises this code path--it works fine. In the general case, however,
                    // it is not clear why the cast to FRV should be safe. As a matter of fact,
                    // this threw a ClassCastException when working on the TLA+ debugger, where
                    // toFcnRcd is called from toString below. Given that the API contract of
                    // Value#toFcnRcd allows null, the cast could be secured with a conditional
                    // and null returned otherwise. In case of null, toString returns the symbolic
                    // value.
                    this.fcnRcd = (FcnRcdValue) fcnRcd.takeExcept(this.excepts);
                }
            }
            return this.fcnRcd;

        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final void write(final IValueOutputStream vos) throws IOException {
        fcnRcd.write(vos);
    }

    /* The fingerprint methods.  */
    @Override
    public final long fingerPrint(final long fp) {
        try {
            final Value fcn = this.toFcnRcd();
            return fcn.fingerPrint(fp);
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
            final Value fcn = this.toFcnRcd();
            return fcn.permute(perm);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /* The string representation of this function.  */
    public final StringBuilder toString(final StringBuilder sb, final int offset) {
        return toString(sb, offset, true);
    }

    /* The string representation of this function.  */
    @Override
    public final StringBuilder toString(final StringBuilder sb, final int offset, final boolean swallow) {
        try {
            if (TLCGlobals.expand || this.params == null) {
                try {
                    final Value val = this.toFcnRcd();
                    return val.toString(sb, offset, true);
                } catch (final Throwable e) { /*SKIP*/ }
            }
            sb.append("[").append(Objects.requireNonNull(this.params));
            sb.append(" |-> <expression ").append(this.body).append(">]");
            return sb;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final SemanticNode getBody() {
        return body;
    }

    @Override
    public final FcnRcdValue getRcd() {
        return fcnRcd;
    }

    @Override
    public FcnParams getParams() {
        return params;
    }

    @Override
    public Context getCon() {
        return con;
    }

    @Override
    public boolean hasRcd() {
        return fcnRcd != null;
    }
}
