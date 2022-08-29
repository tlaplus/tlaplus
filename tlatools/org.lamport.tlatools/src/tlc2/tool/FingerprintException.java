/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved.
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Ian Morris Nieves - initial design and implementation
 ******************************************************************************/

package tlc2.tool;

import tla2sany.semantic.SemanticNode;
import tlc2.value.IValue;

import java.util.ArrayList;
import java.util.List;

public class FingerprintException extends RuntimeException {

    private static final long serialVersionUID = -3982482838722472641L;
    public final IValue value;
    public final FingerprintException next;

    private FingerprintException(final Throwable initCauseThrowable, final IValue value, final FingerprintException next) {
        initCause(initCauseThrowable);
        this.value = value;
        this.next = next;
    }

    public static FingerprintException getNewHead(final IValue v, final Throwable t) {
        FingerprintException fpe;
        if (t instanceof FingerprintException e)
            fpe = e.prependNewHead(v);
        else
            fpe = FingerprintException.createNewHead(v, t);
        return fpe;
    }

    private static FingerprintException createNewHead(final IValue value, final Throwable initCauseThrowable) {
        if (value == null || initCauseThrowable == null)
            return null;
        else
            return new FingerprintException(initCauseThrowable, value, null);
    }

    private FingerprintException prependNewHead(final IValue value) {
        if (value == null)
            return null;
        else
            return new FingerprintException(null, value, this);
    }

    public Throwable getRootCause() {
        FingerprintException nextFPE = this;
        while (nextFPE.next != null)
            nextFPE = nextFPE.next;
        return nextFPE.getCause();
    }

    public String getTrace() {
        return getTraceImpl(0, null);
    }

    private String getTraceImpl(final int traceIndexLabel, final Integer lastSemanticNodeUid) {
        final SemanticNode semanticNode = value.getSource();
        if (semanticNode == null) {
            if (next == null)
                return "";
            else
                return next.getTraceImpl(traceIndexLabel, lastSemanticNodeUid);
        } else {
            final Integer semanticNodeUid = semanticNode.getUid();
            if (semanticNodeUid.equals(lastSemanticNodeUid)) { // same SemanticNode compared to current top of stack
                if (next == null)
                    return "";
                else
                    return next.getTraceImpl(traceIndexLabel, lastSemanticNodeUid);
            } else { // different SemanticNode compared to current top of stack
                final String description = traceIndexLabel + ") " + semanticNode + "\n";
                if (next == null)
                    return description;
                else
                    return next.getTraceImpl(traceIndexLabel + 1, semanticNodeUid) + description;
            }
        }
    }

    public final List<SemanticNode> asTrace() {
        final List<SemanticNode> stack = new ArrayList<>();

        if (value != null) {
            stack.add(this.value.getSource());
        }

        var curr = next;

        while (curr != null && curr.value != null) {
            stack.add(curr.value.getSource());
            curr = curr.next;
        }

        return stack;
    }
}
