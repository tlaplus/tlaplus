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

import java.util.ArrayList;
import java.util.List;

import tla2sany.semantic.SemanticNode;
import tlc2.value.IValue;

public class FingerprintException extends RuntimeException {

  final public IValue value;
  final public FingerprintException next;

  private FingerprintException(Throwable initCauseThrowable, IValue value, FingerprintException next) {
    initCause(initCauseThrowable);
    this.value = value;
    this.next = next;
  }

  public static FingerprintException getNewHead(IValue v, Throwable t){
    FingerprintException fpe = null;
    if(t instanceof FingerprintException)
      fpe = ((FingerprintException) t).prependNewHead(v);
    else
      fpe = FingerprintException.createNewHead(v, t);
    return fpe;
  }

  private static FingerprintException createNewHead(IValue value, Throwable initCauseThrowable){
    if(value == null || initCauseThrowable == null)
      return null;
    else
      return new FingerprintException(initCauseThrowable, value, null);
  }

  private FingerprintException prependNewHead(IValue value){
    if(value == null)
      return null;
    else
      return new FingerprintException(null, value, this);
  }

  public Throwable getRootCause(){
    FingerprintException nextFPE = this;
    while(nextFPE.next != null)
      nextFPE = nextFPE.next;
    return nextFPE.getCause();
  }

  public String getTrace(){
    return getTraceImpl(0, null);
  }

  private String getTraceImpl(final int traceIndexLabel, final Integer lastSemanticNodeUid){
    SemanticNode semanticNode = value.getSource();
    if(semanticNode == null){
      if(next == null)
        return "";
      else
        return next.getTraceImpl(traceIndexLabel, lastSemanticNodeUid);
    }
    else{
      Integer semanticNodeUid = semanticNode.getUid();
      if(semanticNodeUid.equals(lastSemanticNodeUid)){ // same SemanticNode compared to current top of stack
        if(next == null)
          return "";
        else
          return next.getTraceImpl(traceIndexLabel, lastSemanticNodeUid);
      }
      else{ // different SemanticNode compared to current top of stack
        String description = traceIndexLabel + ") " + semanticNode.toString() + "\n";
        if(next == null)
          return description;
        else
          return next.getTraceImpl(traceIndexLabel+1, semanticNodeUid) + description;
      }
    }
  }

  public final List<SemanticNode> asTrace() {
	  final List<SemanticNode> stack = new ArrayList<>();
	  
	  if (value != null) {
		  stack.add(this.value.getSource());
	  }

	  while (next != null && next.value != null) {
		stack.add(next.value.getSource());
	  }
	  
	  return stack;
  }
}
