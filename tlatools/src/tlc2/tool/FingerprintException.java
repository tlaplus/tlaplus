// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool;

import tlc2.value.Value;
import tla2sany.semantic.SemanticNode;

public class FingerprintException extends RuntimeException {

  final public Value value;
  final public FingerprintException next;

  private FingerprintException(Throwable initCauseThrowable, Value value, FingerprintException next) {
    initCause(initCauseThrowable);
    this.value = value;
    this.next = next;
  }

  public static FingerprintException getNewHead(Value v, Throwable t){
    FingerprintException fpe = null;
    if(!(t instanceof FingerprintException))
      fpe = FingerprintException.createNewHead(v, t);
    else
      fpe = ((FingerprintException) t).prependNewHead(v);
    return fpe;
  }

  private static FingerprintException createNewHead(Value value, Throwable initCauseThrowable){
    if(value == null || initCauseThrowable == null)
      return null;
    else
      return new FingerprintException(initCauseThrowable, value, null);
  }

  private FingerprintException prependNewHead(Value value){
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

   public int getTraceLength(){
    int count = 1;
    FingerprintException nextFPE = this;
    while(nextFPE.next != null){
      nextFPE = nextFPE.next;
      count++;
    }
    return count;
  }

  public String getTrace(final int traceIndexLabel){
    SemanticNode semanticNode = value.getSourceSemanticNode();
    if(semanticNode == null){
      if(next == null)
        return "";
      else
        return next.getTrace(traceIndexLabel);
    }
    else{
      String description = traceIndexLabel + ") " + value.getSourceSemanticNode().toString() + "\n";
      if(next == null)
        return description;
      else
        return next.getTrace(traceIndexLabel+1) + description;
    }
  }

}
