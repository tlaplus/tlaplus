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

  public String getTrace(){
    return getTraceImpl(0, null);
  }

  private String getTraceImpl(final Integer traceIndexLabel, final Integer lastSemanticNodeUid){
    SemanticNode semanticNode = value.getSourceSemanticNode();
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

}
