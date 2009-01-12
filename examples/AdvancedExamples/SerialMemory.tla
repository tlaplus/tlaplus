-------------------------- MODULE SerialMemory --------------------------
EXTENDS RegisterInterface

Inner(InitMem, opQ, opOrder) == INSTANCE InnerSerial

Spec == \E InitMem \in [Adr -> Val] : 
           \EE opQ, opOrder : Inner(InitMem, opQ, opOrder)!Spec
=============================================================================