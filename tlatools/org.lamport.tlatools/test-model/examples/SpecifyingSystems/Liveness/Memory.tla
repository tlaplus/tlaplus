----------------------- MODULE Memory ------------------------
EXTENDS MemoryInterface
Inner(mem, ctl, buf) == INSTANCE InternalMemory 
Spec == \EE mem, ctl, buf : Inner(mem, ctl, buf)!ISpec 
==============================================================

