----------------------- MODULE RegisterInterface ---------------------------
CONSTANT Adr, Val, Proc, Reg
VARIABLE regFile
-----------------------------------------------------------------------------
RdRequest == [adr : Adr, val : Val, op : {"Rd"}]
WrRequest == [adr : Adr, val : Val, op : {"Wr"}]
FreeRegValue == [adr : Adr, val : Val, op : {"Free"}]
Request   == RdRequest \cup WrRequest
RegValue  == Request \cup FreeRegValue

RegFileTypeInvariant == regFile \in [Proc -> [Reg -> RegValue]]
=============================================================================
