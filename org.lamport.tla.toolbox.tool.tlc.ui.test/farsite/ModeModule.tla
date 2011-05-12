---- MODULE ModeModule ----
(*`^\addcontentsline{toc}{section}{ModeModule}^'*)

EXTENDS Stubs
(* 
	Windows has fairly involved mode semantics for opening files.  There are
	three types of permissions: read, write, and delete.  When a thread opens
	or creates a fileID, it indicates which permissions it requires that it be
	granted, and it indicates which permissions it requires that others not
	be granted.
 *)

(*Defn*)ATReadable=="ATReadable"
(*Defn*)ATWritable=="ATWritable"
(*Defn*)Access=={ATReadable,ATWritable}

(*Defn*)AccessSet==SUBSET Access

(*Defn*)MTAccessRead=="MTAccessRead"
(*Defn*)MTAccessWrite=="MTAccessWrite"
(*Defn*)MTAccessDelete=="MTAccessDelete"
(*Defn*)MTExcludeRead=="MTExcludeRead"
(*Defn*)MTExcludeWrite=="MTExcludeWrite"
(*Defn*)MTExcludeDelete=="MTExcludeDelete"
(*Defn*)Mode==
  {
  MTAccessRead,
  MTAccessWrite,
  MTAccessDelete,
  MTExcludeRead,
  MTExcludeWrite,
  MTExcludeDelete
  }

(*Defn*)ModeSet==SUBSET Mode

(*Defn*)ModeSetToAccessSet(modes)==
  UNION
  {
  IF MTAccessRead \in modes THEN{ATReadable}ELSE{},
  IF MTAccessWrite \in modes THEN{ATWritable}ELSE{}
  }

(*Defn*)ModeOpposite(mode)==
  IF mode=MTAccessRead
  THEN
    MTExcludeRead
  ELSE IF mode=MTAccessWrite
  THEN
    MTExcludeWrite
  ELSE IF mode=MTAccessDelete
  THEN
    MTExcludeDelete
  ELSE IF mode=MTExcludeRead
  THEN
    MTAccessRead
  ELSE IF mode=MTExcludeWrite
  THEN
    MTAccessWrite
  ELSE
    MTAccessDelete

(*Defn*)ModeSetsCompatible(modes1,modes2)==
  \A mode \in modes1:ModeOpposite(mode)\notin modes2

(*Defn*)ModeIsWeak(mode)==mode \in{MTAccessRead,MTAccessWrite}

====
