---- MODULE ClientActionSerializerModule ----
(*`^\addcontentsline{toc}{section}{ClientActionSerializerModule}^'*)

EXTENDS HostBaseModule
(*Defn*)ClosedActionSerialNumber==Nat \union{Infinity}

(*Defn*)OpenActionSerialNumber==Nat \ {0}

VARIABLE ActionSerialNumber

(*Defn*)ActionSerialNumberType==OpenActionSerialNumber

(*Defn*)ActionSerialNumberInit==1

(*Defn*)AdvanceActionSerialNumber==(ActionSerialNumber')=ActionSerialNumber+1
====
