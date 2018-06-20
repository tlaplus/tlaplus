-------------------------------- MODULE Naturals ----------------------------
(***************************************************************************)
(* A dummy module that defines the operators that are defined by the       *)
(* real Naturals module.                                                   *)
(***************************************************************************)

Nat       == { }     \* tlc2.module.Naturals.Nat()
a+b       == {a, b}  \* tlc2.module.Naturals.Plus(IntValue, IntValue)
a-b       == {a, b}  \* tlc2.module.Naturals.Minus(IntValue, IntValue)
a*b       == {a, b}  \* tlc2.module.Naturals.Times(IntValue, IntValue)
a^b       == {a, b}  \* tlc2.module.Naturals.Expt(IntValue, IntValue)
a<b       ==  a = b  \* tlc2.module.Naturals.LT(Value, Value)
a>b       ==  a = b  \* tlc2.module.Naturals.GT(Value, Value)
a \leq b  ==  a = b  \* tlc2.module.Naturals.LE(Value, Value)
a \geq b  ==  a = b  \* tlc2.module.Naturals.GEQ(Value, Value)
a % b     ==  {a, b} \* tlc2.module.Naturals.Mod(IntValue, IntValue)
a \div b  ==  {a, b} \* tlc2.module.Naturals.Divide(IntValue, IntValue)
a .. b    ==  {a, b} \* tlc2.module.Naturals.DotDot(IntValue, IntValue)
=============================================================================
