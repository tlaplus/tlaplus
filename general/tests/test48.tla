--------------- MODULE test48 -------------

(* test definability of all user-definable infix, prefix, and postfix  
   operators *)

EXTENDS TLC

VARIABLE x


z - y == z
z + y == z
z * y == z
z / y == z
z ^ y == z
z < y == z
z > y == z
z .. y == z
z ... y == z
z | y == z
z || y == z
z & y == z
z && y == z
z $ y == z
z $$ y == z
z ?? y == z
z %% y == z
z ## y == z
z ++ y == z
z -- y == z
z ** y == z
z // y == z
z ^^ y == z
\* z @@ y == z  \* THIS IS DEFINED IN THE TLC MODULE
z !! y == z
z |- y == z
z |= y == z
z -| y == z
z =| y == z
z <: y == z  
\* z :> y == z  \* THIS IS DEFINED IN THE TLC MODULE
z := y == z
z ::= y == z
z \uplus y == z
z \sqcap y == z
z \sqcup y == z
z \div y == z
z \wr y == z
z \star y == z
z \bigcirc y == z
z \bullet y == z
z \prec y == z
z \succ y == z
z \preceq y == z
z \succeq y == z
z \sim y == z
z \simeq y == z
z \ll y == z
z \gg y == z
z \asymp y == z
z \subset y == z
z \supset y == z
z \supseteq y == z
z \approx y == z  
z \cong y == z
z \sqsubset y == z
z \sqsupset y == z
z \sqsubseteq y == z
z \sqsupseteq y == z
z \doteq y == z
z \propto y == z

z ^+ == z
z ^* == z
z ^# == z
-. z == z


Init == 
 /\ x = 0

Next ==
/\ x = 0
/\ 
   \/ x' = x - 1   
   \/ x' = x + 1
   \/ x' = x * 1
   \/ x' = x / 1
   \/ x' = x ^ 1
   \/ x' = (x < 1)  
   \/ x' = (x > 1)  
   \/ x' = x .. 1
   \/ x' = x ... 1
   \/ x' = x | 1
   \/ x' = x || 1
   \/ x' = x & 1
   \/ x' = x && 1
   \/ x' = x $ 1
   \/ x' = x $$ 1
   \/ x' = x ?? 1
   \/ x' = x %% 1
   \/ x' = x ## 1
   \/ x' = x ++ 1
   \/ x' = x -- 1
   \/ x' = x ** 1
   \/ x' = x // 1
   \/ x' = x ^^ 1
   \/ x' = x !! 1
   \/ x' = (x |- 1)
   \/ x' = (x |= 1)
   \/ x' = (x -| 1)
   \/ x' = (x =| 1)
   \/ x' = (x <: 1)
   \/ x' = (x := 1)
   \/ x' = (x ::= 1)
   \/ x' = (x \uplus 1)
   \/ x' = (x \sqcap 1)
   \/ x' = (x \sqcup 1)
   \/ x' = x \div 1
   \/ x' = x \wr 1
   \/ x' = x \star 1
   \/ x' = x \bigcirc 1
   \/ x' = x \bullet 1
   \/ x' = (x \prec 1 )
   \/ x' = (x \succ 1)
   \/ x' = (x \preceq 1)
   \/ x' = (x \succeq 1)
   \/ x' = (x \sim 1)
   \/ x' = (x \simeq 1)
   \/ x' = (x \ll 1)
   \/ x' = (x \gg 1)
   \/ x' = (x \asymp 1)
   \/ x' = (x \subset 1)
   \/ x' = (x \supset 1)
   \/ x' = (x \supseteq 1)
   \/ x' = (x \approx 1)
   \/ x' = (x \cong 1)
   \/ x' = (x \sqsubset 1)
   \/ x' = (x \sqsupset 1)
   \/ x' = (x \sqsubseteq 1)
   \/ x' = (x \sqsupseteq 1)
   \/ x' = (x \doteq 1)
   \/ x' = (x \propto 1)
   \/ x' = x ^+ 
   \/ x' = x ^* 
   \/ x' = x ^# 
   \/ x' = -x  
=============================================================================
