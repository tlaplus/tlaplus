Imported by TowerOfHanoi.tla.
-------------------------------- MODULE Bits --------------------------------
LOCAL INSTANCE Integers

\* & infix operator is implemented by Bits.java.
\* In order to use it, manually compile Bits.java:
\* > javac -cp /path/to/tla2tools.jar Bits.java
\*
\* If you don't have tla2tools.jar, but the TLA+
\* Toolbox installed in /opt/TLA+Toolbox, do:
\* > javac -cp /opt/TLA+Toolbox/plugins/org.lamport.tlatools_*/ Bits.java
\*
\* Place the resulting Bits.class next to Bits.tla (and Bits.java).
\*
\* If TLC correctly loads Bits.class, it prints the following message at
\* startup:
\*
\* @!@!@STARTMSG 2168:0 @!@!@
\* Loading And operator override from /Hanoi.toolbox/Model_1/Bits.class with signature:
\* <Java Method: public static tlc2.value.IntValue Bits.And(tlc2.value.IntValue,tlc2.value.IntValue)>.
\* @!@!@ENDMSG 2168 @!@!@
\*
\* If Bits.class is missing, TLC will fail to check Hanoi.tla with the
\* following message (because of the TLA+ AND operator defined to be FALSE below):
\*
\* @!@!@STARTMSG 1000:1 @!@!@
\* TLC threw an unexpected exception.
\* This was probably caused by an error in the spec or model.
\* See the User Output or TLC Console for clues to what happened.
\* The exception was a java.lang.RuntimeException
\* : Attempted to compare equality of boolean FALSE with non-boolean:
\* 0
\* @!@!@ENDMSG 1000 @!@!@
\*
\*
\* If TLC shows an error similar in words to:
\*
\* Found a Java class for module Bits, but unable to read
\* it as a Java class object. Bits : Unsupported major.minor version 52.0
\*
\* compile Bits.java with a Java version identical to the Toolbox's VM.
\*
\*
\* https://en.wikipedia.org/wiki/Bitwise_operation#Mathematical_equivalents
RECURSIVE And(_,_,_,_)
LOCAL And(x,y,n,m) == LET exp == 2^n
                IN IF m = 0
                   THEN 0
                   ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2)
                        + And(x,y,n+1,m \div 2)

(***************************************************************************)
(* Bitwise AND of x and y                                                  *)
(***************************************************************************)
x & y == And(x, y, 0, x) \* Infix variant of And(x,y)

=============================================================================
\* Modification History
\* Last modified Thu April 25 10:56:12 CEST 2018 by markus
\* Created Mon May 16 15:09:18 CEST 2016 by markus