Check fix to handling of ThmOrAssumpDefNode in Tool.java
on 23 Oct 2012.

---- MODULE test218 ----
EXTENDS Test218a, TLC

I(z) == INSTANCE Test218a WITH y <- z

ASSUME PrintT(I(55)!Foo)

===============================