Sany should produce two level errors when parsing this module.

---- MODULE test217 ----
    \* 12 June 2014: Changed module name from Test217, which is now illegal
EXTENDS test217a
    \* 12 June 2014: Changed from Test217a, which is now illegal
VARIABLE x

I(z) == INSTANCE test217a WITH y <- z
    \* 12 June 2014: Changed from Test217a, which is now illegal

FooBar == I(x')!Foo
THEOREM I({x'})!Foo
===============================