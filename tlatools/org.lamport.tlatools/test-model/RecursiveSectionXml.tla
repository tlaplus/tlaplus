---- MODULE RecursiveSectionXml ----
RECURSIVE f(_), g(_)
f(x) == f(x)
g(x) == g(x)

RECURSIVE h(_)
h(x) == h(x)

nonRecursive == 42
====
