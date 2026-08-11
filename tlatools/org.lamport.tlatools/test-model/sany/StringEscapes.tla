---- MODULE StringEscapes ----
\* Every escape sequence TLA+ string literals support, except \f which is
\* exercised separately by StringFormFeedEscape.tla.
op == "\\ \n \r \t \""
====
