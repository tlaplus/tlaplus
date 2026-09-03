---- MODULE StringFormFeedEscape ----
\* The \f escape denotes a form feed (U+000C), which XML 1.0 cannot represent
\* in character data, not even as a numeric character reference.
op == "\f"
====
