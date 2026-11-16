---------------------------- MODULE Github1394Ext ----------------------------
EXTENDS Github1394
A == INSTANCE Github1394 WITH x <- x + 1
InstSmall == A!SpecSmall
==============================================================================
