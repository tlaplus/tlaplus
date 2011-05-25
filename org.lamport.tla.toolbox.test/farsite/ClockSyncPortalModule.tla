---- MODULE ClockSyncPortalModule ----
(*`^\addcontentsline{toc}{section}{ClockSyncPortalModule}^'*)

EXTENDS Naturals
VARIABLE BaseClock

VARIABLE EarlyOffset

VARIABLE LateOffset

(*Defn*)EarlyClock==BaseClock+EarlyOffset

(*Defn*)LateClock==BaseClock+LateOffset

(*Defn*)NowLaterThan(time)==time<EarlyClock

(*Defn*)NowEarlierThan(time)==LateClock<time
====
