---------------------- MODULE APDiskStateQueueWorkload ----------------------
EXTENDS Integers, FiniteSets

\* Attach Apalache types through INSTANCE without annotating the specification.
CONSTANTS
  \* @type: Bool;
  SpuriousWakeups,
  \* @type: Set(Str);
  Threads,
  \* @type: Set(Str);
  Workers,
  \* @type: Int;
  Capacity,
  \* @type: Str;
  Writer,
  \* @type: Str;
  Reader,
  \* @type: Str;
  Cleaner,
  \* @type: { enq: Int, deq: Int, lo: Int, hi: Int };
  RestoreQueue,
  \* @type: Str;
  Main

VARIABLES
  \* @type: { enq: Int, deq: Int, lo: Int, hi: Int };
  queue,
  \* @type: Int;
  balance,
  \* @type: Int;
  disk,
  \* @type: Int;
  deleted,
  \* @type: { file: Int, done: Bool };
  writer,
  \* @type: { file: Int, cache: Int, canRead: Bool, done: Bool };
  reader,
  \* @type: { done: Bool, limit: Int, ready: Bool };
  cleaner,
  \* @type: Bool;
  finish,
  \* @type: Bool;
  stop,
  \* @type: Set(Str);
  counted,
  \* @type: Str -> Str;
  owner,
  \* @type: Str -> Set(Str);
  waiters,
  \* @type: Str -> Str;
  pc,
  \* @type: Str -> Str;
  op,
  \* @type: Str -> Str;
  kind,
  \* @type: Str -> Bool;
  result,
  \* @type: { enq: Int, deq: Int, lo: Int, hi: Int };
  snapshot,
  \* @type: Int;
  checkpointTo,
  \* @type: Str -> Str;
  stage

\* Fix the argument type; keep the body identical to DiskStateQueue's Size.
\* @type: ({ enq: Int, deq: Int, lo: Int, hi: Int }) => Int;
Size(q) == q.enq + q.deq + Capacity * ( q.hi - q.lo + 1 )

INSTANCE DiskStateQueueWorkload
=============================================================================
