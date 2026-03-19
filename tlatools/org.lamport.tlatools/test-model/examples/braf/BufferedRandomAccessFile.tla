\* Copyright (c) 2024, Oracle and/or its affiliates.

----------------------- MODULE BufferedRandomAccessFile -----------------------
\* This is a model-checkable specification for BufferedRandomAccessFile.java.
\* It covers the core fields as well as the seek, read, write, flush, and
\* setLength operations.
\*
\* There are three major correctess conditions:
\*
\*   (1) the internal invariants V1-V5 should hold
\*   (2) the behavior should refine a general RandomAccessFile
\*   (3) each operation should refine its RandomAccessFile counterpart
\*
\* Readers will probably want to start with the general RandomAccessFile spec
\* before reading this one.

EXTENDS Naturals, Sequences, TLC, Common

CONSTANT BuffSz

VARIABLES
    \* in-memory variables (BufferedRandomAccessFile class fields)
    dirty,
    length,
    curr,
    lo,
    buff,
    diskPos,

    \* the underlying file
    file_content,
    file_pointer

vars == <<
    dirty, length, curr, lo, buff, diskPos,
    file_content, file_pointer>>

TypeOK ==
    /\ dirty \in BOOLEAN
    /\ length \in Offset
    /\ curr \in Offset
    /\ lo \in Offset
    /\ buff \in Array(SymbolOrArbitrary, BuffSz)
    /\ diskPos \in Offset

    /\ file_content \in ArrayOfAnyLength(SymbolOrArbitrary)
    /\ ArrayLen(file_content) <= MaxOffset
    /\ file_pointer \in Offset

-------------------------------------------------------------------------------
\* Internal invariants (copied from comment in BufferedRandomAccessFile.java)

RelevantBufferContent ==
    ArraySlice(buff, 0, Min(BuffSz, length - lo))

LogicalFileContent == \* denoted c(f) in .java file
    IF ArrayLen(RelevantBufferContent) > 0
    THEN WriteToFile(file_content, lo, RelevantBufferContent)
    ELSE file_content

DiskF(i) == \* denoted disk(f)[i] in .java file
    IF i >= 0 /\ i < ArrayLen(file_content)
    THEN ArrayGet(file_content, i)
    ELSE ArbitrarySymbol

BufferedIndexes == lo .. (Min(lo + BuffSz, length) - 1)

Inv1 ==
    \* /\ f.closed == closed(f) \* close() not described in this spec
    \* /\ f.curr == curr(f)     \* by definition; see `file_pointer <- curr` in refinement mapping below
    /\ length = ArrayLen(LogicalFileContent)
    /\ diskPos = file_pointer

\* Inv2 is a bit special.  Most methods restore it just before they return.  It
\* is generally restored by calling `restoreInvariantsAfterIncreasingCurr()`.
\* But, that behavior is difficult to model in straight TLA+ because each
\* method may modify variables multiple times.  So instead, this spec treats
\* Inv2 as a precondition for the methods and verifies that it is always
\* restored by calling `restoreInvariantsAfterIncreasingCurr()`.
\* See `Inv2CanAlwaysBeRestored` below.
Inv2 ==
    /\ lo <= curr
    /\ curr < lo + BuffSz

Inv3 ==
    \A i \in BufferedIndexes:
        ArrayGet(LogicalFileContent, i) = ArrayGet(buff, i - lo)

Inv4 ==
    \A i \in 0 .. (length - 1):
        i \notin BufferedIndexes =>
            ArrayGet(LogicalFileContent, i) = DiskF(i)

Inv5 ==
    (\E i \in BufferedIndexes: DiskF(i) /= ArrayGet(buff, i - lo)) =>
    dirty

-------------------------------------------------------------------------------
\* Behavior

Init ==
    /\ dirty = FALSE
    /\ length = 0
    /\ curr = 0
    /\ lo = 0
    /\ buff \in Array({ArbitrarySymbol}, BuffSz)
    /\ diskPos = 0
    /\ file_pointer = 0
    /\ file_content = EmptyArray

FlushBuffer ==
    /\ dirty
    /\ LET len == Min(length - lo, BuffSz) IN
        /\ IF len > 0
           THEN LET diskPosA == lo IN \* super.seek(this.lo)
            /\ file_content' = WriteToFile(file_content, diskPosA, ArraySlice(buff, 0, len))
            /\ file_pointer' = diskPosA + len
            /\ diskPos' = lo + len
           ELSE
            UNCHANGED <<diskPos, file_pointer, file_content>>
        /\ dirty' = FALSE
    /\ UNCHANGED <<length, curr, lo, buff>>

\* Helper for Seek (not a full action):
\*  - reads lo'
\*  - constrains diskPos', file_pointer', and buff'
FillBuffer ==
    LET diskPosA == lo' IN
    /\ buff' = MkArray(BuffSz, [i \in 0..BuffSz |->
            LET fileOffset == diskPosA + i IN
            IF fileOffset < ArrayLen(file_content)
            THEN ArrayGet(file_content, fileOffset)
            ELSE ArbitrarySymbol])
    /\ file_pointer' = Min(diskPosA + BuffSz, ArrayLen(file_content))
    /\ diskPos' = Min(diskPosA + BuffSz, ArrayLen(file_content))

Seek(pos) ==
    /\ curr' = pos
    /\ IF pos < lo \/ pos >= (lo + BuffSz) THEN
        /\ ~dirty \* call to FlushBuffer
        /\ lo' = (pos \div BuffSz) * BuffSz
        /\ FillBuffer
       ELSE
        UNCHANGED <<lo, diskPos, file_pointer, buff>>
    /\ UNCHANGED <<dirty, length, file_content>>

SetLength(newLength) ==
    /\ file_content' = TruncateOrExtendFile(file_content, newLength)
    /\ IF ArrayLen(file_content) > newLength /\ file_pointer > newLength
       THEN file_pointer' = newLength
       ELSE file_pointer' \in Offset
    /\ length' = newLength
    /\ diskPos' = file_pointer'
    /\ IF curr > newLength
       THEN curr' = newLength
       ELSE UNCHANGED curr
    \* In reality the buffer doesn't change---but some of its bytes might no
    \* longer be relevant and have to be marked as arbitrary.
    /\ buff' = MkArray(BuffSz, [i \in 0..(BuffSz-1) |->
            IF lo + i < newLength
            THEN ArrayGet(buff, i)
            ELSE ArbitrarySymbol])
    /\ UNCHANGED <<dirty, lo>>

Read1(byte) ==
    /\ Inv2
    /\ curr < length
    /\ byte = ArrayGet(buff, curr - lo)
    /\ curr' = curr + 1
    /\ UNCHANGED <<lo, diskPos, buff, file_pointer, dirty, file_content, length>>

Write1(byte) ==
    /\ curr + 1 <= MaxOffset \* bound model checking
    /\ Inv2
    /\ buff' = ArraySet(buff, curr - lo, byte)
    /\ curr' = curr + 1
    /\ dirty' = TRUE
    /\ length' = Max(length, curr')
    /\ UNCHANGED <<lo, diskPos, file_pointer, file_content>>

Read(data) ==
    LET numReadableWithoutSeeking == Min(lo + BuffSz, length) - curr IN
    /\ Inv2
    /\ numReadableWithoutSeeking >= 0
    /\ LET
            numToRead == Min(ArrayLen(data), numReadableWithoutSeeking)
            buffOff == curr - lo
       IN
        /\ data = ArraySlice(buff, buffOff, buffOff + numToRead)
        /\ curr' = curr + numToRead
    /\ UNCHANGED <<buff, dirty, diskPos, file_content, file_pointer, length, lo>>

\* The `write()` method is composed of repeated calls to `writeAtMost()`, so
\* verifying that the latter maintains all our invariants should be sufficient.
WriteAtMost(data) ==
    LET
        numWriteableWithoutSeeking == Min(ArrayLen(data), lo + BuffSz - curr)
        buffOff == curr - lo
    IN
    /\ Inv2
    /\ curr + numWriteableWithoutSeeking <= MaxOffset
    /\ buff' = ArrayConcat(ArrayConcat(
            ArraySlice(buff, 0, buffOff),
            ArraySlice(data, 0, numWriteableWithoutSeeking)),
            ArraySlice(buff, buffOff + numWriteableWithoutSeeking, ArrayLen(buff)))
    /\ dirty' = TRUE
    /\ curr' = curr + numWriteableWithoutSeeking
    /\ length' = Max(length, curr')
    /\ UNCHANGED <<lo, diskPos, file_content, file_pointer>>

Next ==
    \/ FlushBuffer
    \/ \E offset \in Offset:
        \/ Seek(offset)
        \/ SetLength(offset)
    \/ \E symbol \in SymbolOrArbitrary:
        \/ Read1(symbol)
        \/ Write1(symbol)
    \/ \E len \in 1..MaxOffset: \E data \in Array(SymbolOrArbitrary, len):
        \/ WriteAtMost(data)
        \/ Read(data)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
\* Refinement of general RandomAccessFile

RAF == INSTANCE RandomAccessFile WITH
    file_content <- LogicalFileContent,
    file_pointer <- curr

Safety == RAF!Spec

\* Ensure that the various actions behave according to their abstract specifications.
FlushBufferCorrect  == [][FlushBuffer => UNCHANGED RAF!vars]_vars
SeekCorrect         == [][\A offset \in Offset: Seek(offset) => RAF!Seek(offset)]_vars
SetLengthCorrect    == [][\A offset \in Offset: SetLength(offset) => RAF!SetLength(offset)]_vars
SeekEstablishesInv2 == [][\A offset \in Offset: Seek(offset) => Inv2']_vars
Write1Correct       == [][\A symbol \in SymbolOrArbitrary: Write1(symbol) => RAF!Write(SeqToArray(<<symbol>>))]_vars
Read1Correct        == [][\A symbol \in SymbolOrArbitrary: Read1(symbol) => RAF!Read(SeqToArray(<<symbol>>))]_vars
WriteAtMostCorrect  == [][\A len \in 1..MaxOffset: \A data \in Array(SymbolOrArbitrary, len): WriteAtMost(data) => \E written \in 1..len: RAF!Write(ArraySlice(data, 0, written))]_vars
ReadCorrect         == [][\A len \in 1..MaxOffset: \A data \in Array(SymbolOrArbitrary, len): Read(data) => RAF!Read(data)]_vars

\* Inv2 is a precondition for many actions; it should always be possible to
\* restore Inv2 by execuing `restoreInvariantsAfterIncreasingCurr()`.  That
\* method calls `seeek(curr)`, which is composed of a FlushBuffer followed by a
\* Seek, or just a Seek.
\*
\* To ensure that `restoreInvariantsAfterIncreasingCurr()` works as expected
\* (without using the \cdot action composition operator), we'll verify a few
\* things:
\*  - dirty => ENABLED FlushBuffer
\*  - FlushBuffer => ~dirty'
\*  - ~dirty => ENABLED Seek(curr)
\*  - Seek(curr) => Inv2'
\* Together, those properties ensure that it is always possible to restore Inv2
\* by taking a FlushBuffer action (if necessary) followed by a Seek(curr)
\* action.
FlushBufferPossibleWhenDirty == dirty => ENABLED FlushBuffer
FlushBufferMakesProgress == [][FlushBuffer => ~dirty']_vars
SeekCurrPossibleWhenNotDirty == ~dirty => ENABLED Seek(curr)
SeekCurrRestoresInv2 == [][Seek(curr) => Inv2']_vars
Inv2CanAlwaysBeRestored ==
    /\ []FlushBufferPossibleWhenDirty
    /\ FlushBufferMakesProgress
    /\ []SeekCurrPossibleWhenNotDirty
    /\ SeekCurrRestoresInv2

-------------------------------------------------------------------------------
\* Model checking helper definitions

Symmetry == Permutations(Symbols)

Alias == [
    \* constants
    BuffSz            |-> BuffSz,
    MaxOffset         |-> MaxOffset,

    \* regular vars
    dirty             |-> dirty,
    length            |-> length,
    curr              |-> curr,
    lo                |-> lo,
    buff              |-> buff,
    diskPos           |-> diskPos,
    file_content      |-> file_content,
    file_pointer      |-> file_pointer,

    \* abstract vars
    abstract_contents |-> LogicalFileContent]

===============================================================================

--------------------------- MODULE RandomAccessFile ---------------------------
\* Specification of Java's RandomAccessFile class.
\*
\* A RandomAccessFile offers single-threaded access to some on-disk data
\* (`file_content`) and has an internal "pointer" or "cursor" (`file_pointer`).
\* Clients can move the pointer to an arbitrary position, or the client can
\* read or write data linearly from its current position, which simultaneously
\* advances the pointer.
\*
\* The core operations are:
\*   - seek (to move the pointer)
\*   - setLength (to resize the data)
\*   - read (to copy bytes from disk to memory)
\*   - write (to copy bytes from memory to disk)
\*
\* There are some cases where the general RandomAccessFile contract does not
\* define the data contents, for instance when extending the file using
\* setLength.  In this spec, undefined bytes in the file are explicitly marked
\* with `ArbitrarySymbol`.  While not entirely accurate, that choice simplifies
\* many definitions, since there is no need to nondeterministically choose
\* contents for the file.  It also (incidentally) reduces state space explosion
\* during model checking.

EXTENDS Naturals, Sequences, Common

VARIABLES
    file_content,
    file_pointer

vars == <<file_content, file_pointer>>

TypeOK ==
    /\ file_content \in ArrayOfAnyLength(SymbolOrArbitrary)
    /\ ArrayLen(file_content) <= MaxOffset
    /\ file_pointer \in Offset

Init ==
    /\ file_content = EmptyArray
    /\ file_pointer = 0

Seek(new_offset) ==
    /\ new_offset \in Offset
    /\ file_pointer' = new_offset
    /\ UNCHANGED <<file_content>>

SetLength(new_length) ==
    /\ file_content' = TruncateOrExtendFile(file_content, new_length)

    \* The pointer's behavior is very strange.  Per RandomAccessFile docs [1]:
    \*  > If the present length of the file as returned by the length method is
    \*  > greater than the newLength argument then the file will be truncated.
    \*  > In this case, if the file offset as returned by the getFilePointer
    \*  > method is greater than newLength then after this method returns the
    \*  > offset will be equal to newLength.
    \*
    \* The docs say NOTHING else about the file pointer.  So, we can assume
    \* that there are no other formal restrictions on its behavior.
    \*
    \* [1]: https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/io/RandomAccessFile.html#setLength(long)
    /\ IF ArrayLen(file_content) > new_length /\ file_pointer > new_length
       THEN file_pointer' = new_length
       ELSE file_pointer' \in Offset

Read(output) ==
    /\ output = ArraySlice(file_content, file_pointer, Min(file_pointer + ArrayLen(output), ArrayLen(file_content)))
    /\ file_pointer' = file_pointer + ArrayLen(output)
    /\ UNCHANGED <<file_content>>

Write(data) ==
    /\ file_pointer + ArrayLen(data) <= MaxOffset
    /\ file_content' = WriteToFile(file_content, file_pointer, data)
    /\ file_pointer' = file_pointer + ArrayLen(data)

Next ==
    \/ \E offset \in Offset:
        \/ Seek(offset)
        \/ SetLength(offset)
    \/ \E len \in 1..MaxOffset: \E data \in Array(SymbolOrArbitrary, len):
        \/ Write(data)
        \/ Read(data)

Spec == Init /\ [][Next]_vars

===============================================================================

-------------------------------- MODULE Common --------------------------------
\* This module contains constants and definitions common to both
\* RandomAccessFile and BufferedRandomAccessFile.

EXTENDS Naturals, Sequences

CONSTANTS
    Symbols, \* data stored in the file (in reality there are 256 symbols: bytes 0x00 to 0xFF)
    ArbitrarySymbol, \* special token for an arbitrary symbol (to reduce the need for nondeterministic choice)
    MaxOffset \* the highest possible offset (in reality this is 2^63 - 1)

\* The set of legal offsets
Offset == 0..MaxOffset

\* The set of things that can appear at an offset in a file
SymbolOrArbitrary == Symbols \union {ArbitrarySymbol}

\* Minimum and maximum of two numbers
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a <= b THEN b ELSE a

\* Definitions for 0-indexed arrays (as opposed to TLA+ 1-indexed sequences).
\* A major goal of the BufferedRandomAccessFile spec is to prevent off-by-one
\* errors in the implementation; therefore it should use 0-indexed arrays like
\* Java.
\*
\* The definitions are deliberately crafted so that the usual sequence
\* operators do NOT work on them; this is to help avoid accidental mixing of
\* sequences and arrays.
ArrayOfAnyLength(T) == [elems: Seq(T)]
Array(T, len) == [elems: [1..len -> T]]
ConstArray(len, x) == [elems |-> [i \in 1..len |-> x]]
MkArray(len, f) == [elems |-> [i \in 1..len |-> f[i - 1]]]
EmptyArray == [elems |-> <<>>]
ArrayLen(a) == Len(a.elems)
ArrayToSeq(a) == a.elems
SeqToArray(seq) == [elems |-> seq]
ArrayGet(a, i) == a.elems[i+1]
ArraySet(a, i, x) == [a EXCEPT !.elems[i+1] = x]
ArraySlice(a, startInclusive, endExclusive) == [elems |-> SubSeq(a.elems, startInclusive + 1, endExclusive)]
ArrayConcat(a1, a2) == [elems |-> a1.elems \o a2.elems]

\* General contract of the file `write()` call: extend the file with
\* ArbitrarySymbols if necessary, then overlay some `data_to_write` at the
\* given offset.
WriteToFile(file, offset, data_to_write) ==
    LET
       file_len == ArrayLen(file)
       data_len == ArrayLen(data_to_write)
       length == Max(file_len, offset + data_len)
    IN
    MkArray(
        length,
        [i \in 0..(length-1) |->
            CASE
                i < offset -> IF i < file_len THEN ArrayGet(file, i) ELSE ArbitrarySymbol
                []
                i >= offset /\ i < offset + data_len -> ArrayGet(data_to_write, i - offset)
                []
                i >= offset + data_len -> ArrayGet(file, i)])

\* General contract of the file `setLength()` call: truncate the file or fill
\* it with ArbitrarySymbol to reach the desired length.
TruncateOrExtendFile(file, new_length) ==
    IF new_length > ArrayLen(file)
    THEN ArrayConcat(file, ConstArray(new_length - ArrayLen(file), ArbitrarySymbol))
    ELSE ArraySlice(file, 0, new_length)

===============================================================================
