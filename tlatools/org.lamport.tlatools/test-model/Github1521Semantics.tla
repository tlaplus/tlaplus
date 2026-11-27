------------------------ MODULE Github1521Semantics ------------------------
\* https://github.com/tlaplus/tlaplus/issues/1521
VARIABLES x, checks

Index(b) == IF b THEN 2 ELSE 1
WithArg(v) == [<<v>> EXCEPT ![1] = @']

Init == /\ x = FALSE
        /\ checks = TRUE

Step(check) == /\ x' = ~x
               /\ checks' = check
AllCorrect == checks

DirectPrime == Step(
    [<<x>> EXCEPT ![1] = @'] = <<x'>>
)

IndirectPrime == Step(
    [<<x>> EXCEPT ![1] = LET a == @ IN a'] = <<x'>>
)

Unchanged == Step(
    [<<x>> EXCEPT ![1] = UNCHANGED @] = <<UNCHANGED x>>
)

PrimedPath == Step(
    [<<FALSE, TRUE>> EXCEPT ![Index(x)] = @'] =
       [<<FALSE, TRUE>> EXCEPT ![Index(x)] = x']
)

\* The second @ refers to the result of the preceding update.
PriorUpdate == Step(
    [<<x>> EXCEPT ![1] = ~@, ![1] = @'] = <<~x'>>
)

\* The inner EXCEPT uses an outer @ as its base.
NestedBase == Step(
    [<<<<x>>>> EXCEPT ![1] = [@ EXCEPT ![1] = @']] = <<<<x'>>>>
)

\* The inner path uses an outer @.
NestedPath == Step(
    [<<1>> EXCEPT ![1] = [<<x>> EXCEPT ![@] = @']] = <<<<x'>>>>
)

NestedSelector == Step(
    [[a |-> <<x>>] EXCEPT !.a[1] = @'] = [a |-> <<x'>>]
)

OperatorArgument == Step(
    WithArg(x) = <<x'>>
)

\* Control: prime encloses the whole EXCEPT.
WholePrime == Step(
    [<<x>> EXCEPT ![1] = @]' = <<x'>>
)

\* Control: repeated unprimed @.
Unprimed == Step(
    [<<x>> EXCEPT ![1] = @ /\ @] = <<x>>
)

Enabled == Step(
    ENABLED (/\ x' = ~x
                /\ [<<x>> EXCEPT ![1] = @'] = <<~x>>)
)

=============================================================================
