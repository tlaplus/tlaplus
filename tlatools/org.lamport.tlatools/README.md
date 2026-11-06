Running Tests
--------------

Before run any of the commands below, you have to compile the
application classes (if you changed any of them) or compile the test
classes (if changed as well).

Compiling application classes:

``` shell
ant -f customBuild.xml compile
```

Compiling test classes:

``` shell
ant -f customBuild.xml compile-test
```

To run all the tests:

``` shell
ant -f customBuild.xml test
```

To run a single test:

``` shell
# Running the `tlc2.tool.MonolithSpecTest.java` test
ant -f customBuild.xml test-set -Dtest.testcases="tlc2/tool/MonolithSpecTest*"
```

One tip, if you want to record the output of some tlatool (like if you
were seeing the CLI stdout/stderr), you can use `TestPrintStream` in
combination with `ToolIO`. Search for them in the codebase.

Generating traces
-----------------

`-generate num=200 -depth 100 Spec` selects uniformly over the generated
transitions at each step. It enumerates every successor, so the time per
step grows with the number of successors, while retaining only one.

For specifications with large successor sets, use
`-generate num=200,sampling=fast -depth 100 Spec` to stop at the first
successor found in randomized traversal. This can bias the distribution
depending on the specification's syntax. Properties and constraints are
evaluated only for candidates visited before selection. Use the default
`sampling=uniform` when measuring successor distributions; fast mode does
not provide that guarantee.
