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
