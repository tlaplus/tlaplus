# Test Benchmark

## Run JMH benchmarks from maven

To build and run all the benchmarks, run:

``` shell
mvn verify -P benchmark
```

To run a specific benchmark

``` shell
mvn verify -P benchmark -Dbenchmark.class=BENCHMARK_CLASS_WITH_PACKAGE
```

## Run JMH benchmarks from inside Eclipse:

1. Activate Annotation Processing in the project preferences of the tlatools project under "Java Compiler" > "Annotation
   Processing"
2. Add the two jars from lib/jmh/jmh-*.jar as annotation processors to "Java Compiler" > "Annotation Processing" > "
   Factory Path"
3. Add lib/jmh/commons-math3-*.jar to the launch configs classpath
4. Add a main to the benchmark as shown in the various JMH
   examples (https://hg.openjdk.java.net/code-tools/jmh/file/tip/jmh-samples/src/main/java/org/openjdk/jmh/samples/)

## Run JMH benchmarks from command line:

1. Build the benchmark jar
    ``` shell
    mvn package -P benchmark
    ```

2. Run the benchmark jar with appropriate command line arguments (replacing items in all CAPS)
    ``` shell
    java -jar target/org.lamport.tlatools-1.0.0-SNAPSHOT-benchmark.jar -wi 1 -i1 -f1 \
        -rf json \
        -rff Benchmark-$(date +%s)-$(git rev-parse --short HEAD).json \
        -jvmArgsPrepend "-ea -Xms8192m -Xmx8192m" \
        -jvmArgsAppend "-Dtlc2.tool.ModuleOverwritesBenchmark.base=TEST_MODEL_DIRECTORY" \
        CLASS_TO_TEST( e.g. tlc2.tool.queue.DiskQueueBenchmark)
    ```

