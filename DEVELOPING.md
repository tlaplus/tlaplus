Development Notes
=================

Firstly this is not complete. If this doesn't have information you need, please
engage with tlaplus contributors on Github
and add new knowledge, instructions, insights, or tips back to this document to
help the next potential contributor
(or even yourself a few months down the track once you've forgotten everything).


Building TLC / `tlatools.jar`
=============================

While the Toolbox is maintained in [Eclipse](https://github.com/tlaplus/tlaplus/tree/master/general/ide), sometimes changes to TLC do not require building the entire GUI. In such cases, it can be beneficial to compile TLC on the command line. 

While `Maven` is used for the Toolbox (see below), `ant` can be used for the command line. It can be installed with `brew` or `apt` with the package name `ant` (e.g. `brew install ant` and `sudo apt-get install ant`).

Make sure that you're using Java 11+. If you're using a lower version you'll see compilation errors.

You can build TLC from a fresh clone of this repository+:
```bash
$ git clone https://github.com/tlaplus.git
$ cd tlaplus/tlatools/org.lamport.tlatools
$ ant -f customBuild.xml info clean compile compile-test dist
```

The `tlatools.jar` will be created in the `org.lamport.tlatools/dist` directory.

Test that the build was successful by using an example model:
```bash
$ java -jar dist/tla2tools.jar ./test-model/pcal/Bakery.tla
```
To run the unit tests, abbreviate the above `ant` command:
```bash
$ ant -f customBuild.xml test
```

If you're using Linux or OSX, you can install `entr`,
then run the following to watch for and automatically recompile changes:

```sh
find src | entr -ac ant -f org.lamport.tlatools/customBuild.xml compile
```


Building the Toolbox
====================

To build and test the Toolbox (well, everything really), run:

```sh
mvn verify
```

To build without testing, run:

``` sh
mvn install -Dmaven.test.skip=true
```

On completion you'll find the toolbox distributables in `org.lamport.tla.toolbox.product.product/target/products/`

```
> ls -l org.lamport.tla.toolbox.product.product/target/products/
total 475224
drwxr-xr-x 5 golly users      4096 May 19 09:20 org.lamport.tla.toolbox.product.product
-rw-r--r-- 1 golly users 164468054 May 19 09:21 TLAToolbox-1.5.8-linux.gtk.x86_64.zip
-rw-r--r-- 1 golly users 160402860 May 19 09:21 TLAToolbox-1.5.8-macosx.cocoa.x86_64.zip
-rw-r--r-- 1 golly users 161739828 May 19 09:21 TLAToolbox-1.5.8-win32.win32.x86_64.zip
```

Debugging
======================

See guide at https://github.com/tlaplus/tlaplus/tree/master/general/ide.