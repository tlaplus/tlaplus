Development Notes
=================

Firstly this is not complete. If this doesn't have information you need, please
engage with tlaplus contributors on Github
and add new knowledge, instructions, insights, or tips back to this document to
help the next potential contributor
(or even yourself a few months down the track once you've forgotten everything).


Building TLC / `tlatools.jar`
=============================

Firstly, make sure that you're using Java 11+.
If you're using a lower version you'll see compilation errors.

All of the commands below assume you're in the `tlatools` directory
so begin with:

```sh
cd tlatools
```

To build, test, and create `tlatools.jar`:

```sh
ant -f customBuild.xml
```

If you're using Linux or OSX, you can install `entr`,
then run the following to watch for and automatically recompile changes:

```sh
find src | entr -ac ant -f customBuild.xml compile
```


Building the Toolbox
====================

To build and test the Toolbox (well, everything really), run:

```sh
mvn verify
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
