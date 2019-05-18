Development Notes
=================

Firstly this is not complete. If this doesn't have information you need, please
engage with tlaplus contributors on Github
and add new knowledge, instructions, insights, or tips back to this document to
help the next potential contributor
(or even yourself a few months down the track once you've forgotten everything).


Also make sure that you're using Java 11+.
If you're using a lower version you'll see compilation errors.


Building TLC / `tlatools.jar`
=============================

All of the commands below assume you're in the `tlatools` directory
so begin with:

```sh
cd tlatools
```

To build, test, and create `tlatools.jar`:

```sh
ant -f customBuild.xml
```

To watch for, and recompile changes (install `entr` if you haven't already), then run:

```sh
find src | entr -ac ant -f customBuild.xml compile
```

