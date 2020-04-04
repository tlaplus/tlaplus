This is a fragment bundle to Mylyn's notification feed bundle. The Mylyn
bundle is broken on Java 11 (https://bugs.eclipse.org/541569) because
Java 11 finally removes the (previously deprecated) java.se.ee module
(https://openjdk.java.net/jeps/320).

This fragment causes the feed bundle to use the classes in the packages
javax.xml.bind and com.sun.xml provided by the nested libraries (plain
jars) in the lib/ directory instead of XML provided by the JVM itself.

Once Mylyn bug #541569 has been addressed and a new Mylyn release
consumed by the Toolbox (via the .target file), this bundle can probably
be removed again.

--

A similar change (include jaxb-api) was required to fix problems with
jclouds
(ttps://github.com/lemmy/jclouds2p2/commit/38296ac50042c18c17d0c91f3bbd2872d6c2e4ac).