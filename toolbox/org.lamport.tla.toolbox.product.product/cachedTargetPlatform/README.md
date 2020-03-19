This directory contains files that are referenced in the Toolbox's Maven Tycho build
via the TLAToolbox.target file.  We cache/keep the files in our git repository, because
the upstream download location is unreliable and/or an avoidable source of error.  For
example, upstream abstratt is our only dependency that is hosted on bintray and bintray
sometimes cause problems.  Thus, we keep the actual dependency (abstratt) in our git 
repository and reference it as:

https://raw.githubusercontent.com/tlaplus/tlaplus/master/toolbox/org.lamport.tla.toolbox.product.product/cachedTargetPlatform/com.abstratt.eclipsegraphviz.repository-2.5.201812.zip

in TLAToolbox.target (no, Maven Tycho does *not* work with file URLs).