#!/bin/bash

##
##
## Generating the feature.xml with this script has proven difficult. Neither BSN nor Bundle-Version align with file names and thus the feature is broken.
##
##

mkdir -p target/source/features/org.apache.jclouds.feature/

echo '<?xml version="1.0" encoding="UTF-8"?>' >> target/source/features/org.apache.jclouds.feature/feature.xml
echo '<feature id="org.apache.jclouds.feature" label="Apache jclouds Feature" version="1.0.0.qualifier" provider-name="Markus A. Kuppe">' >> target/source/features/org.apache.jclouds.feature/feature.xml
echo '<description></description><license url=""></license>' >> target/source/features/org.apache.jclouds.feature/feature.xml


for f in target/source/plugins/*; 
do 
	# without suffix
	F=`basename $f .jar`
	ARTEFACT=${F%-[0-9.]*}
	VERSION=${F##*-}
	VERSION=${VERSION/_/.}
	echo "<plugin id=\"${ARTEFACT}\" download-size=\"0\" install-size=\"0\" version=\"${VERSION}\" unpack=\"false\"/>" >> target/source/features/org.apache.jclouds.feature/feature.xml;

	
done

echo "<plugin id=\"com.google.guava\" download-size=\"0\" install-size=\"0\" version=\"15.0.0\" unpack=\"false\"/>" >> target/source/features/org.apache.jclouds.feature/feature.xml;
echo "<plugin id=\"com.google.gson\" download-size=\"0\" install-size=\"0\" version=\"2.2.4\" unpack=\"false\"/>" >> target/source/features/org.apache.jclouds.feature/feature.xml;
echo "<plugin id=\"com.google.inject\" download-size=\"0\" install-size=\"0\" version=\"3.0.0\" unpack=\"false\"/>" >> target/source/features/org.apache.jclouds.feature/feature.xml;
echo "<plugin id=\"com.google.inject.assitedinject\" download-size=\"0\" install-size=\"0\" version=\"3.0.0\" unpack=\"false\"/>" >> target/source/features/org.apache.jclouds.feature/feature.xml;

echo '</feature>' >> target/source/features/org.apache.jclouds.feature/feature.xml