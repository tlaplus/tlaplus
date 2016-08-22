#!/bin/bash
DIR=$1
FILE=$2
CP=`dirname $0`/../../dist/tla2tools.jar

function fail { # echo a failure message and exit
	echo "FAILED" $1
	exit 1
}

function nooverwrite { # test if a file already exists; if so -- exit
	if [ -f $1 ]; then
    	echo "File $1 already exists. Quitting."
    	exit 2
	fi
}

function convert { # convert Unicode/ASCII
	# params: a2u/u2a file tag
	nooverwrite ${FILE}_$3.tla
	java -cp $CP tla2unicode.TLAUnicode -$1 $2.tla ${FILE}_$3.tla
}

# Convergence
# When converting back and forth, we'll quickly reach two stable versions

>&2 echo Conversion 1
convert a2u $FILE 1
>&2 echo Conversion 2
convert u2a ${FILE}_1 2
>&2 echo Conversion 3
convert a2u ${FILE}_2 3
>&2 echo Conversion 4
convert u2a ${FILE}_3 4
>&2 echo Conversion 5
convert a2u ${FILE}_4 5

# We don't stop on convergence failure
diff ${FILE}_3.tla ${FILE}_5.tla || Echo "FAILED convergence 1"
diff ${FILE}_2.tla ${FILE}_4.tla || Echo "FAILED convergence 2"

rm ${FILE}_3.tla ${FILE}_4.tla ${FILE}_5.tla 

# Idempotence
# Conversion of ASCII to ASCII or Unicode to Unicode is a no-op

convert a2u ${FILE}_1 a
diff ${FILE}_1.tla ${FILE}_a.tla || fail "idempotence 1"

convert u2a ${FILE}_2 b
diff ${FILE}_b.tla ${FILE}_b.tla || fail "idempotence 2"

rm ${FILE}_a.tla ${FILE}_b.tla

# Equivalence
# Coversion maintains semantic parsing

function toxml { # parse to XML
	nooverwrite $1.xml
	mkdir tmpdir
	cp $1.tla tmpdir/$FILE.tla # We must preserve the file name to match the toplevel module name
	java -cp $CP tla2sany.xml.XMLExporter -o -I $DIR -I /usr/local/lib/tlaps tmpdir/$FILE.tla > $1.0.xml
	# remove location information from XML
	xmllint --format $1.0.xml | gawk -e '/<location>/ {location++} /<\/location>/ {location--;next} {if(location==0)print}' > $1.xml
	rm $1.0.xml
	rm tmpdir/$FILE.tla
	rmdir tmpdir
}

>&2 echo Parse ASCII
toxml $FILE
>&2 echo Parse Unicode
toxml ${FILE}_1
>&2 echo Parse ASCII 2
toxml ${FILE}_2

diff ${FILE}.xml ${FILE}_1.xml || fail "equivalence 1"
diff ${FILE}.xml ${FILE}_2.xml || fail "equivalence 2"

rm ${FILE}.xml ${FILE}_1.tla ${FILE}_1.xml ${FILE}_2.tla ${FILE}_2.xml 

echo "SUCCESS!"
