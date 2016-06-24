#!/bin/bash

SPEC="Grid5k"

# Check Grid5k.tla for semantical meaning
K=${1-"04"}
L=${2-"01"}
N=${3-"10"}
C=${4-"04"}
MODEL='k'$K'_l'$L'_n'$N'_c'$C

# Performance related properties
WORKERS=${5-"$(nproc --all)"}
HEAP_MEM=${6-"128G"}
DIRECT_MEM=${7-"128g"}
FPSET_IMPL="tlc2.tool.fp.OffHeapDiskFPSet"

# TLC version
REV=$(git rev-parse HEAD)

# measure.sh's fs path
#DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# TLC's code location
TLATOOLS_HOME=../../tlatools/

# Trap interrupts and exit instead of continuing the for loop below
trap "echo Exited!; exit;" SIGINT SIGTERM

######################################

# Generate TLC's config on-the-fly
cat > $MODEL.cfg <<EOF
CONSTANT K = $K
CONSTANT L = $L
CONSTANT N = $N
CONSTANT C = $C
INIT Init
NEXT Next
EOF

# Repeat N times to even out noise...
for i in {1..3}; do
        # For varying worker (core) counts...
        for ((w=$WORKERS; w > 0;w=w/2)); do

          # Output/log files
          JFR_OUTPUT_FILE=$REV'_w'$w'_i'$i.jfr
          TIME_OUTPUT_FILE=$REV-$w.txt
          TLC_OUTPUT_FILE=$REV-$i-$w-tlc.txt

          /usr/bin/time --append --output=$TIME_OUTPUT_FILE \
          java -XX:+UnlockCommercialFeatures \
           -XX:+FlightRecorder \
           -XX:FlightRecorderOptions=defaultrecording=true,disk=true,repository=/tmp,dumponexit=true,dumponexitpath=$JFR_OUTPUT_FILE,maxage=12h,settings=$TLATOOLS_HOME/jfr/tlc.jfc \
           -javaagent:$TLATOOLS_HOME/jfr/jmx2jfr.jar=$TLATOOLS_HOME/jfr/jmxprobes.xml \
           -Xmx$HEAP_MEM -Xms$HEAP_MEM \
           -XX:MaxDirectMemorySize=$DIRECT_MEM \
           -Dtlc2.tool.fp.FPSet.impl=$FPSET_IMPL \
           -cp $TLATOOLS_HOME/class:$TLATOOLS_HOME/lib/* \
           -DspecName=$SPEC \
           -DmodelName=$MODEL \
           tlc2.TLC -deadlock -checkpoint 99999 -workers $w -config $MODEL $SPEC 2>&1 | tee $TLC_OUTPUT_FILE;
          # newer TLC versions support "-checkpoint 0", but 99999 suffices.

          # cleanup left-over states/ directory to free disk space
          rm -rf states/

          # Notify user of completion
          cat $TLC_OUTPUT_FILE | mail -s "Model: $MODEL Workers: $w" $(id -u -n)
        done
done
