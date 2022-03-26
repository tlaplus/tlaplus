#!/bin/bash

SPEC="${1-"Bloemen"}"

# Performance related properties
BAQUEUE=${2-"true"}
WORKERS=${3-"$(nproc --all)"}
HEAP_MEM=${4-"8G"}
DIRECT_MEM=${5-"8g"}
FPSET_IMPL="tlc2.tool.fp.OffHeapDiskFPSet"

# TLC version
REV=$(git rev-parse HEAD)

# measure.sh's fs path
#DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# TLC's code location
TLATOOLS_HOME="../../tlatools/org.lamport.tlatools/dist/tla2tools.jar"

# Trap interrupts and exit instead of continuing the for loop below
trap "echo Exited!; exit;" SIGINT SIGTERM

######################################

# Repeat N times to even out noise...
for i in {1..3}; do
        # For varying worker (core) counts...
        for ((w=$WORKERS; w > 0;w=w/2)); do

          # Output/log files
          JFR_OUTPUT_FILE=$REV'_w'$w'_i'$i.jfr
          TIME_OUTPUT_FILE=$REV-$w.txt
          TLC_OUTPUT_FILE=$REV-$i-$w-tlc.txt

          /usr/bin/time --append --output=$TIME_OUTPUT_FILE \
          java \
           -XX:+UseParallelGC \
           -Xmx$HEAP_MEM -Xms$HEAP_MEM \
           -XX:MaxDirectMemorySize=$DIRECT_MEM \
           -Dtlc2.tool.fp.FPSet.impl=$FPSET_IMPL \
           -Dtlc2.tool.ModelChecker.BAQueue=$BAQUEUE \
           -DTLA-Library=.. \
           -cp "$TLATOOLS_HOME" \
           -DspecName=$SPEC \
           tlc2.TLC -deadlock -checkpoint 99999 -workers $w "${SPEC}/MC.tla" 2>&1 | tee $TLC_OUTPUT_FILE;
          # newer TLC versions support "-checkpoint 0", but 99999 suffices.

          # cleanup left-over states/ directory to free disk space
          rm -rf states/

          # Notify user of completion
          #cat $TLC_OUTPUT_FILE | mail -s "Model: $MODEL Workers: $w" $(id -u -n)
        done
done
