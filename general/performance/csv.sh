#!/bin/bash

echo "Implementation,Processors,Insertions,Duration,Memory,LoadFactor,Locks,TblCnt,JunitTime,NUMABalancing,PageDefrag,Govenor"

for file in $1/*-tlc.txt; do
   PROCESSORS=$(echo $file | cut -d "-" -f3)
   IMPL=$(basename $file | cut -d "_" -f1)

   FILE=$(cat $file)
   INSERTIONS=$(echo $FILE | grep -Po 'Total puts: \K[0-9]+')
   DURATION=$(echo $FILE | grep -Po 'duration: \K[^ ]+')
   LOADFACTOR=$(echo $FILE | grep -Po 'total load factor: \K[0-9.]+')
   LOCKS=$(echo $FILE | grep -Po 'FPSet lock count is: \K[0-9]+')
   MEM=$(echo $FILE | grep -Po 'FPSet table count is: \K[^ ]+')
   TBLCNT=$(echo $FILE | grep -Po 'FPSet bucket count is: \K[0-9]+')
   JUNITTIME=$(echo $FILE | grep -Po 'Time: \K[0-9,.]*')
   NUMA=$(echo $FILE | grep -Po 'kernel.numa_balancing = \K[0-9,.]*')
   DEFRAG=$(echo $FILE | grep 'page_defrag = ' | grep -Po '\[.*\]')
   GOVENOR=$(echo $FILE | grep -Po 'scaling_governor = \K[a-z]*')

   echo $IMPL,$PROCESSORS,$INSERTIONS,$DURATION,$(echo $MEM | sed s/,//g),$LOADFACTOR,$LOCKS,$TBLCNT,$(echo $JUNITTIME | sed s/,//g),$NUMA,$DEFRAG,$GOVENOR
done
