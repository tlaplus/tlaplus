This folder contains all libraries and config files to profile TLC with Java Flight Recorder (JFR).

A default JFR is created with:

-XX:StartFlightRecording=settings=default
-XX:FlightRecorderOptions=defaultrecording=true,disk=true,repository=/tmp,dumponexit=true,dumponexitpath=dump.jfr,maxage=1h,settings=${project_loc:tlatools}/jfr/tlc.jfc

To additionally record JMX data in the flight recording, add:

-javaagent:${project_loc:tlatools}/jfr/jmx2jfr.jar=${project_loc:tlatools}/jfr/jmxprobes.xml

and replace the "default" settings with ${project_loc:tlatools}/jfr/tlc.jfc

Afterwards, the resulting flight recording can be opened with Java Mission Control (JMC).	


Further processing (charting...) is best done by converting the .jfr to xml:

java oracle.jrockit.jfr.parser.Parser -xml dump.jfr > dump.xml

To select all TLC related elements, do:

xmlstarlet sel 
  -N jfr=http://www.oracle.com/hotspot/jvm/
  -N jvm=http://www.oracle.com/hotspot/jvm/ 
  -N p4108=http://www.hirt.se/jfr/jmx2jfr/
  -t -c "//p4108:MBeans_tlc2_tool_ModelChecker" dump.xml

Do print all the attributes of "StatesGeneratedPerMinute do:

xmlstarlet sel 
  -N jfr=http://www.oracle.com/hotspot/jvm/ 
  -N jvm=http://www.oracle.com/hotspot/jvm/ 
  -N p4108=http://www.hirt.se/jfr/jmx2jfr/ 
  -t -v "//p4108:MBeans_tlc2_tool_ModelChecker/p4108:StatesGeneratedPerMinute" dump.xml

---
http://www.slideshare.net/marcushirt/java-mission-control-java-flight-recorder-deep-dive
https://docs.oracle.com/javase/8/docs/technotes/guides/troubleshoot/tooldescr004.html#BABHCDEA
https://docs.oracle.com/javacomponents/jmc-5-4/jfr-runtime-guide/run.htm#JFRUH179
http://hirt.se/blog/?p=689
http://hirt.se/blog/?p=446