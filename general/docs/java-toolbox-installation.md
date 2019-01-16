### TLA   Tools and Toolbox and the 2019 Oracle change of license

Oracle's [January 2019 license update](https://www.java.com/en/download/release_notice.jsp) for Oracle Java SE effectively means that Oracle Java SE will not be available for business, commercial or production use without a commercial license (see e.g. [Jetbrain's announcement](https://blog.jetbrains.com/idea/2018/09/using-java-11-in-production-important-things-to-know/) for background information).  Thus, all affected TLA+ users that do not purchase a license from Oracle will have to switch to an alternative Java distribution such as [Zulu](https://www.azul.com/downloads/zulu/), [Amazon](https://aws.amazon.com/corretto/), [RedHat](), [OpenJDK](http://jdk.java.net/), [AdoptOpenJDK](https://adoptopenjdk.net/)... (see [Stephen Colebourne's blog post](https://blog.joda.org/2018/09/time-to-look-beyond-oracles-jdk.html) for details).

### AdoptOpenJDK

At the time of writing, the best choice is the [OpenJDK 8 (LTS) Hotspot](https://adoptopenjdk.net/releases.html) JRE distributions which is available for [Windows](https://github.com/AdoptOpenJDK/openjdk8-binaries/releases/download/jdk8u192-b12/OpenJDK8U-jre_x64_windows_hotspot_8u192b12.zip), [macOS](https://github.com/AdoptOpenJDK/openjdk8-binaries/releases/download/jdk8u192-b12/OpenJDK8U-jre_x64_mac_hotspot_8u192b12.tar.gz), and [Linux](https://github.com/AdoptOpenJDK/openjdk8-binaries/releases/download/jdk8u192-b12/OpenJDK8U-jre_x64_linux_hotspot_8u192b12.tar.gz).



The TLA+ project has retroactively checked compatibility of its [1.5.7 Toolbox release](https://github.com/tlaplus/tlaplus/releases/tag/v1.5.7) and will immediately shift testing of future releases to run on the AdoptOpenJDK distribution.  Additionally, [issue #176](https://github.com/tlaplus/tlaplus/issues/176) lays out the plan to include Java in future Toolbox releases to free TLA+ users from manually installing Java.  Until then please manually download the AdoptOpenJDK distribution.  Afterwards extract the downloaded AdoptOpenJDK zip file into a newly created ```jre/``` folder under Toolbox's ```toolbox``` directory.  The Toolbox will automatically run with the AdoptOpenJDK distribution.  The [screencast](https://www.youtube.com/watch?v=TBjVTOy_rcE) below outlines all steps from downloading, installing to running the Toolbox with AdoptOpenJDK.

[![Installation screencast](https://img.youtube.com/vi/TBjVTOy_rcE/0.jpg)](https://www.youtube.com/watch?v=TBjVTOy_rcE)
