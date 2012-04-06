#!/bin/bash
#
# To run this script the ec2-ami-tools have to be installed on your system. 
# Afterwards the following command will create a new instance and execute this script right after system startup. 
# It should be good for TLC development afterwards.
#
# ec2-run-instances -m --key markus@kuppe.org --instance-type m2.4xlarge --user-data-file /path/to/ProvisionEC2.sh ami-c162a9a8
#

# switch to mount to use the instance ephemeral storage rather than ESB
cd /mnt

# download non pkg mgmt provided tools in background
# no package mgmt for Eclipse profiler, hence install manually into /opt
(wget -q http://www.yourkit.com/download/yjp-10.0.4-linux.tar.bz2  && cd /opt && tar xfj /mnt/yjp-10.0.4-linux.tar.bz2) &

# no package mgmt for yourkit profiler, hence install manually into /opt
(wget -q ftp://mirror.cc.vt.edu/pub/eclipse/technology/epp/downloads/release/indigo/SR1/eclipse-rcp-indigo-SR1-linux-gtk-x86_64.tar.gz && cd /opt && tar xfz /mnt/eclipse-rcp-indigo-SR1-linux-gtk-x86_64.tar.gz) & 

# apache maven 3
(wget -q http://apache.osuosl.org/maven/binaries/apache-maven-3.0.4-bin.tar.gz && cd /opt && tar xfz /mnt/apache-maven-3.0.4-bin.tar.gz) &

# aapche ant
(wget -q http://apache.osuosl.org/ant/binaries/apache-ant-1.8.3-bin.tar.gz && cd /opt && tar xfz /mnt/apache-ant-1.8.3-bin.tar.gz) &

# create user kuppe and setup public key
useradd --home /mnt/kuppe -m kuppe -s /bin/bash -G admin,sudo
ln -s /mnt/kuppe /home/kuppe
mkdir /home/kuppe/.ssh
# personal one to ssh into the box
echo "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQDaFesWicuMjw2s9+4rl36IP781nZ07Vasir5nybvVmmN2wDV1sTcv0iS8VgH54qxmCtV2zQiub0gMq4kHnnTVMKdlMGOyhbvC4X3UVmhJFrD+8UG5bmsbEVXjmgh7Y1oEoldrIf4DlnnHcetdSwuMvV5xqI3iZ+8xg0j9pnN8a9xWj5dUv/rkq2Z5So7AYd+aVCU6uETh8N9fsMZSo/Eu9A+vYvwWhsysY0S8m7wr9zkd71fjc1mTPlAsZGtzACRswrk3S2NLdCd7NNOU1jT5QVffc7poTeCngMFrXjmtUPZZQxOfA6oDq0rSCep+TgjVa2KQAypMDQTjKfkwjaklL markus@kuppe.org" >> /home/kuppe/.ssh/authorized_keys
echo "ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAy4sKgMk2QS8wKze690bmar4cJXz2/AGJr36uJ8gds6zAhM9cyQ4GEuOgOORAOWcUAg3HZI65GdCqtHE+P4t9P5Qi1bE+d24ZL0Ebg6z5P8f8XvSId7Gd/p7YXgCcOJj4nxRHRr3fmHvLw+s0PLCaCg5uqShOBhyxbD8H8pgh4WqxUhHtAeIV+OhuazgLjCYL9b2DFSUtad6j+c+podcZGOJq+DLhP3NWJI5eiO2u7PuX06sRCTo4UxZlP+bvjhU7tH/VRIg9R7CO9TvmMykJEAwa6G5vf4kCFeh9f0pYA26UUFg8z0P2ki7+Z0zHXD3w7zbDYzZ9snFY9RtajtNkXw== markus@kuppe.org" >> /home/kuppe/.ssh/authorized_keys
# ec2 keypair to ssh out
echo "-----BEGIN RSA PRIVATE KEY-----
MIIEowIBAAKCAQEA2PhIljjYT3rrqQ9uprXj6xQ83peXsB3C6MNBX3QjZ08kXV0S
VaPIsg0Tj+WMjX6YZoHs7EXL+trFwH7eLKiqFcNeJbl/Vz4zVgwEbE2zzsoQU7CX
uqjJv/J2e/Mxmy/BBFlROdpd68djFmMuu1cAWgD+bM1VaZo/u1SeHwof9VafTkYD
scIM3aZLdqsfE5+alZIzsMaqRrADbGly5n3UaPXlxVzvOOTpO28rT6ncCbEqAdrU
VB/K8B61T0LCbF2J00BSn/JoX9tbsYXbJx4OI1hJNTMv1yPsf5o0fJLEFnKY7plQ
BcO35TA9WWAYo6Nwkfm9hrVeLik8Y3/G2xHAZwIDAQABAoIBAEVMZ8KzPUOFeydw
KmNMzRMUT6y4tlYl6070rjiSm4wvlunLBEQeH8ferVTUeGPo/zweW1HLqS7iGS82
VjflVw3EbJmX+bgfwb3F8NO2ratqlnRkftG7f1SzWGyWbE2onvmInYzg1gaslFVe
MFrdmtskXh7aJmGoRprKmAZJ8ZMmFJVjJAfRPud59kcWMy8p6vopTnMvD0erAP5i
eVhq9uzEpeQnNewxURSjigCXJW61UF1rWbNbAd6sb/kIYW3nit7g0yAYBfp0u+ay
dbHampIrxLO2czzOtkzn1AMZsP1l87Bpan0BorxnuBMUe4bXOeLoXrh24yYwr4Lm
3PVt0mECgYEA/njoI6002yai8sAeO+v9dSJcBJyG41mx8e4xuNof39Wq7UEUdBFa
9Jf6G1FhgW0y8vD5jOKjWGpNvPpWVZ+Egd/OcYBDqanhV50NVvl7+OIMy/qZHj46
dWDFmd5WYaacock5E+brV4xyPCsE3Pq8N0qvy6WmvyygpFZj+Jr/5o0CgYEA2kW9
crGRLCEPzL0/IAs/Ae7UbwMPRFL2n9WMBQ6EBf6ICirLXc8/PR1PaRNabgKOXsF8
XgLq5PnHM9mKzIJhEagP9yBtQ6VcBf6sH1mC0Vgcr6wO88PXFQo1gP85WbD2MMtM
07Hl7jDLD3sB+HOYZ3tpCcp8NRSQyrBToB1mb8MCgYBpfXW+VG806i9isoHWFV5c
0IGU586DMQuzXyr9lm7gO5NAB1qTQx6Rhu8HpBTnsn0MeRj6bnmIjYjsblqb5CTq
Mf1C0Ak8rE/eIh0FkSbzZcIoTRpsjx9syVEhGCp3ELqd1uzycyfcgzxX9P1vHgIo
aa22nlUhqz5s4eNPi/HJgQKBgEa69LIW8lkfeZQ5+xuyKT/CGdrDXg4g6ERRGeeF
laivm3vX9EC46OAwAEynddVSRLpV7qw0O9PpUPDvXLf6w+PJ1yqYum+CRTi4FySt
h+O4rssKcWnym175CO99RSNYYd7b8lBjRIQUEak5jiDprIhUCGygzfERcf4Md3za
KhirAoGBAMATt4LvEhVizVxQyv3Y0AHFkA5BD2a/rb0N5IKA3C3hBdjzhCcpN1CH
9SDc4bC6r2rNVpPsfQmzrd7SBeNfGQt4LlqM+T8K4tG/XBv/qzJepNovaktXc+Kk
Ql9HA1KsWKcIixTRgHsG7XmtW5tETAQgi2n2oz/YbyQcNDQQCnSx
-----END RSA PRIVATE KEY-----
" > /home/kuppe/.ssh/id_rsa
echo "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQDY+EiWONhPeuupD26mtePrFDzel5ewHcLow0FfdCNnTyRdXRJVo8iyDROP5YyNfphmgezsRcv62sXAft4sqKoVw14luX9XPjNWDARsTbPOyhBTsJe6qMm/8nZ78zGbL8EEWVE52l3rx2MWYy67VwBaAP5szVVpmj+7VJ4fCh/1Vp9ORgOxwgzdpkt2qx8Tn5qVkjOwxqpGsANsaXLmfdRo9eXFXO845Ok7bytPqdwJsSoB2tRUH8rwHrVPQsJsXYnTQFKf8mhf21uxhdsnHg4jWEk1My/XI+x/mjR8ksQWcpjumVAFw7flMD1ZYBijo3CR+b2GtV4uKTxjf8bbEcBn kuppe@ec2.amazonaws.com" > /home/kuppe/.ssh/id_rsa.pub
chmod 600 /home/kuppe/.ssh/id_rsa

# fix permission because steps are executed by root
chown -R kuppe:kuppe /home/kuppe
echo "kuppe ALL=(ALL) NOPASSWD: ALL" >> /etc/sudoers

# create user lamport
useradd -m lamport -s /bin/bash -G admin,sudo
mkdir /home/lamport/.ssh
echo "ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAIEAodOzPQlOIq+8ZDb75L0FR6VeMV/B+COXvkXPiwI4kEXkiadiEkynv7GIwVx3AfryvRtG2gYBUDccNuATVmz7HfhxKGlGOCLY4aZw3qIsMTTfe3nlQ0cRbU4q4npDwiPEQW8MUZe9zfBpPUL1eakZkTSpZaAOTLgYqRgOobLpSKk= lamport@SVC-LAPORT-1" > /home/lamport/.ssh/authorized_keys
chown -R lamport:lamport /home/lamport
echo "lamport ALL=(ALL) NOPASSWD: ALL" >> /etc/sudoers

# add x2go ubuntu ppa repository to package manager apt
add-apt-repository ppa:x2go/stable -y

# add cloudera hadoop repository to package manager
wget http://archive.cloudera.com/one-click-install/maverick/cdh3-repository_1.0_all.deb
dpkg -i cdh3-repository_1.0_all.deb

# update package index and install basic packages needed
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get upgrade -y
apt-get --no-install-recommends install openjdk-7-jdk visualvm openjdk-6-jdk juju unzip mc htop sysstat apache2 munin munin-node munin-java-plugins munin-plugins-extra git git-svn sshfs rsync -y

# if UI/X needed
apt-get --no-install-recommends install gnome-core gdm gnome-session-fallback firefox libwebkitgtk-1.0-0 tightvncserver xorg x2goserver x2goserver-xsession -y

# remove overlay scrollbar. it messes with eclipse
apt-get purge overlay-scrollbar liboverlay-scrollbar-0.2-0 liboverlay-scrollbar3-0.2-0 -y

# clear cached packages to save disk space
apt-get clean

# try saving a few bytes
P1=/etc/munin/plugins
P2=/usr/share/munin/plugins
# activate extra munin stats
rm $P1/apache_*
rm $P1/munin_*
rm $P1/http_*
rm $P1/fw_*
# for jmx plugin to work, the vm has to be started with -D properties to listen on port 5400
ln -s $P2/jmx_ $P1/jmx_ClassesLoaded
ln -s $P2/jmx_ $P1/jmx_ClassesLoadedTotal
ln -s $P2/jmx_ $P1/jmx_ClassesUnloaded
ln -s $P2/jmx_ $P1/jmx_CompilationTimeTotal
ln -s $P2/jmx_ $P1/jmx_GCCount
ln -s $P2/jmx_ $P1/jmx_GCTime
ln -s $P2/jmx_ $P1/jmx_CurrentThreadCpuTime
ln -s $P2/jmx_ $P1/jmx_CurrentThreadUserTime
ln -s $P2/jmx_ $P1/jmx_MemoryAllocatedHeap
ln -s $P2/jmx_ $P1/jmx_MemoryAllocatedNonHeap
ln -s $P2/jmx_ $P1/jmx_MemoryEdenPeak
ln -s $P2/jmx_ $P1/jmx_MemoryEdenUsage
ln -s $P2/jmx_ $P1/jmx_MemoryEdenUsagePostGC
ln -s $P2/jmx_ $P1/jmx_MemoryObjectsPending
ln -s $P2/jmx_ $P1/jmx_MemoryPermGenPeak
ln -s $P2/jmx_ $P1/jmx_MemoryPermGenUsage
ln -s $P2/jmx_ $P1/jmx_MemoryPermGenUsagePostGC
ln -s $P2/jmx_ $P1/jmx_MemorySurvivorPeak
ln -s $P2/jmx_ $P1/jmx_MemorySurvivorUsage
ln -s $P2/jmx_ $P1/jmx_MemorySurvivorUsagePostGC
ln -s $P2/jmx_ $P1/jmx_MemoryTenuredGenPeak
ln -s $P2/jmx_ $P1/jmx_MemoryTenuredGenUsage
ln -s $P2/jmx_ $P1/jmx_MemoryTenuredGenUsagePostGC
ln -s $P2/jmx_ $P1/jmx_MemorythresholdPostGCCount
ln -s $P2/jmx_ $P1/jmx_MemorythresholdUsageCount
ln -s $P2/jmx_ $P1/jmx_ProcessorsAvailable
ln -s $P2/jmx_ $P1/jmx_Threads
ln -s $P2/jmx_ $P1/jmx_ThreadsDaemon
ln -s $P2/jmx_ $P1/jmx_ThreadsDeadlocked
ln -s $P2/jmx_ $P1/jmx_ThreadsPeak
ln -s $P2/jmx_ $P1/jmx_ThreadsStartedTotal
ln -s $P2/jmx_ $P1/jmx_Uptime
# restart munin after config changes
service munin-node restart

# allow everybody to see munin stats
echo "RedirectMatch ^/$ /munin
Alias /munin /var/cache/munin/www
<Directory /var/cache/munin/www>
        Order allow,deny
        Allow from all
        Options None
</Directory>
" > /etc/munin/apache.conf
service apache2 restart

# backup rrdtool data
echo "MAILTO=root
*/5 * * * *     root ps axu|grep java|grep -v grep >> /var/lib/munin/ps.txt
*/10 * * * *	kuppe rsync -avz -e ssh /var/lib/munin/ kuppe@tla.msr-inria.inria.fr:~/rrdtool/`hostname`
*/10 * * * *	kuppe rsync -avz -e ssh /var/cache/munin/ kuppe@tla.msr-inria.inria.fr:~/rrdtool/`hostname`
*/10 * * * *	kuppe rsync -avz -e ssh /home/kuppe/run.log kuppe@tla.msr-inria.inria.fr:~/rrdtool/`hostname`
" > /etc/cron.d/rrdbackup

wget http://64.34.161.181/download/3.5.0/Linux/FE/nxserver_3.5.0-9_amd64.deb
wget http://64.34.161.181/download/3.5.0/Linux/nxnode_3.5.0-7_amd64.deb
wget http://64.34.161.181/download/3.5.0/Linux/nxclient_3.5.0-7_amd64.deb
dpkg -i nxclient_3.5.0-7_amd64.deb
dpkg -i nxnode_3.5.0-7_amd64.deb
dpkg -i nxserver_3.5.0-9_amd64.deb

# add maven and ant to the path
echo "export MAVEN_HOME=/opt/apache-maven/
export ANT_HOME=/opt/apache-ant
export PATH=$PATH:/opt/apache-maven/bin:/opt/apache-ant/bin/
" > /etc/profile.d/java.sh

mkdir -p /mnt/kuppe
chown kuppe:kuppe /mnt/kuppe

cd /home/kuppe
echo "#!/bin/bash
#
# setup kuppe's development environment
#

# add tla.msr-inria.inria.fr known host key to .ssh/known_hosts
echo \"|1|NhbrD14HejMNWnHwOahQhtrBHMc=|7peaar3B1D7AF+Yja+Il98HDIEk= ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAymaqVw6MX0zpVms76QnTO4jTVMzH9Z0/tKGNfh0LZIkAA6QnXMgCIxo+j7N5zBRIwggh9KuE2UKpL5Q17dQ/ue5rNjfglHU6sZfNjEDcL679BqQISr+PzcVH065e7gpVjfyj6E9we2XLuXSAUSU3yzGyLrneRfKXU7W3GNfGaFszmP6n4QyLaUPBFyMdstaynG4naIxTTZ+VpuaDb5lKpjWqBrnWbzh+/El5wU+DFPnKXAnrQemOZNIVGt15QHoFZoKbaNNP+n+rF6uzxjHrHZJnnyK1xp6lkiSm0WEw7WZGBiCywUDefv+P9CpT4bklWGI5uTgI0m/iJlH5ZU5r3Q==
|1|9aOYC/DulqHTbwArybtfVdbGskA=|ogpjhptZMjmTR9w1mu3/lGRSeQ8= ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAymaqVw6MX0zpVms76QnTO4jTVMzH9Z0/tKGNfh0LZIkAA6QnXMgCIxo+j7N5zBRIwggh9KuE2UKpL5Q17dQ/ue5rNjfglHU6sZfNjEDcL679BqQISr+PzcVH065e7gpVjfyj6E9we2XLuXSAUSU3yzGyLrneRfKXU7W3GNfGaFszmP6n4QyLaUPBFyMdstaynG4naIxTTZ+VpuaDb5lKpjWqBrnWbzh+/El5wU+DFPnKXAnrQemOZNIVGt15QHoFZoKbaNNP+n+rF6uzxjHrHZJnnyK1xp6lkiSm0WEw7WZGBiCywUDefv+P9CpT4bklWGI5uTgI0m/iJlH5ZU5r3Q==
\" > ~/.ssh/known_hosts

# clone git repo for eclipse to pick it up easily
mkdir -p ~/git
/usr/bin/git clone ssh://kuppe@tla.msr-inria.inria.fr/home/kuppe/tla.git ~/git/tla
/usr/bin/git clone git://github.com/lemmy/jmx2munin.git ~/git/jmx2munin
# fix git credentials so that we can commit successfully
git config --global user.email \"tlaplus.net@lemmster.de\"
git config --global user.name \"Markus Alexander Kuppe\"

# build tla with maven
#/opt/apache-maven-3.0.4/bin/mvn -f /home/kuppe/git/tla/pom.xml install -Dmaven.test.skip=true
export JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64
cd ~/git/tla/tlatools/
/opt/apache-ant-1.8.3/bin/ant -f customBuild.xml dist-mixed-zip -Dtest.skip=true

#
# build jmx2munin
#
cd ~/git/jmx2munin
/opt/apache-maven-3.0.4/bin/mvn install
# add jar and script to munin
sudo cp target/jmx2munin-1.0.jar /usr/share/munin/jmx2munin.jar
sudo cp contrib/jmx2munin.sh /usr/share/munin/plugins
sudo chmod +x /usr/share/munin/plugins/jmx2munin.sh
# try saving a few bytes
P1=/etc/munin/plugins
P2=/usr/share/munin/plugins
# activate DiskFPSet0 stats
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::filecnt
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::tblcnt
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::indexcnt
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::disklookupcnt
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::diskwritecnt
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::diskhitcnt
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::diskseekcnt
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::memhitcnt
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::growdiskmark
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::checkpointmark
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::bucketcapacity
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::tblcapacity
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::overallcapacity
# activate ModelChecker stats
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::distinctstatesgenerated
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::progress
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::distinctstatesgeneratedperminute
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::statequeuesize
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::statesgenerated
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::statesgeneratedperminute
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::workercount

sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-0::waitedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-0::blockedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-1::waitedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-1::blockedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-2::waitedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-2::blockedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-3::waitedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-3::blockedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-4::waitedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-4::blockedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-5::waitedtime
sudo ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-5::blockedtime
# restart munin to make the above change take effect
sudo service munin-node restart

# launch tlc model checker on amazon performance spec
cd ~/git/tla/general/performance

## start non distributed TLC
#screen -h 99999 /usr/bin/java -Xmx60000m -Xdebug -Xrunjdwp:transport=dt_socket,server=y,suspend=n,address=1044 -Dcom.sun.management.jmxremote -Dcom.sun.management.jmxremote.port=5400 -Dcom.sun.management.jmxremote.ssl=false -Dcom.sun.management.jmxremote.authenticate=false -cp ~/git/tla/tlatools/dist/tla2tools.jar tlc2.TLC -checkpoint 3 -fpbits 0 -fp 0 -workers 6 -fpmem 0.8 MC > /home/kuppe/run.log 2>&1

## start distributed tlc with distributed fp sets
## fpset
#screen -h 99999 /usr/bin/java -Xmx60000m -Xdebug -Xrunjdwp:transport=dt_socket,server=y,suspend=n,address=1044 -Dcom.sun.management.jmxremote -Dcom.sun.management.jmxremote.port=5400 -Dcom.sun.management.jmxremote.ssl=false -Dcom.sun.management.jmxremote.authenticate=false -Djava.rmi.server.hostname=`ifconfig eth0 | awk '/inet addr/ {split ($2,A,":"); print A[2]}'` -cp /mnt/kuppe/git/tla/tlatools/dist/tla2tools.jar tlc2.tool.fp.FPSet /mnt/kuppe/fpset > /home/kuppe/runFPSet.log 2>&1

## server
#screen -h 99999 /usr/bin/java -Xmx60000m -Xdebug -Xrunjdwp:transport=dt_socket,server=y,suspend=n,address=1044 -Dcom.sun.management.jmxremote -Dcom.sun.management.jmxremote.port=5400 -Dcom.sun.management.jmxremote.ssl=false -Dcom.sun.management.jmxremote.authenticate=false -Dfp_server=10.13.18.141,10.78.14.132,10.79.65.177,10.218.5.227 -Djava.rmi.server.hostname=`ifconfig eth0 | awk '/inet addr/ {split ($2,A,":"); print A[2]}'` -cp /mnt/kuppe/git/tla/tlatools/dist/tla2tools.jar tlc2.tool.distributed.TLCServer -fpbits 0 -fp 0 -fpmem 0.8 /mnt/kuppe/git/tla/general/performance/MC > /home/kuppe/run.log 2>&1

## worker
#screen -h 99999 /usr/bin/java -Xmx5000m -Djava.rmi.server.hostname=`ifconfig eth0 | awk '/inet addr/ {split ($2,A,":"); print A[2]}'` -cp /mnt/kuppe/git/tla/tlatools/dist/tla2tools.jar tlc2.tool.distributed.TLCWorker 10.218.65.156

" > /home/kuppe/provisionKuppe.sh

chown -R kuppe:kuppe /home/kuppe/
chmod +x /home/kuppe/provisionKuppe.sh
chmod 666 $(tty) 
sudo -u kuppe /home/kuppe/provisionKuppe.sh > /home/kuppe/provisionKuppe.log 2>&1

