This folder contains an HTML as well as an XML dump of the old Bugzilla
database which used to be available at bugzilla.tlaplus.net.

All places in the TLA+ source code that linked to bugzilla.tlaplus.net
have been converted to link to (local) the dump file instead for
historical reasons.


The bzipped bugzilla.sql file is a MySQL database dump. As such, it can
be used if someone ever wants to revive bugzilla.tlaplus.net (The domain
"tlaplus.net" is owned by Simon Zambrowski).