---- MODULE CertificateModule ----
(*`^\addcontentsline{toc}{section}{CertificateModule}^'*)

EXTENDS FileFieldModule,FiniteSets
(* ********** Server-to-Client Lease-Grant Certificate ******************************************************************** *)

(*Defn*)CTSingletonLeaseGrant=="CTSingletonLeaseGrant"

(*Defn*)SingletonLeaseGrantCertificates==
  [
    type:{CTSingletonLeaseGrant},
    fileField:FileField,
    rw:PReadOrWrite,
    value:FileValueType,
    expiration:ClosedTime
  ]

(*Defn*)LeaseGrantCertificates==UNION{SingletonLeaseGrantCertificates}

(* ********** FileID-Ownership Deed Certificate ***************************************************************************** *)

(* I don't think deeds ever need to be passed around in certificates:

<Definition>CTDeed == "CTDeed"</Definition>
<Definition>
	DeedCertificates ==
	  [	type : { CTDeed },
		deed : Deed
	  ]
</Definition>

 *)

(* ********** Certificate ************************************************************************************************* *)

(*Defn*)Certificate==UNION{LeaseGrantCertificates}

ASSUME Certificate \subseteq Blob
====
