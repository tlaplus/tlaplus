---- MODULE CertifierModule ----
(*`^\addcontentsline{toc}{section}{CertifierModule}^'*)

EXTENDS PhysicalComponentsModule
(* ********** Definitions ************************************************************************************************** *)

(*Defn*)HostCertificateSetsToSignType==[Host->BlobSet]

(*Defn*)HostSignedCertificateSetsType==[Host->BlobSet]

(*Defn*)HostCertificateSetsToSignInit==[host \in Host|->{}]

(*Defn*)HostSignedCertificateSetsInit==[host \in Host|->{}]

VARIABLE HostCertificateSetsToSign

VARIABLE HostSignedCertificateSets

(* ********** Predicates *************************************************************************************************** *)

(*Defn*)CertifierInitialized==
  /\ HostCertificateSetsToSign=HostCertificateSetsToSignInit
  /\ HostSignedCertificateSets=HostSignedCertificateSetsInit

(* ********** Actions ****************************************************************************************************** *)

(*Defn*)UpdateSignedCertificates==
  \E hostCertificateSetsToSign \in HostCertificateSetsToSignType:
     /\ (HostCertificateSetsToSign')=hostCertificateSetsToSign
     /\ (HostSignedCertificateSets')=
        [host \in Host|->
          HostSignedCertificateSets[host]\union
          ( hostCertificateSetsToSign[host]\intersect Blob)
        ]
====
