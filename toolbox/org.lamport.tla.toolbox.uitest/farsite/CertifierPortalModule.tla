---- MODULE CertifierPortalModule ----
(*`^\addcontentsline{toc}{section}{CertifierPortalModule}^'*)

EXTENDS Stubs
VARIABLE CertificateSetToSign

VARIABLE HostSignedCertificateSets

(* ********** Predicates *************************************************************************************************** *)

(*Defn*)IsCertificateSignedBySignatory(cert,signatory)==
  cert \in HostSignedCertificateSets[signatory]

(* ********** Partial Actions ********************************************************************************************** *)

(*Defn*)SignCertificateSet(certSet)==(CertificateSetToSign')=certSet

(*Defn*)SignCertificate(cert)==SignCertificateSet({cert})

(*Defn*)SignNoCertificate==(CertificateSetToSign')={}
====
