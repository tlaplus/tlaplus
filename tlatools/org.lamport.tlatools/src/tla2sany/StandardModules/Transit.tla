-------------------------------- MODULE Transit --------------------------------

LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

TransitSerialize(absoluteFilename, value) ==
  (**************************************************************************)
  (* Serializes a tuple of values to the given file as (plain) TRANSIT.     *)
  (* Records will be serialized as a TRANSIT objects, and tuples as arrays. *)
  (**************************************************************************)
  TRUE

TransitDeserialize(absoluteFilename) ==
  (****************************************************************************)
  (* Deserializes TRANSIT values from the given file. TRANSIT objects will be *)
  (* deserialized to records, and arrays will be deserialized to tuples.      *)
  (****************************************************************************)
  CHOOSE val : TRUE

ndTransitSerialize(absoluteFilename, value) ==
  (***************************************************************************)
  (* Serializes a tuple of values to the given file as newline delimited     *)
  (* TRANSIT. Records will be serialized as a TRANSIT objects, and tuples as *)
  (* arrays.                                                                 *)
  (***************************************************************************)
  TRUE

ndTransitDeserialize(absoluteFilename) ==
  (***************************************************************************)
  (* Deserializes TRANSIT values from the given file. TRANSIT values must be *)
  (* separated by newlines. TRANSIT objects will be deserialized to records, *)
  (* and arrays will be deserialized to tuples.                              *)
  (***************************************************************************)
  CHOOSE val : TRUE

=============================================================================
