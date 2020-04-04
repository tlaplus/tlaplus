---- MODULE FileFieldModule ----
(*`^\addcontentsline{toc}{section}{FileFieldModule}^'*)

EXTENDS FiniteSets,FileModule
(* ********** FileField Record Definitions ********************************************************************************* *)

(*Defn*)FContent=="FContent"
(*Defn*)FDelDisp=="FDelDisp"
(*Defn*)FParent=="FParent"
(*Defn*)FChildren=="FChildren"
(*Defn*)FOpenHandle=="FOpenHandle"
(*Defn*)FBonaFide=="FBonaFide"
(*Defn*)FModes=="FModes"
(*Defn*)FAccesses=="FAccesses"
(*Defn*)FPath=="FPath"
(*Defn*)FInfiniteChildren=="FInfiniteChildren"
(*Defn*)FileFieldType==
  {
  FContent,
  FDelDisp,
  FParent,
  FChildren,
  FOpenHandle,
  FBonaFide,
  FModes,
  FAccesses,
  FPath,
  FInfiniteChildren
  }

(*Defn*)FSharedValueFields=={FContent,FDelDisp,FParent}

(*Defn*)FileContentField==[field:{FContent},fileID:FileID]
(*Defn*)MakeFileContentField(i_fileID)==[field|->FContent]
(*Defn*)FileDelDispField==[field:{FDelDisp},fileID:FileID]
(*Defn*)MakeFileDelDispField(i_fileID)==[field|->FDelDisp]
(*Defn*)FileParentField==[field:{FParent},fileID:FileID]
(*Defn*)MakeFileParentField(i_fileID)==[field|->FParent]

(*Defn*)FileChildField==[field:{FChildren},fileID:FileID,label:Label]
(*Defn*)MakeFileChildField(i_fileID,i_label)==
  [field|->FChildren,label|->i_label]

(*Defn*)FileBonaFideField==[field:{FBonaFide},fileID:FileID]
(*Defn*)MakeFileBonaFideField(i_fileID)==[field|->FBonaFide]

(*Defn*)FileOpenHandleField==
  [field:{FOpenHandle},fileID:FileID,so:BBSelfOrOther]
(*Defn*)FileOpenHandleField_isSelfOrOther(this)==this.so
(*Defn*)MakeFileOpenHandleField(i_fileID,i_so)==[field|->FOpenHandle]

(*Defn*)FileModeField==
  [field:{FModes},fileID:FileID,so:BBSelfOrOther,mode:Mode]
(*Defn*)FileModeField_isSelfOrOther(this)==this.so
(*Defn*)MakeFileModeField(i_fileID,i_mode,i_so)==
  [field|->FModes,mode|->i_mode]

(*Defn*)FileBlackBoxField==UNION{FileOpenHandleField,FileModeField}
(*Defn*)PartitionedValueField==UNION{FileBonaFideField,FileBlackBoxField}
(*Defn*)PartitionedValueField_isSelfOrOther(this)==
  IF this \in FileBonaFideField
  THEN
    BBSelf
  ELSE IF this \in FileOpenHandleField
  THEN
    this.so
  ELSE
    this.so

(*Defn*)FileAccessField==[field:{FAccesses},fileID:FileID,access:Access]
(*Defn*)MakeFileAccessField(i_fileID,i_access)==
  [field|->FAccesses,access|->i_access]
(*Defn*)FilePathField==[field:{FPath},fileID:FileID]
(*Defn*)MakeFilePathField(i_fileID)==[field|->FPath]
(*Defn*)FileSingletonField==
  UNION
  {
  FileContentField,
  FileDelDispField,
  FileParentField,
  FileChildField,
  PartitionedValueField,
  FileAccessField,
  FilePathField
  }

(*Defn*)FileInfiniteChildField==
  [field:{FInfiniteChildren},fileID:FileID,excludedLabels:LabelSet]
(*Defn*)MakeFileInfiniteChildField(i_fileID,i_excludedLabels)==
  [field|->FInfiniteChildren,excludedLabels|->i_excludedLabels]
(*Defn*)FileField==UNION{FileSingletonField,FileInfiniteChildField}

(*Defn*)FileFieldSet==SUBSET FileField

(*Defn*)FileSharedValueFields==
  UNION{FileContentField,FileDelDispField,FileParentField}

(*Defn*)MakeFileSharedValueField(fileID,field)==
  IF field=FContent
  THEN
    MakeFileContentField(fileID)
  ELSE IF field=FDelDisp
  THEN
    MakeFileDelDispField(fileID)
  ELSE IF field=FParent
  THEN
    MakeFileParentField(fileID)
  ELSE
    0

(*Defn*)MakeFileSharedValueFields(fileID)==
  {
  MakeFileContentField(fileID),
  MakeFileDelDispField(fileID),
  MakeFileParentField(fileID)
  }

(* **********                                        *********************************************************************** *)

(*Defn*)AllPeekableUnwarrantiedFileSingletonFields(fileID)==
  UNION
  {
  {MakeFileContentField(fileID)},
  {MakeFileDelDispField(fileID)},
  {MakeFileParentField(fileID)},
  {MakeFileChildField(fileID,label):label \in Label},
  {MakeFileOpenHandleField(fileID,so):so \in BBSelfOrOther},
  {MakeFileBonaFideField(fileID)},
  {MakeFileModeField(fileID,mode,so):mode \in Mode,so \in BBSelfOrOther},
  {MakeFileAccessField(fileID,access):access \in Access}
  }

(*Defn*)AllPokeableUnwarrantiedFileSingletonFields(fileID)==
  UNION
  {
  {MakeFileContentField(fileID)},
  {MakeFileDelDispField(fileID)},
  {MakeFileParentField(fileID)},
  {MakeFileChildField(fileID,label):label \in Label},
  {MakeFileOpenHandleField(fileID,BBSelf)},
  {MakeFileModeField(fileID,mode,BBSelf):mode \in Mode}
  }

(* ********** Singleton / Infinite Conversion Operators ******************************************************************** *)

(*Defn*)FileFieldToFileSingletonFieldSet(fileField)==
  IF fileField \in FileSingletonField
  THEN
    {fileField}
  ELSE
    {MakeFileChildField(fileField.fileID,label):
      label \in Label \ fileField.excludedLabels
    }

(* Convert a finite set of FileField to a possibly infinite set of FileSingletonField *)

(*Defn*)FileFieldSetToFileSingletonFieldSet(fileFields)==
  UNION{FileFieldToFileSingletonFieldSet(fileField):fileField \in fileFields}

(* Convert a possibly infinite set of FileSingletonField to a finite set of FileField *)

(*Defn*)FileSingletonFieldSetToFileFieldSet(fileSingletonFields)==
  CHOOSE fileFields \in FileFieldSet:
    /\ FileFieldSetToFileSingletonFieldSet(fileFields)=fileSingletonFields
    /\ IsFiniteSet(fileFields)
    /\ ( \A otherFileFields \in FileFieldSet:
            \/ FileFieldSetToFileSingletonFieldSet(otherFileFields)#fileSingletonFields
            \/ (\neg IsFiniteSet(otherFileFields))
            \/ Cardinality(otherFileFields)\geq Cardinality(fileFields))
====
