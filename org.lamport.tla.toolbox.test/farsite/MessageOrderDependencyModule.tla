---- MODULE MessageOrderDependencyModule ----
(*`^\addcontentsline{toc}{section}{MessageOrderDependencyModule}^'*)

EXTENDS CommonMessageModule
(* ********** Record Definitions ******************************************************************************************* *)

(*Defn*)FileHandles==[fileID:FileID,handle:Handle]

(*Defn*)FileHandle(fileID,handle)==[fileID|->fileID,handle|->handle]

(* ********** OpenFile Fields ********************************************************************************************** *)

(*Defn*)FileSingletonFieldsPeekedByOpenFileOperationMessage(msg)==
  UNION
  {
  {MakeFileDelDispField(msg.fileID)},
  {MakeFileModeField(msg.fileID,ModeOpposite(mode),BBSelf):mode \in msg.modes},
  {MakeFileModeField(msg.fileID,ModeOpposite(mode),BBOther):
    mode \in msg.modes
  },
  {MakeFileOpenHandleField(msg.fileID,BBSelf)},
  {MakeFileBonaFideField(msg.fileID)},
  {MakeFileModeField(msg.fileID,mode,BBSelf):mode \in msg.modes},
  {MakeFileAccessField(msg.fileID,access):
    access \in ModeSetToAccessSet(msg.modes)
  }
  }

(*Defn*)FileSingletonFieldsPokedByOpenFileOperationMessage(msg)==
  UNION
  {
  IF msg.firstHandle THEN{MakeFileOpenHandleField(msg.fileID,BBSelf)}ELSE{},
  {MakeFileModeField(msg.fileID,mode,BBSelf):mode \in msg.firstModes}
  }

(* ********** CleanupFile Fields ******************************************************************************************* *)

(*Defn*)FileSingletonFieldsPeekedByCleanupFileOperationMessage(msg)==
  UNION
  {
  {MakeFileOpenHandleField(msg.fileID,BBSelf)},
  {MakeFileBonaFideField(msg.fileID)},
  {MakeFileModeField(msg.fileID,mode,BBSelf):mode \in msg.modes}
  }

(*Defn*)FileSingletonFieldsPokedByCleanupFileOperationMessage(msg)==
  {MakeFileModeField(msg.fileID,mode,BBSelf):mode \in msg.lastModes}

(* ********** CloseFile Fields ********************************************************************************************* *)

(*Defn*)FileSingletonFieldsPeekedByCloseFileOperationMessage(msg)==
  UNION
  {
  {MakeFileOpenHandleField(msg.fileID,BBSelf)},
  {MakeFileBonaFideField(msg.fileID)},
  {MakeFileAccessField(msg.fileID,access):access \in msg.accesses},
  IF msg.lastHandle
  THEN
    IF msg.unlinkPreclusion=UPDelDispFalse
    THEN
      {MakeFileDelDispField(msg.fileID)}
    ELSE IF msg.unlinkPreclusion=UPOtherHandleOpen
    THEN
      {MakeFileOpenHandleField(msg.fileID,BBOther)}
    ELSE
      {}
  ELSE
    {}
  }

(*Defn*)FileSingletonFieldsPokedByCloseFileOperationMessage(msg)==
  IF msg.lastHandle THEN{MakeFileOpenHandleField(msg.fileID,BBSelf)}ELSE{}

(* ********** CloseAndUnlinkFile Fields ************************************************************************************ *)

(*Defn*)FileSingletonFieldsPeekedByCloseAndUnlinkFileOperationMessage(msg)==
  UNION
  {
  AllPeekableUnwarrantiedFileSingletonFields(msg.childFile),
  {MakeFileChildField(msg.parentFile,msg.label)}
  }

(*Defn*)FileSingletonFieldsPokedByCloseAndUnlinkFileOperationMessage(msg)==
  UNION
  {
  AllPokeableUnwarrantiedFileSingletonFields(msg.childFile),
  {MakeFileChildField(msg.parentFile,msg.label)}
  }

(* ********** WriteFile Fields ********************************************************************************************* *)

(*Defn*)FileSingletonFieldsPeekedByWriteFileOperationMessage(msg)==
  UNION
  {
  {MakeFileOpenHandleField(msg.fileID,BBSelf)},
  {MakeFileAccessField(msg.fileID,ATWritable)}
  }

(*Defn*)FileSingletonFieldsPokedByWriteFileOperationMessage(msg)==
  {MakeFileContentField(msg.fileID)}

(* ********** CreateFile Fields ******************************************************************************************** *)

(*Defn*)FileSingletonFieldsPeekedByCreateFileOperationMessage(msg)==
  UNION
  {
  AllPeekableUnwarrantiedFileSingletonFields(msg.fileID),
  {MakeFileChildField(msg.parentFile,msg.label)},
  {MakeFileDelDispField(msg.parentFile)}
  }

(*Defn*)FileSingletonFieldsPokedByCreateFileOperationMessage(msg)==
  UNION
  {
  AllPokeableUnwarrantiedFileSingletonFields(msg.fileID),
  {MakeFileChildField(msg.parentFile,msg.label)}
  }

(* ********** DeleteFile Fields ******************************************************************************************** *)

(*Defn*)FileSingletonFieldsPeekedByDeleteFileOperationMessage(msg)==
  UNION
  {
  {MakeFileOpenHandleField(msg.fileID,BBSelf)},
  {MakeFileBonaFideField(msg.fileID)},
  {MakeFileModeField(msg.fileID,MTAccessDelete,BBSelf)},
  {MakeFileChildField(msg.fileID,label):label \in Label}
  }

(*Defn*)FileSingletonFieldsPokedByDeleteFileOperationMessage(msg)==
  {MakeFileDelDispField(msg.fileID)}

(* ********** MoveFile Fields ********************************************************************************************** *)

(*Defn*)FileSingletonFieldsPeekedByMoveFileOperationMessage(msg)==
  UNION
  {
  {MakeFileOpenHandleField(msg.childFile,BBSelf)},
  {MakeFileBonaFideField(msg.childFile)},
  {MakeFileParentField(msg.childFile)},
  {MakeFileChildField(msg.srcParentFile,msg.srcLabel)},
  {MakeFileChildField(msg.destParentFile,msg.destLabel)},
  {MakeFileDelDispField(msg.destParentFile)},
  {MakeFilePathField(msg.destParentFile)}
  }

(*Defn*)FileSingletonFieldsPokedByMoveFileOperationMessage(msg)==
  UNION
  {
  {MakeFileParentField(msg.childFile)},
  {MakeFileChildField(msg.srcParentFile,msg.srcLabel)},
  {MakeFileChildField(msg.destParentFile,msg.destLabel)}
  }

(* ********** Operation Message Fields ************************************************************************************* *)

(*Defn*)FileSingletonFieldsPeekedByOperationMessage(msg)==
  IF msg \in OpenFileOperationMessage
  THEN
    FileSingletonFieldsPeekedByOpenFileOperationMessage(msg)
  ELSE IF msg \in CleanupFileOperationMessage
  THEN
    FileSingletonFieldsPeekedByCleanupFileOperationMessage(msg)
  ELSE IF msg \in CloseFileOperationMessage
  THEN
    FileSingletonFieldsPeekedByCloseFileOperationMessage(msg)
  ELSE IF msg \in CloseAndUnlinkFileOperationMessage
  THEN
    FileSingletonFieldsPeekedByCloseAndUnlinkFileOperationMessage(msg)
  ELSE IF msg \in WriteFileOperationMessage
  THEN
    FileSingletonFieldsPeekedByWriteFileOperationMessage(msg)
  ELSE IF msg \in CreateFileOperationMessage
  THEN
    FileSingletonFieldsPeekedByCreateFileOperationMessage(msg)
  ELSE IF msg \in DeleteFileOperationMessage
  THEN
    FileSingletonFieldsPeekedByDeleteFileOperationMessage(msg)
  ELSE IF msg \in MoveFileOperationMessage
  THEN
    FileSingletonFieldsPeekedByMoveFileOperationMessage(msg)
  ELSE
    {}

(*Defn*)FileSingletonFieldsPokedByOperationMessage(msg)==
  IF msg \in OpenFileOperationMessage
  THEN
    FileSingletonFieldsPokedByOpenFileOperationMessage(msg)
  ELSE IF msg \in CleanupFileOperationMessage
  THEN
    FileSingletonFieldsPokedByCleanupFileOperationMessage(msg)
  ELSE IF msg \in CloseFileOperationMessage
  THEN
    FileSingletonFieldsPokedByCloseFileOperationMessage(msg)
  ELSE IF msg \in CloseAndUnlinkFileOperationMessage
  THEN
    FileSingletonFieldsPokedByCloseAndUnlinkFileOperationMessage(msg)
  ELSE IF msg \in WriteFileOperationMessage
  THEN
    FileSingletonFieldsPokedByWriteFileOperationMessage(msg)
  ELSE IF msg \in CreateFileOperationMessage
  THEN
    FileSingletonFieldsPokedByCreateFileOperationMessage(msg)
  ELSE IF msg \in DeleteFileOperationMessage
  THEN
    FileSingletonFieldsPokedByDeleteFileOperationMessage(msg)
  ELSE IF msg \in MoveFileOperationMessage
  THEN
    FileSingletonFieldsPokedByMoveFileOperationMessage(msg)
  ELSE
    {}

(*Defn*)FileSingletonFieldsPeekedOrPokedByOperationMessage(msg)==
  FileSingletonFieldsPeekedByOperationMessage(msg)\union
  FileSingletonFieldsPokedByOperationMessage(msg)

(* ********** Operation Message Handle ************************************************************************************ *)

(*Defn*)FileHandlesPeekedByOperationMessage(msg)==
  IF msg \in CleanupFileOperationMessage
  THEN
    {FileHandle(msg.fileID,msg.handle)}
  ELSE IF msg \in CloseFileOperationMessage
  THEN
    {FileHandle(msg.fileID,msg.handle)}
  ELSE IF msg \in CloseAndUnlinkFileOperationMessage
  THEN
    {FileHandle(msg.childFile,msg.handle)}
  ELSE IF msg \in WriteFileOperationMessage
  THEN
    {FileHandle(msg.fileID,msg.handle)}
  ELSE IF msg \in DeleteFileOperationMessage
  THEN
    {FileHandle(msg.fileID,msg.handle)}
  ELSE IF msg \in MoveFileOperationMessage
  THEN
    {FileHandle(msg.childFile,msg.childHandle)}
  ELSE
    {}

(*Defn*)FileHandlesPokedByOperationMessage(msg)==
  IF msg \in OpenFileOperationMessage
  THEN
    {FileHandle(msg.fileID,msg.handle)}
  ELSE IF msg \in CleanupFileOperationMessage
  THEN
    {FileHandle(msg.fileID,msg.handle)}
  ELSE IF msg \in CloseFileOperationMessage
  THEN
    {FileHandle(msg.fileID,msg.handle)}
  ELSE IF msg \in CloseAndUnlinkFileOperationMessage
  THEN
    {FileHandle(msg.childFile,msg.handle)}
  ELSE IF msg \in CreateFileOperationMessage
  THEN
    {FileHandle(msg.fileID,msg.handle)}
  ELSE
    {}

(*Defn*)FileHandlesPeekedOrPokedByOperationMessage(msg)==
  FileHandlesPeekedByOperationMessage(msg)\union
  FileHandlesPokedByOperationMessage(msg)

(* ********** Lease-Release Message Fields ********************************************************************************* *)

(*Defn*)FileSingletonFieldsPokedByLeaseReleaseMessage(msg)==
  FileFieldToFileSingletonFieldSet(msg.fileField)

(* ********** Client Consistency Message Fields and Handle **************************************************************** *)

(*Defn*)FileSingletonFieldsPokedByClientConsistencyMessage(msg)==
  IF msg \in OperationMessage
  THEN
    FileSingletonFieldsPokedByOperationMessage(msg)
  ELSE IF msg \in LeaseReleaseMessage
  THEN
    FileSingletonFieldsPokedByLeaseReleaseMessage(msg)
  ELSE
    {}

(*Defn*)FileSingletonFieldsPeekedOrPokedByClientConsistencyMessage(msg)==
  IF msg \in OperationMessage
  THEN
    FileSingletonFieldsPeekedOrPokedByOperationMessage(msg)
  ELSE IF msg \in LeaseReleaseMessage
  THEN
    FileSingletonFieldsPokedByLeaseReleaseMessage(msg)
  ELSE
    {}

(*Defn*)FileHandlesPokedByClientConsistencyMessage(msg)==
  IF msg \in OperationMessage
  THEN
    FileHandlesPokedByOperationMessage(msg)
  ELSE
    {}

(*Defn*)FileHandlesPeekedOrPokedByClientConsistencyMessage(msg)==
  IF msg \in OperationMessage
  THEN
    FileHandlesPeekedOrPokedByOperationMessage(msg)
  ELSE
    {}

(* ********** Putting it all together ************************************************************************************** *)

(*Defn*)MessagesAreForwardDependent(msg1,msg2)==
  \/ FileSingletonFieldsPokedByClientConsistencyMessage(msg1)\intersect
     FileSingletonFieldsPeekedOrPokedByClientConsistencyMessage(msg2)
     #
     {}
  \/ FileHandlesPokedByClientConsistencyMessage(msg1)\intersect
     FileHandlesPeekedOrPokedByClientConsistencyMessage(msg2)
     #
     {}

(*Defn*)MessagesAreOrderDependent(msg1,msg2)==
  \/ MessagesAreForwardDependent(msg1,msg2)
  \/ MessagesAreForwardDependent(msg2,msg1)
====
