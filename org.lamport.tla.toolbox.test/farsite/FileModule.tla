---- MODULE FileModule ----
(*`^\addcontentsline{toc}{section}{FileModule}^'*)

EXTENDS AbstractComponentsModule,PhysicalComponentsModule,ModeModule
(* ********** Component Definitions **************************************************************************************** *)

(* 
<Enum name="PIndividualOrEveryone">
	<Enum-Value name="PIndividual"/>
	<Enum-Value name="PEveryone"/>
</Enum>
 *)

(*Defn*)PIndividual=="PIndividual"

(*Defn*)PEveryone=="PEveryone"

(*Defn*)PIndividualOrEveryone=={PIndividual,PEveryone}

(* 
<Enum name="PReadOrWrite">
	<Enum-Value name="PRead"/>
	<Enum-Value name="PWrite"/>
</Enum>
 *)

(*Defn*)PRead=="PRead"

(*Defn*)PWrite=="PWrite"

(*Defn*)PReadOrWrite=={PRead,PWrite}

(*Defn*)Parent==[fileID:FileOrNil,label:LabelOrNil]
(*Defn*)MakeParent(i_fileID,i_label)==[fileID|->i_fileID,label|->i_label]

(*Defn*)BBSelf=="BBSelf"
(*Defn*)BBOther=="BBOther"
(*Defn*)BBSelfOrOther=={BBSelf,BBOther}

(*Defn*)BBSelfMap==[Client->HandleSet]

(*  Note: Note that this map data type is identical to the PrivateValue
	map. That's natural: as JD likes to say, a PrivateValue is
	"a half of a half of a BlackBox". But we don't want to use the
	type by name, because the BlackBox.self field would better be
	called a "PublicValue" (since it's value is visible as the "other"
	field on other hosts) and we don't want the name to mislead.
	 *)

(*Defn*)BBOtherMap==[Client->Boolean]

(*Defn*)BlackBox==[self:BBSelfMap,other:BBOtherMap]
(*Defn*)MakeBlackBox(i_self,i_other)==[self|->i_self,other|->i_other]

(*Defn*)PrivateValue==[Client->HandleSet]

(* ********** Special FileValue Types ************************************************************************************* *)

(*Defn*)OpenHandleRecord==
  [handle:Handle,accessRead:Boolean,accessWrite:Boolean]
(*Defn*)MakeOpenHandleRecord(i_handle,i_accessRead,i_accessWrite)==
  [handle|->i_handle,accessRead|->i_accessRead,accessWrite|->i_accessWrite]

(*Defn*)OpenHandleRecordSet==SUBSET OpenHandleRecord

(*Defn*)BonaFideHandleRecord==
  [
    handle:Handle,
    accessDelete:Boolean,
    exclRead:Boolean,
    exclWrite:Boolean,
    exclDelete:Boolean
  ]
(*Defn*)
MakeBonaFideHandleRecord(
  i_handle,i_accessDelete,i_exclRead,i_exclWrite,i_exclDelete)==
  [
  handle|->i_handle,
  accessDelete|->i_accessDelete,
  exclRead|->i_exclRead,
  exclWrite|->i_exclWrite,
  exclDelete|->i_exclDelete
  ]

(*Defn*)BonaFideHandleRecordSet==SUBSET BonaFideHandleRecord

(* ********** FileValue *************************************************************************************************** *)

(*Defn*)FileValueTypeType_Content=="FileValueTypeType_Content"
(*Defn*)FileValueTypeType_Boolean=="FileValueTypeType_Boolean"
(*Defn*)FileValueTypeType_Parent=="FileValueTypeType_Parent"
(*Defn*)FileValueTypeType_FileID=="FileValueTypeType_FileID"
(*Defn*)FileValueTypeType_HandleSet=="FileValueTypeType_HandleSet"
(*Defn*)FileValueTypeType_FileSeq=="FileValueTypeType_FileSeq"
(*Defn*)FileValueTypeType_OpenHandleRecordSet==
  "FileValueTypeType_OpenHandleRecordSet"
(*Defn*)FileValueTypeType_BonaFideHandleRecordSet==
  "FileValueTypeType_BonaFideHandleRecordSet"
(*Defn*)FileValueTypeType_Nil=="FileValueTypeType_Nil"
(*Defn*)FileValueTypeType==
  {
  FileValueTypeType_Content,
  FileValueTypeType_Boolean,
  FileValueTypeType_Parent,
  FileValueTypeType_FileID,
  FileValueTypeType_HandleSet,
  FileValueTypeType_FileSeq,
  FileValueTypeType_OpenHandleRecordSet,
  FileValueTypeType_BonaFideHandleRecordSet,
  FileValueTypeType_Nil
  }

(*Defn*)FileValueTypeContent==Content
(*Defn*)FileValueTypeBoolean==Boolean
(*Defn*)FileValueTypeParent==Parent
(*Defn*)FileValueTypeFileID==FileID
(*Defn*)FileValueTypeHandleSet==HandleSet
(*Defn*)FileValueTypeFileSeq==FileSeq
(*Defn*)FileValueTypeOpenHandleRecordSet==OpenHandleRecordSet
(*Defn*)FileValueTypeBonaFideHandleRecordSet==BonaFideHandleRecordSet
(*Defn*)FileValueTypeNil=={Nil}
(*Defn*)FileValueType==
  UNION
  {
  FileValueTypeContent,
  FileValueTypeBoolean,
  FileValueTypeParent,
  FileValueTypeFileID,
  FileValueTypeHandleSet,
  FileValueTypeFileSeq,
  FileValueTypeOpenHandleRecordSet,
  FileValueTypeBonaFideHandleRecordSet,
  FileValueTypeNil
  }

(*Defn*)ChildMap==[Label->FileOrNil]

(*Defn*)ModeMap==[Mode->BlackBox]

(*Defn*)AccessMap==[Access->PrivateValue]

(*Defn*)FileValue==
  [
    content:Content,
    delDisp:Boolean,
    parent:Parent,
    children:ChildMap,
    openHandle:BlackBox,
    bonaFide:PrivateValue,
    modes:ModeMap,
    accesses:AccessMap,
    path:FileSeq
  ]
(*Defn*)
MakeFileValue(
  i_content,
  i_delDisp,
  i_parent,
  i_children,
  i_openHandle,
  i_bonaFide,
  i_modes,
  i_accesses,
  i_path)==
  [
  content|->i_content,
  delDisp|->i_delDisp,
  parent|->i_parent,
  children|->i_children,
  openHandle|->i_openHandle,
  bonaFide|->i_bonaFide,
  modes|->i_modes,
  accesses|->i_accesses,
  path|->i_path
  ]

(* ********** FileValueTableState *********************************************************************************************** *)

(*Defn*)FileValueTable==[FileID->FileValue]

VARIABLE FileValueTableState

(*Defn*)FileValueTableStateType==FileValueTable

(* ********** Initialization *********************************************************************************************** *)

(*Defn*)FileValueInit==
  CHOOSE fileValue \in FileValue:
    ( \A client \in Client,label \in Label,mode \in Mode,access \in Access:
         /\ fileValue.content=ContentNull
         /\ fileValue.delDisp=Boolean
         /\ fileValue.parent=MakeParent(Nil,Nil)
         /\ fileValue.children[label]=Nil
         /\ fileValue.openHandle.self[client]={}
         /\ fileValue.openHandle.other[client]=FALSE
         /\ fileValue.bodaFide[client]={}
         /\ fileValue.modes[mode].self[client]={}
         /\ fileValue.modes[mode].other[client]=FALSE
         /\ (fileValue.accesses[access])[client]={}
         /\ fileValue.path= <<>>)

(*Defn*)FileValueRootInit==
  [
    [FileValueInit EXCEPT
      !.openHandle=
        [@EXCEPT
          !.self=
            [client \in DOMAIN@|->
              IF client \in Client
              THEN
                LET(*Defn*)AtSymbol001==@[client]IN RootHandle
              ELSE
                @[client]
            ]
        ]
    ]
  EXCEPT
    !.bonaFide=
      [client \in DOMAIN@|->
        IF client \in Client
        THEN
          LET(*Defn*)AtSymbol002==@[client]IN RootHandle
        ELSE
          @[client]
      ]
  ]

(*Defn*)FileValueTableInit==
  [fileID \in FileID|->
    IF fileID=FilesystemRoot THEN FileValueRootInit ELSE FileValueInit
  ]

(* ********** FileID Identifiers ********************************************************************************************* *)

ASSUME FileID=PosIntSeq

ASSUME FilesystemRoot= <<>>

(*Defn*)FileHasBeenConceived(fileID)==
  fileID#FilesystemRoot=>
  Last(fileID)\leq FileValueTableState[AllButLast(fileID)].maxSuffix
====
