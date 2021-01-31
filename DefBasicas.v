(* In this file we model the concepts of the OS that will be the core of our formalization *)

Require Import Maps.

Section Permissions.

(* Permission identifier *)
Parameter idPerm : Set.
Axiom idPerm_eq : forall (id1 id2 : idPerm), {id1 = id2} + {id1 <> id2}.

(* Permission group identifier *)
Parameter idGrp : Set.
Axiom idGrp_eq : forall (id1 id2 : idGrp), {id1 = id2} + {id1 <> id2}.

(* Permission levels *)
Inductive permLevel : Set :=
    | dangerous
    | normal
    | signature
    | signatureOrSys.

(* Permission definition *)
Record Perm : Set := perm { idP: idPerm;
                            maybeGrp: option idGrp;
                            pl: permLevel }.


End Permissions.


Section Components.

(* Application's component identifier *)
Parameter idCmp : Set.
Axiom idCmp_eq : forall (id1 id2 : idCmp), {id1 = id2} + {id1 <> id2}.

(* This represents the type of the uris identifiers (from the context providers) *)
Parameter uri : Set.
Axiom uri_eq : forall (id1 id2 : uri), {id1 = id2} + {id1 <> id2}.

(* A resource from a content provider *)
Parameter res: Set.
Axiom res_eq : forall (id1 id2 : res), {id1 = id2} + {id1 <> id2}.

(* Parameter that represents the available mime-types. Used by Intent and Intent Filter *)
Parameter mimeType: Set.
Axiom mimeType_eq : forall (id1 id2 : mimeType), {id1 = id2} + {id1 <> id2}.

(* Kind of data referred by an Intent *)
Inductive dataType : Set :=
    | content
    | file
    | other.

(* Data field of an Intent or an Intent Filter *)
Record Data : Set := dt { path: option uri;
                          mime: option mimeType;
                          type: dataType }.

(* Category of a component. Used by Intent o Intent Filter *)
Parameter Category : Set.
Axiom Category_eq : forall (id1 id2 : Category), {id1 = id2} + {id1 <> id2}.

(* Kind of actions available *)
Inductive intentAction : Set :=
    | activityAction
    | serviceAction
    | broadcastAction.

(* Definition of an Intent Filter *)
Record intentFilter : Set := iFilter { actFilter: list intentAction;
                                      dataFilter: list Data;
                                      catFilter: list Category}.

(* Component's definition: Activities, Services, Broadcast Receivers and Content Providers *)
Record Activity : Set := activity { idA: idCmp;
                                    expA: option bool;
                                    cmpEA: option Perm;
                                    intFilterA: list intentFilter }.

Record Service : Set := service { idS: idCmp;
                                  expS: option bool;
                                  cmpES: option Perm;
                                  intFilterS: list intentFilter }.

Record BroadReceiver : Set := broadreceiver { idB: idCmp;
                                              expB: option bool;
                                              cmpEB: option Perm;
                                              intFilterB: list intentFilter}.

Record CProvider : Set := cprovider { idC: idCmp; 
                                      map_res : mapping uri res;
                                      expC: option bool;
                                      cmpEC: option Perm;
                                      readE: option Perm;
                                      writeE: option Perm;
                                      grantU: bool;
                                      uriP: list uri }.

Inductive Cmp : Set :=
    | cmpAct : Activity -> Cmp
    | cmpSrv : Service -> Cmp
    | cmpCP : CProvider -> Cmp
    | cmpBR : BroadReceiver -> Cmp.


End Components.


Section RunningComponents.

(* Identifier of an instance of a component *)
Parameter iCmp : Set.
Axiom iCmp_eq : forall (ic1 ic2 : iCmp), {ic1 = ic2} + {ic1 <> ic2}.

End RunningComponents.


Section Applications.

(* Application's identifiers *)
Parameter idApp : Set.
Axiom idApp_eq : forall (id1 id2 : idApp), {id1 = id2} + {id1 <> id2}.

(* Certificate of an app *)
Parameter Cert: Set.
Axiom Cert_eq : forall (id1 id2 : Cert), {id1 = id2} + {id1 <> id2}.

(* Manifest of an app  *)
Record Manifest : Set := mf {  cmp: list Cmp;
                               minSdk: option nat;
                               targetSdk: option nat;
                               use: list Perm;
                               usrP: list Perm; 
                               appE: option Perm }.

(* Aplicaciones instaladas en la imagen del sistema *)
Record SysImgApp : Set := siapp { idSI: idApp;
                                  certSI: Cert;
                                  manifestSI: Manifest;
                                  defPermsSI : list Perm;
                                  appResSI: list res }.

End Applications.


Section Intents.

(* Intent identifier *)
Parameter idInt : Set.
Axiom idInt_eq : forall (id1 id2 : idInt), {id1 = id2} + {id1 <> id2}.

(* Intent's extra data *)
Parameter Extra : Set.
Axiom Extra_eq : forall (id1 id2 : Extra), {id1 = id2} + {id1 <> id2}.

(* Intent's flags *)
Parameter Flag : Set.
Axiom Flag_eq : forall (id1 id2 : Flag), {id1 = id2} + {id1 <> id2}.

(* Kinds of Intents *)
Inductive intentType : Set :=
    | intActivity
    | intService
    | intBroadcast.

Record Intent : Set := intent { idI: idInt;
                                cmpName: option idCmp;
                                intType: intentType;
                                action: option intentAction;
                                data: Data;
                                category: list Category;
                                extra: option Extra;
                                flags: option Flag;
                                brperm: option Perm }.


End Intents.


Section Misc.

(* Available operations over a resource *)
Inductive PType :=
    | Read
    | Write
    | Both.

(* Generic value type *)
Parameter Val : Set.

(* Calls to the system API *)
Parameter SACall : Set.

(* SDK's older than this one are considered old and Android 10 prompts user's to verify the permission
this app obtained at installation time *)
Definition vulnerableSdk : nat := 22.

End Misc.

