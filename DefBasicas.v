(* En este archivo se modelan los conceptos del
 * sistema operativo que formarán parte de la formalización *)

Require Import Maps.

Section Permissions.

(* Identificadores de permisos *)
Parameter idPerm : Set.
(* Los identificadores son comparables *)
Axiom idPerm_eq : forall (id1 id2 : idPerm), {id1 = id2} + {id1 <> id2}.

(* Identificadores de grupos de permisos *)
Parameter idGrp : Set.
(* Los identificadores son comparables *)
Axiom idGrp_eq : forall (id1 id2 : idGrp), {id1 = id2} + {id1 <> id2}.

(* Niveles de permisos *)
Inductive permLevel : Set :=
    | dangerous
    | normal
    | signature
    | signatureOrSys.

(* Permisos *)
Record Perm : Set := perm { idP: idPerm;
                            maybeGrp: option idGrp;
                            pl: permLevel }.


End Permissions.


Section Components.

(* Identificador de un componente *)
Parameter idCmp : Set.
(* Los identificadores son comparables *)
Axiom idCmp_eq : forall (id1 id2 : idCmp), {id1 = id2} + {id1 <> id2}.

(* Representa el tipo de los identificadores de recursos *)
Parameter uri : Set.
(* Los identificadores son comparables *)
Axiom uri_eq : forall (id1 id2 : uri), {id1 = id2} + {id1 <> id2}.

(* Identificador de recursos de un CProvider *)
Parameter res: Set.
(* Los identificadores son comparables *)
Axiom res_eq : forall (id1 id2 : res), {id1 = id2} + {id1 <> id2}.

(* Tipo de archivo de cada componente para un Intent o Intent Filter *)
Parameter mimeType: Set.
(* Deben ser comparables *)
Axiom mimeType_eq : forall (id1 id2 : mimeType), {id1 = id2} + {id1 <> id2}.

(* Tipo de datos al que refiere el Intent o Intent Filter *)
Inductive dataType : Set :=
    | content
    | file
    | other.

(* Campo data de un Intent o Intent Filter *)
Record Data : Set := dt { path: option uri;
                          mime: option mimeType;
                          type: dataType }.

(* Categoría de cada componente para un Intent o Intent Filter *)
Parameter Category : Set.
(* Deben ser comparables *)
Axiom Category_eq : forall (id1 id2 : Category), {id1 = id2} + {id1 <> id2}.

(* Acciones de cada componente para un Intent o Intent Filter *)
Inductive intentAction : Set :=
    | activityAction
    | serviceAction
    | broadcastAction.

(* Filtros de intent que puede recibir un componente *)
Record intentFilter : Set := iFilter { actFilter: list intentAction;
                                      dataFilter: list Data;
                                      catFilter: list Category}.

(* Tipos de componentes *)
(* Actividad *)
Record Activity : Set := activity { idA: idCmp;
                                    expA: option bool;
                                    cmpEA: option Perm;
                                    intFilterA: list intentFilter }.

(* Servicio *)
Record Service : Set := service { idS: idCmp;
                                  expS: option bool;
                                  cmpES: option Perm;
                                  intFilterS: list intentFilter }.

(* Broadcast Receiver *)
Record BroadReceiver : Set := broadreceiver { idB: idCmp;
                                              expB: option bool;
                                              cmpEB: option Perm;
                                              intFilterB: list intentFilter}.

(* Content Provider *)
Record CProvider : Set := cprovider { idC: idCmp; 
                                      map_res : mapping uri res;
                                      expC: option bool;
                                      cmpEC: option Perm;
                                      readE: option Perm;
                                      writeE: option Perm;
                                      grantU: bool;
                                      uriP: list uri }.

(* Componentes genéricos *)
Inductive Cmp : Set :=
    | cmpAct : Activity -> Cmp
    | cmpSrv : Service -> Cmp
    | cmpCP : CProvider -> Cmp
    | cmpBR : BroadReceiver -> Cmp.


End Components.


Section RunningComponents.

(* Identificador de una instancia en ejecución de un componente *)
Parameter iCmp : Set.
(* Los identificadores son comparables *)
Axiom iCmp_eq : forall (ic1 ic2 : iCmp), {ic1 = ic2} + {ic1 <> ic2}.

End RunningComponents.


Section Applications.

(* Identificador de una aplicación *)
Parameter idApp : Set.
(* Los identificadores son comparables *)
Axiom idApp_eq : forall (id1 id2 : idApp), {id1 = id2} + {id1 <> id2}.

(* Certificado de una aplicación *)
Parameter Cert: Set.
(* Deben ser comparables *)
Axiom Cert_eq : forall (id1 id2 : Cert), {id1 = id2} + {id1 <> id2}.

(* Manifiesto de una aplicación *)
Record Manifest : Set := mf {  cmp: list Cmp;
                               minSdk: option nat;
                               targetSdk: option nat;
                               use: list idPerm;
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

(* Identificador de un Intent. *)
Parameter idInt : Set.
(* Los identificadores son comparables *)
Axiom idInt_eq : forall (id1 id2 : idInt), {id1 = id2} + {id1 <> id2}.

(* Datos Extra para un Intent *)
Parameter Extra : Set.
(* Deben ser comparables *)
Axiom Extra_eq : forall (id1 id2 : Extra), {id1 = id2} + {id1 <> id2}.

(* Datos Flag para un Intent *)
Parameter Flag : Set.
(* Deben ser comparables *)
Axiom Flag_eq : forall (id1 id2 : Flag), {id1 = id2} + {id1 <> id2}.

(* Tipos de Intents *)
Inductive intentType : Set :=
    | intActivity
    | intService
    | intBroadcast.

(* Intent *)
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

(* Tipo de operación que puede hacerse sobre un recurso *)
Inductive PType :=
    | Read
    | Write
    | Both.

(* Tipo genérico para los valores *)
Parameter Val : Set.

(* Llamadas a APIs del sistema *)
Parameter SACall : Set.

(* TODO: Preguntar cómo representar esto. Sabemos el número del sdk a partir del
cual no podría correrse, pero no sé si conviene dejarlo como parámetro o no *)
Parameter vulnerableSdk : nat.

End Misc.

