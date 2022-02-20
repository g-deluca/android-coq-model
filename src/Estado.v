(* En este archivo se incluye la representación del sistema de seguridad de
 * Android y la definición de las propiedades que debe cumplir
 * para ser considerado válido *)
Require Import DefBasicas.
Require Import EqTheorems.
Require Import Maps.
Require Export List.


Section Estado.

(* Parte estática del estado del sistema *)
Record Environment := env {
                            (* Para cada aplicación instalada por el usuario, retorna su manifiesto *)
                            manifest: mapping idApp Manifest;
                            (* Para cada aplicación instalada por el usuario, retorna el certificado con el que fue firmada *)
                            cert: mapping idApp Cert;
                            (* Para cada aplicación instalada por el usuario, retorna la lista de permisos que ella define *)
                            defPerms: mapping idApp (list Perm);
                            (* Reúne la lista de aplicaciones preinstaldas de fábrica *)
                            systemImage: list SysImgApp
                           }.

(* Parte dinámica del estado del sistema *)
Record State := st { 
                    (* La lista de aplicaciones instaladas por el usuario *)
                     apps: list idApp;
                     (* Las aplicaciones que ya fueron ejecutadas alguna vez *)
                     (* NOTE: alreadyVerified \subset apps podría ser un invariante nuevo *)
                     alreadyVerified: list idApp;
                    (* Para cada aplicación instalada, retorna la lista de grupos de permisos para los cuales 
                     * la aplicación posee algùn permiso otorgado *)
                     grantedPermGroups : mapping idApp (list idGrp);
                    (* Para cada aplicación instalada, retorna la lista de permisos a ella individualmente otorgados *)
                     perms: mapping idApp (list Perm);
                     (* Mapa que indica de qué componente es una instancia cada módulo en ejecución *)
                     running: mapping iCmp Cmp;
                     (* Mapa que indica a qué recursos tiene qué tipo de derecho permanentemente otorgados cada aplicación *)
                     delPPerms: mapping (idApp * CProvider * uri) PType;
                     (* Mapa que indica a qué recursos tiene qué tipo de derecho temporalmente otorgados cada módulo en ejecución *)
                     delTPerms: mapping (iCmp * CProvider * uri) PType;
                     (* Mapa que indica, dado un recurso de una aplicación, qué valor posee *)
                     resCont: mapping (idApp * res) Val;
                    (* La lista de intents que han sido enviados, junto con su remitente *)
                     sentIntents: list (iCmp*Intent) 
                    }.

(* Estado del sistema *)
Record System := sys {
                       (* Conformado por una parte estática *)
                       state: State;
                       (* y una dinámica *)
                       environment: Environment 
                     }.

End Estado.



Section EstadoValido.

(* La aplicación a forma parte del sistema *)
Definition isAppInstalled (a:idApp) (s:System) : Prop :=
    (* si fue instalada por el usuario *)
    In a (apps (state s)) \/
    (* o estaba preinstalada de fábrica *)
    (exists sysapp:SysImgApp,
    In sysapp (systemImage (environment s)) /\
    idSI sysapp = a).

(* Predicado para verificar si un componente pertence a una aplicación instalada *)
Definition inApp (c:Cmp)(a:idApp)(s:System) : Prop := 
exists (m:Manifest),
(* si existe una aplicación instalada por el usuario *)
(map_apply idApp_eq (manifest (environment s)) a = Value idApp m \/
(* o una preinstalada de fábrica con id a *)
(exists sysapp:SysImgApp,
    In sysapp (systemImage (environment s)) /\
    idSI sysapp = a /\
    manifestSI sysapp=m)
) /\
(* y c pertenece a ella *)
In c (cmp m).

(* Predicado para verificar si el componente que toma como parámetro es un
 * content provider *)
Definition isCProvider (c : Cmp) : Prop :=
match c with
   | cmpCP _ => True
   | _ => False
end.

(* Predicado para verificar si en s existe el recurso apuntado por el URI u en
 * el content provider cp *)
Definition existsRes (cp : CProvider)(u:uri)(s:System) : Prop := 
exists (a:idApp),
inApp (cmpCP cp) a s /\
exists r:res, map_apply uri_eq (map_res cp) u = Value uri r /\
exists v:Val, (map_apply rescontdomeq (resCont (state s))) (a, r) = Value (idApp*res) v.

(* Función que devuelve el id de un componente *)
Definition getCmpId (c:Cmp) : idCmp :=
match c with
   | cmpAct a => idA a
   | cmpSrv s => idS s
   | cmpBR br => idB br
   | cmpCP cp => idC cp
end.

(* Predicado que indica si un permiso es de sistema *)
Parameter isSystemPerm : Perm -> Prop.

(* Predicado para verificar si un permiso fue definido por el usuario en un estado *)
Definition usrDefPerm (p:Perm)(s:System) : Prop := 
(exists (a:idApp) (l: list Perm),
map_apply idApp_eq (defPerms (environment s)) a = Value idApp l /\
In p l) \/ (* Si es definido por una app instalada o *)
(exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ 
In p (defPermsSI sysapp)). (* es definido por una app de sistema *)


(* Predicado que indica si un permiso existe en el sistema *)
Definition permExists (p:Perm)(s:System) : Prop := 
    isSystemPerm p \/ usrDefPerm p s. (* Un permiso existe si es de sistema o lo define alguna app *)

Variable s:System.

(* No hay dos componentes pertenecientes a aplicaciones instaladas que tengan el mismo identificador *)
Definition allCmpDifferent : Prop := 
forall (c1 c2:Cmp)(a1 a2:idApp),
inApp c1 a1 s -> 
inApp c2 a2 s ->
getCmpId c1 = getCmpId c2 -> c1 = c2.

(* Un mismo componente no está asociado a dos aplicaciones distintas *)
Definition notRepeatedCmps : Prop := 
forall (c:Cmp)(a1 a2:idApp),
inApp c a1 s ->
inApp c a2 s ->
a1 = a2.

(* Si un componente está corriendo, éste no puede ser un content provider *)
Definition notCPrunning : Prop := 
forall (ic:iCmp)(c:Cmp),
map_apply iCmp_eq (running (state s)) ic = Value iCmp c ->  
~isCProvider c.

(* Si una delegación sobre un content provider que se realizó a través de intents
 * está vigente, entonces la instancia que recibió dicha delegación está ejecutándose 
 * y el content provider en cuestión está instalado *)
Definition delTmpRun : Prop := 
forall (ic:iCmp)(cp:CProvider)(u:uri)(pt:PType),
map_apply deltpermsdomeq (delTPerms (state s)) (ic, cp, u) = Value (iCmp*CProvider*uri) pt ->
(exists a1: idApp, inApp (cmpCP cp) a1 s) /\
exists c:Cmp, exists a:idApp, inApp c a s /\ 
map_apply iCmp_eq (running (state s)) ic = Value iCmp c.

(* Si una instancia está corriendo, el componente del cual es una
 * instancia, está instalado *)
Definition cmpRunAppIns : Prop := 
forall (ic:iCmp)(c:Cmp), 
map_apply iCmp_eq (running (state s)) ic = Value iCmp c -> 
exists a:idApp, inApp c a s.

(* Todo recurso en el sistema pertenece a una aplicación instalada *)
Definition resContAppInst : Prop := 
forall (a:idApp)(r:res)(v:Val),
map_apply rescontdomeq (resCont (state s)) (a, r) = Value (idApp*res) v -> 
isAppInstalled a s.

(* Dada una aplicación y una lista de permisos, indica si esta lista es la de los permisos
 * definidos por la aplicación *)
Definition defPermsForApp (a:idApp) (l:list Perm) : Prop :=
    map_apply idApp_eq (defPerms (environment s)) a = Value idApp l \/
    (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ defPermsSI sysapp = l /\ idSI sysapp = a).

(* Si dos recursos definidos tienen igual id, son el mismo de la misma aplicación *)
Definition notDupPerm : Prop :=
forall (a a':idApp) (p p':Perm) (l l':list Perm),
defPermsForApp a l ->
defPermsForApp a' l' ->
In p l ->
In p' l' ->
idP p = idP p' ->
(p=p' /\ a=a').

(* Los permisos individualmente otorgados existen *)
Definition grantedPermsExist : Prop:=
    forall (a:idApp) (p:Perm) (l:list Perm), map_apply idApp_eq (perms (state s)) a = Value idApp l -> In p l -> permExists p s.

(* Solo las aplicaciones instalada tienen definido un manifesto, un certificado 
 * y un conjunto de recursos *)
Definition statesConsistency : Prop :=
forall (a:idApp),
(In a (apps (state s)) <->
(exists m:Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m)) /\
(In a (apps (state s)) <->
(exists c:Cert, map_apply idApp_eq (cert (environment s)) a = Value idApp c)) /\
(In a (apps (state s)) <->
(exists l:list Perm, map_apply idApp_eq (defPerms (environment s)) a = Value idApp l)) /\
(In a (apps (state s)) \/ (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a) <->
(exists l:list Perm, (map_apply idApp_eq (perms (state s)) a = Value idApp l))) /\
(In a (apps (state s)) \/ (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a) <->
(exists l:list idGrp, map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp l)).

(* Si una aplicación figura como instalada por el usuario, no existe una aplicación
 * preinstalada con el mismo identificador *)
Definition notDupApp : Prop :=
    forall (a:idApp),
    (In a (apps (state s)) -> ~(exists sysapp:SysImgApp,
    In sysapp (systemImage (environment s)) /\
    idSI sysapp = a)).

(* Todas las aplicaciones instaladas tienen identificadores diferentes *)
Definition notDupSysApp : Prop :=
    forall (s1 s2 : SysImgApp),
    In s1 (systemImage (environment s)) /\
    In s2 (systemImage (environment s)) /\
    idSI s1 = idSI s2 -> s1 = s2.

(* Todos los maps representan funciones parciales *)
Definition allMapsCorrect : Prop :=
    map_correct (manifest (environment s)) /\
    map_correct (cert (environment s)) /\
    map_correct (defPerms (environment s)) /\
    map_correct (grantedPermGroups (state s)) /\
    map_correct (perms (state s)) /\
    map_correct (running (state s)) /\
    map_correct (delPPerms (state s)) /\
    map_correct (delTPerms (state s)) /\
    map_correct (resCont (state s)).

(* No existen intents distintos con igual identificador *)
Definition noDupSentIntents : Prop :=
    forall (i i': Intent) (ic ic' : iCmp),
        In (ic,i) (sentIntents (state s)) ->
        In (ic',i') (sentIntents (state s)) ->
        idI i = idI i' ->
        ic=ic' /\ i=i'.

(* Esta proposición vale si y sólo si el estado es válido *)
Definition validstate  : Prop := allCmpDifferent /\
                                 notRepeatedCmps /\
                                 notCPrunning /\
                                 delTmpRun /\
                                 cmpRunAppIns /\
                                 resContAppInst /\
                                 statesConsistency /\
                                 notDupApp /\
                                 notDupSysApp /\
                                 notDupPerm /\
                                 allMapsCorrect /\
                                 grantedPermsExist /\
                                 noDupSentIntents.

End EstadoValido.
