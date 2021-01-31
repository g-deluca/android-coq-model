(* In this file we define our representation of an Android state (from the permission model
perspective) and we define the properties that we consider it has to satisfy to be a valid state *)
Require Import DefBasicas.
Require Import EqTheorems.
Require Import Maps.
Require Export List.


Section Estado.

(* Static part of the system *)
Record Environment := env {
                            (* For each app installed by the user, it returns its manifest *)
                            manifest: mapping idApp Manifest;
                            (* For each app installed by the user, it returns the certificate that was used to sign it*)
                            cert: mapping idApp Cert;
                            (* For each app installed by the user, it returns the list of permissions it defines *)
                            defPerms: mapping idApp (list Perm);
                            (* Pre-installed apps *)
                            systemImage: list SysImgApp
                           }.

(* Dynamic part of the system *)
Record State := st { 
                    (* A list of the applications installed by the user *)
                     apps: list idApp;
                     (* A list of the old apps that have already been verified by the user *)
                     alreadyVerified: list idApp;
                     (* For each installed app, it returns a list of the permission groups that it has*)
                     grantedPermGroups : mapping idApp (list idGrp);
                     (* For each installed app, it returns a list of the permission that it has*)
                     perms: mapping idApp (list Perm);
                     (* Mapping between components and instances of that component *)
                     running: mapping iCmp Cmp;
                     (* Mapping the indicates the resources with permanent permissions that each application has *)
                     delPPerms: mapping (idApp * CProvider * uri) PType;
                     (* Mapping the indicates the resources with temporary permissions that each application has *)
                     delTPerms: mapping (iCmp * CProvider * uri) PType;
                     (* Mapping that indicates the value of an app's resource *)
                     resCont: mapping (idApp * res) Val;
                    (* A list of already sent intents with its sender *)
                     sentIntents: list (iCmp*Intent) 
                    }.

(* The complete state of the system*)
Record System := sys {
                       state: State;
                       environment: Environment 
                     }.

End Estado.



Section EstadoValido.

(* The application is part of the system if ...*)
Definition isAppInstalled (a:idApp) (s:System) : Prop :=
    (* if it was installed by the user *)
    In a (apps (state s)) \/
    (* or if it was pre installed in the system *)
    (exists sysapp:SysImgApp,
    In sysapp (systemImage (environment s)) /\
    idSI sysapp = a).

(* A component belongs to an installed app if ...*)
Definition inApp (c:Cmp)(a:idApp)(s:System) : Prop := 
exists (m:Manifest),
(* that component is declared in a manifest of an app installed by the user *)
(map_apply idApp_eq (manifest (environment s)) a = Value idApp m \/
(* or it's declared in the manifest of a pre installed app*)
(exists sysapp:SysImgApp,
    In sysapp (systemImage (environment s)) /\
    idSI sysapp = a /\
    manifestSI sysapp=m)
) /\
In c (cmp m).

 (* Returns true if the component is a content provider *)
Definition isCProvider (c : Cmp) : Prop :=
match c with
   | cmpCP _ => True
   | _ => False
end.

 (* Predicate that verifies if a resource exists in some state of the system *)
Definition existsRes (cp : CProvider)(u:uri)(s:System) : Prop := 
exists (a:idApp),
inApp (cmpCP cp) a s /\
exists r:res, map_apply uri_eq (map_res cp) u = Value uri r /\
exists v:Val, (map_apply rescontdomeq (resCont (state s))) (a, r) = Value (idApp*res) v.

Definition getCmpId (c:Cmp) : idCmp :=
match c with
   | cmpAct a => idA a
   | cmpSrv s => idS s
   | cmpBR br => idB br
   | cmpCP cp => idC cp
end.

(* Parameter used to recognize the permissions declared by the system *)
Parameter isSystemPerm : Perm -> Prop.

(* Predicate used to check if a permission was declared by some app *)
Definition usrDefPerm (p:Perm)(s:System) : Prop := 
(exists (a:idApp) (l: list Perm),
map_apply idApp_eq (defPerms (environment s)) a = Value idApp l /\
In p l) \/ (* The app that defines it can be user installed*)
(exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ 
In p (defPermsSI sysapp)). (* or pre installed *)


(* We consider that a permission exists if it was defined by the system or by some application*)
Definition permExists (p:Perm)(s:System) : Prop := 
    isSystemPerm p \/ usrDefPerm p s.

Variable s:System.

(* Two components from different apps can't have the same identifier *)
Definition allCmpDifferent : Prop := 
forall (c1 c2:Cmp)(a1 a2:idApp),
inApp c1 a1 s -> 
inApp c2 a2 s ->
getCmpId c1 = getCmpId c2 -> c1 = c2.

(* One component cannot be associated to more than one application *)
Definition notRepeatedCmps : Prop := 
forall (c:Cmp)(a1 a2:idApp),
inApp c a1 s ->
inApp c a2 s ->
a1 = a2.

(* If a component is running, it can't be a Contet Provider *)
Definition notCPrunning : Prop := 
forall (ic:iCmp)(c:Cmp),
map_apply iCmp_eq (running (state s)) ic = Value iCmp c ->  
~isCProvider c.

 (* If a delegation over a content provider that was done via Intents is currently valid, then the
 instance that received that permission is running and the content provider is available *)
Definition delTmpRun : Prop := 
forall (ic:iCmp)(cp:CProvider)(u:uri)(pt:PType),
map_apply deltpermsdomeq (delTPerms (state s)) (ic, cp, u) = Value (iCmp*CProvider*uri) pt ->
(exists a1: idApp, inApp (cmpCP cp) a1 s) /\
exists c:Cmp, exists a:idApp, inApp c a s /\ 
map_apply iCmp_eq (running (state s)) ic = Value iCmp c.

(* Every instance of a component belongs to an installed app *)
Definition cmpRunAppIns : Prop := 
forall (ic:iCmp)(c:Cmp), 
map_apply iCmp_eq (running (state s)) ic = Value iCmp c -> 
exists a:idApp, inApp c a s.

(* Every resource in the system belongs to an installed app *)
Definition resContAppInst : Prop := 
forall (a:idApp)(r:res)(v:Val),
map_apply rescontdomeq (resCont (state s)) (a, r) = Value (idApp*res) v -> 
isAppInstalled a s.

(* Given an app and a permission list, this predicate indicates if this is list of permission is the
one defined by that app *)
Definition defPermsForApp (a:idApp) (l:list Perm) : Prop :=
    map_apply idApp_eq (defPerms (environment s)) a = Value idApp l \/
    (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ defPermsSI sysapp = l /\ idSI sysapp = a).

(* There are no duplicated permissions *)
Definition notDupPerm : Prop :=
forall (a a':idApp) (p p':Perm) (l l':list Perm),
defPermsForApp a l ->
defPermsForApp a' l' ->
In p l ->
In p' l' ->
idP p = idP p' ->
(p=p' /\ a=a').

(* Every permission that has been granted to an app, exist.*)
Definition grantedPermsExist : Prop:=
    forall (a:idApp) (p:Perm) (l:list Perm), map_apply idApp_eq (perms (state s)) a = Value idApp l -> In p l -> permExists p s.

 (* Only installed apps have a manifest, a certificate and a set of resources *)
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

(* If an application was installed by the user, it cannot have the same identifier than a pre installed app *)
Definition notDupApp : Prop :=
    forall (a:idApp),
    (In a (apps (state s)) -> ~(exists sysapp:SysImgApp,
    In sysapp (systemImage (environment s)) /\
    idSI sysapp = a)).

(* Pre installed applications' indentifiers are unique *)
Definition notDupSysApp : Prop :=
    forall (s1 s2 : SysImgApp),
    In s1 (systemImage (environment s)) /\
    In s2 (systemImage (environment s)) /\
    idSI s1 = idSI s2 -> s1 = s2.

(* Every map is a partial function (they are well defined) *)
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

(* If two intents have the same id, they are exactly the same intent *)
Definition noDupSentIntents : Prop :=
    forall (i i': Intent) (ic ic' : iCmp),
        In (ic,i) (sentIntents (state s)) ->
        In (ic',i') (sentIntents (state s)) ->
        idI i = idI i' ->
        ic=ic' /\ i=i'.

(* Valid state definition*)
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
