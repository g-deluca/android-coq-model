(* En este archivo se implementa una función que muta el sistema frente a acciones
 * respetando la relación exec *)
Require Import ErrorManagement.
Require Import Estado.
Require Import Semantica.
Require Import Maps.
Require Import DefBasicas.
Require Import EqTheorems.
Require Import Operaciones.
Require Import RuntimePermissions.
Require Import MyList.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.PeanoNat.

Section Result.

(* El resultado de ejecutar una acción en un estado es el nuevo estado alcanzado
*  y la respuesta del motor ante la solicitud *)
Record Result : Set := result {
    response : Response;
    system : System
}.
End Result.

Section AuxDefinitions.

(* Filtra de una lista los elementos que sean valores (y no errores) *)
Fixpoint getValues (A B:Set) (l:list (exc B A)) {struct l} : list B := 
    match l with
    | nil => nil
    | Value _ a::rest => a :: getValues A B rest
    | _ :: rest => getValues A B rest
    end.

(* Obtiene todos los componentes del sistema, tanto de aplicaciones instaladas
* como de aplicaciones de fábrica *)
Definition getAllComponents (s:System) : list Cmp :=
    let maybeinstalledManifests := map (map_apply idApp_eq (manifest (environment s))) (apps (state s)) in
    let installedManifests := getValues idApp Manifest maybeinstalledManifests in
    let installedCmps := map cmp installedManifests in
    let sysCmps := map (fun sysapp => cmp (manifestSI sysapp)) (systemImage (environment s)) in
    concat (installedCmps ++ sysCmps).

(* Indica si existe un componente con el mismo id que el de aquel que se recibe
* como parámetro presente en el sistema *)
Definition cmpIdInStateBool (c:Cmp) (s:System) : bool :=
    let allComponents := getAllComponents s in
    let allComponentIds := map getCmpId allComponents in
    existsb (fun cid => If idCmp_eq cid (getCmpId c) then true else false) allComponentIds.

(* Indica si el componente c está presente en el sistema *)
Definition cmpInStateBool (c:Cmp) (s:System) : bool :=
    let allComponents := getAllComponents s in
    existsb (fun c' => If Cmp_eq c' c then true else false) allComponents.

(* Indica si una app está presente en el sistema *)
Definition isAppInstalledBool (a:idApp) (s:System) : bool :=
    let installedAppsIds := apps (state s) in
    let installedAppsIds := installedAppsIds ++ map idSI (systemImage (environment s)) in
    InBool idApp idApp_eq a installedAppsIds.

(* Retorna la lista de permisos definidos por las aplicaciones presentes en el sistema *)
Definition usrDefPerms (s:System) : list Perm :=
    let maybeinstalledDefPerms := map (map_apply idApp_eq (defPerms (environment s))) (apps (state s)) in
    let installeddefPerms := getValues idApp (list Perm) maybeinstalledDefPerms in
    let sysDefPerms := map defPermsSI (systemImage (environment s)) in
    concat (installeddefPerms ++ sysDefPerms).

(* Representa la lista de permisos predefinidos del sistema *)
Parameter systemPerms : list Perm.
(* Asegura la relación entre systemPerms y el predicado isSystemPerm *)
Axiom isSysPermCorrect : forall (p:Perm), isSystemPerm p <-> In p systemPerms.

(* Retorna todos los permisos válidos del sistema *)
Definition getAllPerms (s:System) : list Perm :=
    systemPerms ++ usrDefPerms s.

(* Indica si cierto permiso es de sistema *)
Definition isSystemPermBool (p:Perm) : bool := InBool idPerm idPerm_eq (idP p) (map idP systemPerms).

(* Retorna de un manifiesto los permisos que él define (es decir, los que no son de sistema) *)
Definition nonSystemUsrP (m:Manifest) : list Perm :=
    filter (fun perm => negb (isSystemPermBool perm)) (usrP m).

(* Indica si los permisos que quiere definir una app no fueron ya definidos previamente *)
Definition authPermsBool (m:Manifest)(s:System) : bool := 
    negb (existsb (fun p => (existsb (fun p' => If idPerm_eq (idP p') (idP p) then true else false) (usrDefPerms s))) (nonSystemUsrP m)).

(* Indica si una lista es vacía *)
Definition isNil (A:Set) (l:list A) : bool :=
    match l with
    | nil => true
    | _ => false
    end.

(* Indica si x contiene un valor *)
Definition isSomethingBool (A:Set) (x:option A) : bool :=
    match x with | Some _ => true | _ => false end.

(* Indica si un componente define correctamente sus intentFilters *)
Definition definesIntentFilterCorrectlyBool (cmp:Cmp) : bool :=
    let theFilters :=
        match cmp with
        | cmpAct a => intFilterA a
        | cmpSrv s => intFilterS s
        | cmpCP _ => nil
        | cmpBR br => intFilterB br
        end in                                     
        negb (existsb (fun iFil => (negb (isNil Data (dataFilter iFil) && isNil Category (catFilter iFil)) && (isNil intentAction (actFilter iFil)))) theFilters).

(* Negación de la función anterior *)
Definition definesIntentFilterIncorrectly (cmp:Cmp) : bool :=
    negb (definesIntentFilterCorrectlyBool cmp).

(* Indica si algún componente de la lista que es su parámetro declara incorrectammente algún intentFilter *)
Definition anyDefinesIntentFilterIncorrectly (cmps : list Cmp) : bool :=
    existsb definesIntentFilterIncorrectly cmps.

(* Agrega a un mapa una lista de claves, valores *)
Definition addAll (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (indexAndValues:list (index*values)) (mp:mapping index values) :=
    fold_right (fun pair oldmap => map_add indexeq oldmap (fst pair) (snd pair)) mp indexAndValues.

(* Elimina de un mapa una lista de claves *)
Definition dropAll (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (indexes:list index) (mp:mapping index values) :=
    fold_right (fun i oldmap => map_drop indexeq oldmap i) mp indexes.

(* Agrega al mapa recibido todos los claves valores especificados *)
Definition addNewResCont (app:idApp) (oldResCont:mapping (idApp * res) Val) (lRes :list res) : mapping (idApp * res) Val :=
    addAll (idApp*res) Val rescontdomeq (map (fun r => ((app,r),initVal)) lRes) oldResCont.

(* Retorna una lista de todos los componentes que tienen al menos una instancia en ejecución en el sistema *)
Definition getRunningCmps (s:System) : list Cmp :=
    let keys := map_getKeys (running (state s)) in
    getValues iCmp Cmp (map (map_apply iCmp_eq (running (state s))) keys).

(* Indica si un componente está ejecutándose en el sistema *)
Definition isCmpRunning (c:Cmp) (s:System) : bool :=
    InBool idCmp idCmp_eq (getCmpId c) (map getCmpId (getRunningCmps s)).

(* Indica si algún componente de la app se está ejecutando en ese momento *)
Definition isAnyCmpRunning (app:idApp) (s:System) : bool :=
    match map_apply idApp_eq (manifest (environment s)) app with
    | Error _ _ => false (* No pasa nunca *)
    | Value _ mfst => existsb (fun c => isCmpRunning c s) (cmp mfst)
    end.

(* fst de una tripla *)
Definition fst3 (A B C : Set) (tuple3:(A*B*C)):A :=
    let (a,b) := tuple3 in fst a.

(* snd de una tripla *)
Definition snd3 (A B C : Set) (tuple3:(A*B*C)):B :=
    let (a,b) := tuple3 in snd a.

(* Indica si un componente es un proveedor de contenido *)
Definition isCProviderBool (c : Cmp) : bool :=
    match c with
    | cmpCP _ => true
    | _ => false
    end.

(* Indica si un componente es una actividad *)
Definition isActivityBool (c : Cmp) : bool :=
    match c with
    | cmpAct _ => true
    | _ => false end.

(* Indica si un componente es un servicio *)
Definition isServiceBool (c : Cmp) : bool :=
    match c with
    | cmpSrv _ => true
    | _ => false end.

(* Indica si un componente es un receptor de broadcast *)
Definition isBroadReceiverBool (c : Cmp) : bool :=
    match c with
    | cmpBR _ => true
    | _ => false end.

(* Retorna la actividad si el componente recibido es de actividad. None, si no. *)
Definition maybeGetActivityFromCmp (c : Cmp) : option Activity :=
match c with
   | cmpAct act => Some act
   | _ => None
end.

(* Retorna el receptor de broadcast si el componente recibido es un receptor de broadcast. None, si no. *)
Definition maybeGetBroadReceiverFromCmp (c : Cmp) : option BroadReceiver :=
match c with
   | cmpBR b => Some b
   | _ => None
end.

(* Algún manifiesto por defecto. No se usa nunca, es para tipar *)
Definition defaultManifest : Manifest := mf nil None None nil nil None.
(* Algún id de aplicación por defecto. No se usa nunca, es para tipar *)
Parameter defaultApp : idApp.

(* Algún certificado por defecto. No se usa nunca, es para tipar *)
Parameter defaultCert : Cert.

(* Alguna imagen de sistema por defecto. No se usa nunca, es para tipar *)
Definition defaultSysApp : SysImgApp := siapp defaultApp defaultCert defaultManifest nil nil.

(* Retorna todos los componentes que pertenecen a una app *)
Definition getAllCmps (app:idApp) (s:System) : list Cmp :=
    match map_apply idApp_eq (manifest (environment s)) app with
    | Value _ m => cmp m
    | Error _ _ => cmp (manifestSI (hd defaultSysApp (filter (fun sysapp => If idApp_eq app (idSI sysapp) then true else false) (systemImage (environment s)))))
    end.

(* Retorna todos los proveedores de contenido de una aplicación *)
Definition getCProviders (app:idApp) (s:System) : list Cmp :=
    filter isCProviderBool (getAllCmps app s).

(* Elimina todos los otorgamientos a todos los permisos definidos por la aplicación *)
Definition dropAppPerms (oldstate:System) (app:idApp) : mapping idApp (list Perm) :=
    let defPermsApp := match map_apply idApp_eq (defPerms (environment oldstate)) app with
                    | Value _ l => l
                    | Error _ _ => nil (* nunca pasa *)
                    end in
    let theKeys := map_getKeys (perms (state oldstate)) in
    let theKeyVals := map (fun key => (key,match map_apply idApp_eq (perms (state oldstate)) key with | Value _ l => filter (fun p => negb (InBool Perm Perm_eq p defPermsApp)) l | Error _ _ => nil (*nunca pasa*) end)) theKeys in
            map_drop idApp_eq (addAll idApp (list Perm) idApp_eq theKeyVals (perms (state oldstate))) app.

(* Elimina todas las delegaciones permanentes a todos los proveedores de contenido de la aplicación *)
Definition dropAllPPerms (s:System) (app:idApp) : mapping (idApp * CProvider * uri) PType :=
    let appCProviders := getCProviders app s in
    let oldpperms := delPPerms (state s) in
    let filteredkeys := filter (fun tuple3 => If idApp_eq (fst3 idApp CProvider uri tuple3) app then true else InBool Cmp Cmp_eq (cmpCP (snd3 idApp CProvider uri tuple3)) appCProviders ) (map_getKeys oldpperms) in
        dropAll (idApp * CProvider * uri) PType delppermsdomeq filteredkeys oldpperms.

(* Elimina todas las delegaciones temporales a todos los proveedores de contenido de la aplicación *)
Definition dropAllTPerms (s:System) (app:idApp) : mapping (iCmp * CProvider * uri) PType :=
    let appCProviders := getCProviders app s in
    let oldtperms := delTPerms (state s) in
    let filteredkeys := filter (fun tuple3 => InBool Cmp Cmp_eq (cmpCP (snd3 iCmp CProvider uri tuple3)) appCProviders ) (map_getKeys oldtperms) in
        dropAll (iCmp * CProvider * uri) PType deltpermsdomeq filteredkeys oldtperms.

(* Elimina todos los recursos de la aplicación *)
Definition dropAllRes (resCont : mapping (idApp*res) Val) (app:idApp) : mapping (idApp*res) Val :=
    let filteredkeys := filter (fun pair => If idApp_eq app (fst pair) then true else false) (map_getKeys resCont) in
        dropAll (idApp * res) Val rescontdomeq filteredkeys resCont.

(* Retorna la lista de permisos que la aplicación lista como usados *)
Definition permsInUse (app:idApp) (s:System) : list idPerm :=
    match map_apply idApp_eq (manifest (environment s)) app with
    | Error _ _ => hd nil (map (fun sysapp => use (manifestSI sysapp)) (filter (fun sysapp => If idApp_eq app (idSI sysapp) then true else false) (systemImage (environment s))))
    | Value _ m => use m
    end.

(* Retorna la lista de permisos individualmente otorgados a la aplicación *)
Definition grantedPermsForApp (app:idApp) (s:System) : list Perm :=
    match map_apply idApp_eq (perms (state s)) app with
    | Error _ _ => nil (* Nunca pasa *)
    | Value _ list => list
    end.

(* Retorna una lista de idGrp que indica los grupos que están asociados a permisos
   actualmente otorgados*)
Definition permissionGroupsInUse (app: idApp) (s: System) : list idGrp :=
    let permsForApp := grantedPermsForApp app s in
    let groupedPerms := filter (fun perm => negb (isSomethingBool idGrp (maybeGrp perm))) permsForApp in
    let groups := map (fun perm => match maybeGrp perm with | None => nil | Some g => cons g nil end) groupedPerms in
    concat groups.


(* Agrega un permiso como individualmente otorgado a la aplicación *)
Definition grantPermission (app:idApp) (p:Perm) (oldperms : mapping idApp (list Perm)) : mapping idApp (list Perm) :=
    match map_apply idApp_eq oldperms app with
    | Error _ _ => oldperms (* Nunca pasa *)
    | Value _ list => map_add idApp_eq oldperms app (p::list)
    end.

(* Elimina un permiso de los individualmente otorgados a la aplicación *)
Definition revokePermission (app:idApp) (p:Perm) (oldperms : mapping idApp (list Perm)) : mapping idApp (list Perm) :=
    match map_apply idApp_eq oldperms app with
    | Error _ _ => oldperms (* Nunca pasa *)
    | Value _ list => map_add idApp_eq oldperms app (remove Perm_eq p list)
    end.

(* Agrega un grupo de permisos como otorgado a la aplicación *)
Definition grantPermissionGroup (app:idApp) (g:idGrp) (oldpermGroups : mapping idApp (list idGrp)) : mapping idApp (list idGrp) :=
    match map_apply idApp_eq oldpermGroups app with
    | Error _ _ => oldpermGroups (* Nunca pasa *)
    | Value _ list => map_add idApp_eq oldpermGroups app (g::list)
    end.

(* Elimina un grupo de permisos de los otorgados a la aplicación *)
Definition revokePermissionGroup (app:idApp) (g:idGrp) (oldpermGroups : mapping idApp (list idGrp)) : mapping idApp (list idGrp) :=
    match map_apply idApp_eq oldpermGroups app with
    | Error _ _ => oldpermGroups (* Nunca pasa *)
    | Value _ list => map_add idApp_eq oldpermGroups app (remove idGrp_eq g list)
    end.

Definition getPermsOfGroup (g: idGrp) (app: idApp) (s: System) : list Perm :=
    let allPerms := grantedPermsForApp app s in
    filter (fun perm =>
        match maybeGrp perm with
          | None => false
          | Some g' => if idGrp_eq g g' then true else false
        end) allPerms.

Definition revokeAllPermsOfGroup
    (app: idApp)
    (g: idGrp)
    (s: System) : mapping idApp (list Perm) :=

    let permsToBeRemoved := getPermsOfGroup g app s in
    let oldperms := perms (state s) in
    match map_apply idApp_eq oldperms app with
    | Error _ _ => oldperms (* Nunca pasa *)
    | Value _ list => map_add idApp_eq oldperms app (removeAll Perm_eq permsToBeRemoved list)
    end.

(* Retorna el id de la aplicación a la cual el componente pertenece; junto con su manifiesto *)
Definition getManifestAndAppFromCmp (c:Cmp) (s:System) : (idApp*Manifest) :=
    let maybeinstalledPairs := map (fun a => (a, (map_apply idApp_eq (manifest (environment s)) a ))) (apps (state s)) in
    let maybeinstalledPairs := maybeinstalledPairs ++ map (fun sysapp => (idSI sysapp, Value idApp (manifestSI sysapp))) (systemImage (environment s)) in
    let hisManifests := filter (fun pair => match (snd pair) with | Error _ _ => false | Value _ mfst => InBool idCmp idCmp_eq (getCmpId c) (map getCmpId (cmp mfst)) end) maybeinstalledPairs in
    let theapp := fst (hd (defaultApp, Value idApp defaultManifest) hisManifests) in
    let theMaybeMfst := snd (hd (defaultApp, Value idApp defaultManifest) hisManifests) in
    match theMaybeMfst with
    | Error _ _ => (theapp, defaultManifest)
    | Value _ mfst => (theapp, mfst)
    end.

(* Retorna el manifiesto de la aplicación a la cual el componente pertenece *)
Definition getManifestFromCmp (c:Cmp) (s:System) : Manifest :=
    snd (getManifestAndAppFromCmp c s).

(* Retorna el id de la aplicación a la cual el componente pertenece *)
Definition getAppFromCmp (c:Cmp) (s:System) : idApp :=
    fst (getManifestAndAppFromCmp c s).

(* Retorna la mínima versión de sdk necesaria para ejecutar la aplicación *)
Definition getCmpMinSdkImpl (c : Cmp) (s:System) : option nat :=
    minSdk (getManifestFromCmp c s).

(* Retorna la versión de sdk objetivo para ejecutar la aplicación *)
Definition getCmpTargetSdkImpl (c : Cmp) (s:System) : option nat :=
    targetSdk (getManifestFromCmp c s).

(* Indica si n<=m *)
Function lebnat (n:nat) (m:nat) {struct n} : bool :=
    match n with
    |0 => true
    |S x => match m with
        | 0 => false
        | S y => lebnat x y
        end
    end.

(* Indica si la versión objetivo o la versión mínima de desarrollo son <= 16 *)
Definition getDefaultExpBool (cp: CProvider) (s:System): bool :=
    match getCmpMinSdkImpl (cmpCP cp) s with
    | None => false
    | Some n => match getCmpTargetSdkImpl (cmpCP cp) s with
        | None => false
        | Some m => lebnat n 16 || lebnat m 16
        end
    end.

(* Retorna la lista de permisos definidos por la aplicación *)
Definition getDefPermsForApp (a:idApp) (s:System) : list Perm :=
    match (map_apply idApp_eq (defPerms (environment s)) a) with
    | Value _ l => l
    | Error _ _ => hd nil (map defPermsSI (filter (fun sysapp => If idApp_eq a (idSI sysapp)then true else false) (systemImage (environment s))))
    end.

(* Retorna el certificado con el que fue firmada una aplicación *)
Definition getAppCert (a:idApp) (s:System) : Cert :=
    match (map_apply idApp_eq (cert (environment s)) a) with
    | Value _ c => c
    | Error _ _ => hd defaultCert (map certSI (filter (fun sysapp => If idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s))))
    end.

(* Retorna el certificado con el que fue firmada la aplicación que declara cierto permiso *)
Definition getCertOfDefiner (p:Perm) (s:System) : Cert :=
    let pairs := map (fun a => (a, getDefPermsForApp a s)) (apps (state s) ++ map idSI (systemImage (environment s))) in
    let theonelist := filter (fun pair => InBool Perm Perm_eq p (snd pair)) pairs in
    hd defaultCert (map (fun pair => getAppCert (fst pair) s) theonelist).
    
(* Retorna el manifiesto de una aplicación *)
Definition getManifestForApp (a:idApp) (s:System) : Manifest :=
    match (map_apply idApp_eq (manifest (environment s)) a) with
    | Value _ m => m
    | Error _ _ => hd defaultManifest (map manifestSI (filter (fun sysapp => If idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s))))
    end.

(* Indica si el permiso forma parte de un grupo y este grupo fue otorgado a la aplicación *)
Definition groupIsGranted (a:idApp) (p:Perm) (s:System) : bool :=
    match maybeGrp p with
    | None => false
    | Some grp => match map_apply idApp_eq (grantedPermGroups (state s)) a with
        | Error _ _ => false
        | Value _ grps => InBool idGrp idGrp_eq grp grps
        end
    end.

(* Indica si la aplicación es de sistema *)
Definition isSysImgAppBool (a:idApp) (s:System) : bool :=
    match (filter (fun sysapp => If idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s))) with
    | nil => false
    | _ => true
    end.

(* Indica si la aplicación tiene el permiso p *)
Definition appHasPermissionBool (idapp:idApp) (p:Perm) (s:System) : bool :=
    (* El permiso debe existir *)
    InBool Perm Perm_eq p (getAllPerms s) &&
    (* La aplicación debe estar instalada *)
    isAppInstalledBool idapp s &&
    (* El permiso debe estar individualmente otorgado o *)
    (InBool Perm Perm_eq p (grantedPermsForApp idapp s) ||
    let mfst := getManifestForApp idapp s in
        (* la app lo lista como usado y además *)
        if InBool idPerm idPerm_eq (idP p) (use mfst) then
           let defPerms := getDefPermsForApp idapp s in
                (* El permiso es definido por ella o *)
                if InBool idApp idApp_eq idapp (apps (state s)) && InBool Perm Perm_eq p defPerms then true
                else
                    match pl p with
                    | normal => true (* el permiso es normal o *)
                    | dangerous => false (* encontramos un permiso peligroso que no esta otorgado individualmente *)
                    | signature => if (InBool Perm Perm_eq p (usrDefPerms s) && If Cert_eq (getAppCert idapp s) (getCertOfDefiner p s) then true else false) then true else false (* el permiso es de tipo signature y quien lo define fue firmada con el mismo certificado que la aplicación *)
                    | signatureOrSys => if ((InBool Perm Perm_eq p (usrDefPerms s) && (If Cert_eq (getAppCert idapp s) (getCertOfDefiner p s) then true else false)) || (If Cert_eq (getAppCert idapp s) manufacturerCert then true else false)) then true else false (* el permiso es de tipo signatureOrSys y quien lo define fue firmada con el mismo certificado que la aplicación o la aplicación es del fabricante *)
                    end
        else false).

(* Indica si el componente c tiene los permisos necesarios para efectuar la operación thisE sobre el content provider cp *)
Definition canDoThisBool (c:Cmp) (cp:CProvider)(s:System) (thisE : CProvider -> option Perm) : bool :=
    (* El componente debe estar en el sistema *)
    if negb (cmpInStateBool c s) then false else
    (* también el content provider *)
    if negb (cmpInStateBool (cmpCP cp) s) then false else
    let (a1, m1) := getManifestAndAppFromCmp c s in
    let (a2, m2) := getManifestAndAppFromCmp (cmpCP cp) s in
    let requiredPerm := match thisE cp with
        | Some p => Some p
        | None => match cmpEC cp with
            | Some p => Some p
            | None => appE m2
            end
        end in

    let checkPerm := match requiredPerm with
        | None => true (* Si ningún permiso es necesario, entonces true *)
        | Some p => appHasPermissionBool a1 p s
        end in

    If idApp_eq a1 a2 then true (* Si es la propia app, true *)
    else
    match (expC cp) with
    | Some false => false (* Si el contentprovider no permite acceso externo, false *)
    | Some true => checkPerm (* Si no, si ningún permiso es necesario para el acceso, true. Si lo es, chequear que tenga dicho permiso *)
    | None => if getDefaultExpBool cp s then checkPerm else false (* Si el campo no se especifica y la aplicación es vieja, se asume que permite accesos de terceros. Si es nueva, se asume que no *)
    end.

(* Indica si el componente c tiene los permisos necesarios para leer el content provider cp *)
Definition canReadBool (c:Cmp) (cp:CProvider)(s:System) : bool := canDoThisBool c cp s readE.

(* Indica si el componente c tiene los permisos necesarios para escribir el content provider cp *)
Definition canWriteBool (c:Cmp) (cp:CProvider)(s:System) : bool := canDoThisBool c cp s writeE.

(* Indica si dos tipos de delegaciones son iguales *)
Definition eq_PType (pt pt':PType) : bool :=
    match pt with
    | Both => match pt' with
        | Both => true
        | _ => false
        end
    | Read => match pt' with
        | Read => true
        | _ => false
        end
    | Write => match pt' with
        | Write => true
        | _ => false
        end
    end.

(* Indica si l componente c tiene permisos delegados para realizar la operación pt sobre el
  recurso identificado por u del content provider cp *)
Definition delPermsBool (c:Cmp)(cp:CProvider)(u:uri)(pt:PType)(s:System) : bool :=
    if (negb (cmpInStateBool c s)) then false else
    let a := getAppFromCmp c s in
    let runningAppAndiCmps := map (fun pair=> (item_index pair, getAppFromCmp (item_info pair) s)) (running (state s)) in
    let myRunningiCmps := map (fun pair => fst pair) (filter (fun pair => If idApp_eq a (snd pair) then true else false) runningAppAndiCmps) in
    if existsb (fun icmp => match map_apply deltpermsdomeq (delTPerms (state s)) (icmp, cp, u) with | Error _ _ => false | Value _ Both => true | Value _ pt' => eq_PType pt' pt end) myRunningiCmps then true
    else match map_apply delppermsdomeq (delPPerms (state s)) (a, cp, u) with | Error _ _ => false | Value _ Both => true | Value _ pt' => eq_PType pt' pt end.

(* Indica si existe el recurso apuntado por el URI u en
  el content provider cp *)
Definition existsResBool (cp : CProvider)(u:uri)(s:System) : bool := 
    let allTheComponents:= getAllComponents s in
    if negb (InBool Cmp Cmp_eq (cmpCP cp) allTheComponents) then false else
    let theapp := getAppFromCmp (cmpCP cp) s in
    match map_apply uri_eq (map_res cp) u with
    | Error _ _ => false
    | Value _ r => match map_apply rescontdomeq (resCont (state s)) (theapp, r) with
        | Error _ _ => false
        | _ => true
        end
    end.

(* Sobreescribe el valor del recurso u de cp con el valor val *)
Definition writeResCont (icmp:iCmp) (cp:CProvider) (u:uri) (val:Val) (s:System) : mapping (idApp * res) Val  :=
    let oldResCont := resCont (state s) in
    let a := getAppFromCmp (cmpCP cp) s in
    match map_apply uri_eq (map_res cp) u with
    | Error _ _ => oldResCont (* Nunca pasa *)
    | Value _ r => map_add rescontdomeq oldResCont (a, r) val
    end.

(* Indica si dos tipos de intent son iguales *)
Definition intTypeEqBool (t t' : intentType) : bool :=
    match t with
    | intActivity => match t' with | intActivity => true | _ => false end
    | intService => match t' with | intService => true | _ => false end
    | intBroadcast => match t' with | intBroadcast => true | _ => false end
    end.

(* Indica si ic es el identificador de una instancia en ejecución *)
Definition isiCmpRunningBool (ic:iCmp) (s:System) : bool :=
    InBool iCmp iCmp_eq ic (map_getKeys (running (state s))).

(* Filtra los elementos que contienen valor, retornando su contenido *)
Function getSomes (A B:Set) (f:A-> option B) (l:list A) {struct l} : list B :=
    match l with
    | nil => nil
    | x::rest => match f x with
        | Some y => y :: getSomes A B f rest
        | None => getSomes A B f rest
        end
    end.
    
(* Indica si la aplicación puede recibir intents con
  la acción especificada *)
Definition actionTestBool (i:Intent)(iFil:intentFilter)(s:System): bool :=
    match action i with
    | None => negb (isNil intentAction (actFilter iFil))
    | Some iAct => InBool intentAction intentAction_eq iAct (actFilter iFil)
    end.

(* Indica si la aplicación puede recibir intents con la 
  categoría especificada*)
Definition categoryTestBool (i:Intent)(iFil:intentFilter)(s:System): bool :=
    match category i with
    | nil => true
    | lIntent => negb (existsb (fun c => negb (InBool Category Category_eq c (catFilter iFil))) lIntent)
    end.

(* Indica si dos tipos de dato son iguales *)
Definition eqDataType (dt dt': dataType) : bool :=
    match dt with
    | content => match dt' with | content => true | _ => false end
    | file => match dt' with | file => true | _ => false end
    | other => match dt' with | other => true | _ => false end
    end.

(* Indica si la URI del intent es de tipo 'content' o 'file' *)
Definition isContentOrFileBool (i:Intent) : bool :=
eqDataType (type (data i)) content || eqDataType (type (data i)) file.

(* Si el intent no especifica URI ni tipo MIME, el filtro tampoco debe hacerlo *)
Definition notUriAndNotMimeBool (i:Intent)(iFil:intentFilter)(s:System) : bool :=
    negb (isSomethingBool uri (path (data i))) &&
    negb (isSomethingBool mimeType (mime (data i))) &&
    isNil Data (dataFilter iFil).

(*Si el intent especifica URI pero no tipo MIME,
  el filtro debe especificar la misma URI y no especificar ningún tipo MIME*)
Definition uriAndNotMimeBool (i:Intent)(iFil:intentFilter)(s:System) : bool :=
    isSomethingBool uri (path (data i)) &&
    negb (isSomethingBool mimeType (mime (data i))) &&
    InBool Data Data_eq (data i) (dataFilter iFil).

(*Si el intent especifica tipo MIME pero no URI,
  el filtro debe listar el mismo tipo MIME y no especificar ninguna URI*)
Definition notUriAndMimeBool (i:Intent)(iFil:intentFilter)(s:System) : bool :=
    negb (isSomethingBool uri (path (data i))) &&
    isSomethingBool mimeType (mime (data i)) && 
    InBool Data Data_eq (data i) (dataFilter iFil).

(*Si el intent especifica tipo MIME y URI,
  el filtro debe listar el mismo tipo MIME y la misma URI o 
  la URI debe contener un content o file y el filtro no listar ninguna URI*)
Definition uriAndMimeBool (i:Intent)(iFil:intentFilter)(s:System) : bool :=
    let allSomeMimes := getSomes Data mimeType mime (dataFilter iFil) in
    let allPaths := map path (dataFilter iFil) in
    let allSomePaths := getSomes Data uri path (dataFilter iFil) in
    match path (data i) with
    | None => false
    | Some thePath => match mime (data i) with
        | None => false
        | Some theMime =>
            InBool mimeType mimeType_eq theMime allSomeMimes &&
            (InBool uri uri_eq thePath allSomePaths ||
            (isContentOrFileBool i && existsb (fun maybe => negb (isSomethingBool uri maybe)) allPaths)
            )
        end
    end.

(* Indica si se cumple alguna de las cuatro funciones arriba detalladas *)
Definition dataTestBool (i:Intent)(iFil:intentFilter)(s:System): bool :=
notUriAndNotMimeBool i iFil s ||
uriAndNotMimeBool i iFil s ||
notUriAndMimeBool i iFil s ||
uriAndMimeBool i iFil s.

(* Indica si el parámetro es Some true *)
Definition isSomeTrue (maybeB : option bool) : bool :=
    match maybeB with
        | Some true => true
        | _ => false
    end.

(* Indica si el componente puede ser iniciado por una aplicación externa *)
Definition canBeStartedBool (c:Cmp) (s:System): bool :=
 match c with
    | cmpAct a => (isSomeTrue (expA a)) || (negb (isSomethingBool bool (expA a)) && isNil intentFilter (intFilterA a))
    | cmpSrv sr => (isSomeTrue (expS sr)) || (negb (isSomethingBool bool (expS sr)) && isNil intentFilter (intFilterS sr))
    | cmpCP cp => (isSomeTrue (expC cp)) || (negb (isSomethingBool bool (expC cp)) && getDefaultExpBool cp s)
    | cmpBR br => (isSomeTrue (expB br)) || (negb (isSomethingBool bool (expB br)) && isNil intentFilter (intFilterB br))
 end.

(* Indica si el componente c1 tiene los permisos para iniciar al componente c2 mandando un intent explícito *)
Definition canStartBool (c1 c2: Cmp)(s:System) : bool :=
    (* Ambos componentes deben estar en el sistema *)
    if negb(cmpInStateBool c1 s) then false else
    if negb(cmpInStateBool c2 s) then false else
    let (a1,m) := getManifestAndAppFromCmp c1 s in
    let a2 := getAppFromCmp c2 s in
    (* Si pertenecen a la misma aplicación, puede iniciarlo *)
    If idApp_eq a1 a2 then true else
        (* c2 debe permitir ejecución por app externa *)
        canBeStartedBool c2 s &&
        let maybep := match c2 with
            | cmpAct a => match cmpEA a with | None => appE m | x => x end
            | cmpSrv s => match cmpES s with | None => appE m | x => x end
            | cmpCP cp => match cmpEC cp with | None => appE m | x => x end
            | cmpBR br => match cmpEB br with | None => appE m | x => x end
            end in
        match maybep with
            | None => true (* Si no requiere permisos para ser iniciado, true *)
            | Some p => appHasPermissionBool a1 p s (* Si requiere el permiso p, la aplicacioón a la cual c1 pertenece debe conter con él *)
        end.

Definition canRunBool (app: idApp) (s: System) : bool :=
    InBool idApp idApp_eq app (alreadyVerified (state s)) ||
    match targetSdk (getManifestForApp app s) with
    | None => false
    | Some n =>  vulnerableSdk <? n
    end.

(* Retorna los intentFilters de un componente *)
Definition getFilters (c:Cmp) : list intentFilter :=
    match c with
    | cmpAct ac => intFilterA ac
    | cmpSrv s => intFilterS s
    | cmpCP _ => nil
    | cmpBR br => intFilterB br
    end.

(* Retorna el componente al cual está dirigido el intent, si existe. Si no, retorna None *)
Definition maybeIntentForAppCmp (i:Intent)(a:idApp)(ic:iCmp)(s:System) : option Cmp :=
    if negb (isAppInstalledBool a s) then None else
    if negb (InBool (iCmp*Intent) sentintentseq (ic,i) (sentIntents (state s))) then None else
    let allCmpsA := getAllCmps a s in
    match cmpName i with
    | None => None
    | Some idc => match filter (fun installedcomp => If idCmp_eq idc (getCmpId installedcomp) then true else false) allCmpsA with
        | nil => None
        | c :: _ => Some c
        end
    end.

(* Indica si el content provider permite delegar permisos sobre el recurso referido por u *)
Definition canGrantBool (cp:CProvider)(u:uri)(s:System) : bool:=
    let allCmps := getAllComponents s in
    InBool Cmp Cmp_eq (cmpCP cp) allCmps &&
    (InBool uri uri_eq u (uriP cp) ||
        (isNil uri (uriP cp) && grantU cp)).

(* Elimina todas las delegaciones temporales a la instancia ic *)
Definition removeTPerms (icmp:iCmp) (st:State) : mapping (iCmp * CProvider * uri) PType:=
    let oldTPerms := delTPerms st in
    let allKeys := map_getKeys oldTPerms in
    let filteredKeys := filter (fun tuple => If iCmp_eq icmp (fst (fst tuple)) then true else false) allKeys in
        dropAll (iCmp * CProvider * uri) PType deltpermsdomeq filteredKeys oldTPerms.

(* Indica si el componente c' cumple los requisitos para recibir un intent con actiontype intacttype sobre el recurso u de cmp y cmp es un content provider *)
Definition receiveIntentCmpRequirements (c':Cmp) (u:uri) (s:System) (intactype:PType) (cmp:Cmp) : bool :=
    match cmp with
    | cmpCP cp => let thiscanread := canReadBool c' cp s || delPermsBool c' cp u Read s in
                      let thiscanwrite := canWriteBool c' cp s || delPermsBool c' cp u Write s in
                      existsResBool cp u s && canGrantBool cp u s &&
                      match intactype with
                      | Read => thiscanread
                      | Write => thiscanwrite
                      | Both => thiscanread && thiscanwrite
                      end
    | _ => false
    end.

(* Algún id de componente por defecto. No se usa nunca, es para tipar *)
Parameter defaultCmpId : idCmp.
(* Algún id de instancia en ejecución por defecto. No se usa nunca, es para tipar *)
Parameter defaultiCmp : iCmp.

(* Hace al componente con id name destinatario del intent i *)
Definition overrideIntentName (i:Intent) (name:idCmp) : Intent :=
    intent (idI i)
            (Some name)
            (intType i)
            (action i)
            (data i)
            (category i)
            (extra i)
            (flags i)
            (brperm i).

(* Algún proveedor de contenido por defecto. No se usa nunca, es para tipar *)
Definition defaultCProvider : CProvider := cprovider defaultCmpId nil None None None None true nil.

(* Elige un componente factible de recibir el intent que se está resolviendo *)
Definition chooseCmp (pair:iCmp * Intent) (a:idApp) (s:System) :=
    let allCmpsA := getAllCmps a s in
    let allActsA := filter isActivityBool allCmpsA in
    let allServsA := filter isServiceBool allCmpsA in
    let allBroadsA := filter isBroadReceiverBool allCmpsA in
    let ic := fst pair in
    let intt := snd pair in
    let defaultCmp := cmpCP defaultCProvider in
    match map_apply iCmp_eq (running (state s)) ic with
        | Error _ _ => defaultCmp (* nunca pasa *)
        | Value _ c1 => let startableCmps := match intType intt with
                | intActivity => filter (fun c2 => canStartBool c1 c2 s) allActsA (* Si el intent es de actividad, busco entre las actividades *)
                | intService => filter (fun c2 => canStartBool c1 c2 s) allServsA (* Si el intent es de servicio, busco entre los servicios *)
                | intBroadcast  => filter (fun c2 => canStartBool c1 c2 s) allBroadsA (* Si el intent es de broadcast, busco entre los broadcasts *)
                end
                in
                (* y de ellos, retorno alguno que cumpla los tests *)
                let filteredstartableCmps := filter (fun cmp => let iFils := getFilters cmp in existsb (fun iFil => actionTestBool intt iFil s && categoryTestBool intt iFil s && dataTestBool intt iFil s) iFils) startableCmps in
                (hd defaultCmp (filteredstartableCmps))
    end.

(* Retorna el identificador de un componente factible de recibir el intent que se está resolviendo *)
Definition chooseCmpId (pair:iCmp * Intent) (a:idApp) (s:System) :=
    getCmpId (chooseCmp pair a s).

(* Explicita el Intent que se resuelve *)
Definition resolveImplicitToExplicitIntent (i:Intent)(a:idApp)(s:System) : list (iCmp*Intent):=
    let oldSentIntents := sentIntents (state s) in
    let filterFun := fun pair => If idInt_eq (idI i) (idI (snd pair)) then true else false in
    (* se actualizarán los intents cuyo id coincida con el de aquel recibido como parámetro (hay solo uno) *)
    let updateSentIntents := filter filterFun oldSentIntents in 
    (* los otros no se modificarán *)
    let remainingSentIntents := filter (fun pair => negb (filterFun pair)) oldSentIntents in
    let theIcIntent := hd (defaultiCmp, i) updateSentIntents in
    (* se elige un componente factible de recibirlo *)
    let chosenCmpId := chooseCmpId theIcIntent a s in
    (* se sobrescribe el nombre del intent a resolver *)
    let updatedSentIntents := map (fun pair => (fst pair, overrideIntentName (snd pair) chosenCmpId)) updateSentIntents in
    remainingSentIntents ++ updatedSentIntents.

(* Se pone en ejecución una instancia de c con identificador ic *)
Definition performRunCmp (i:Intent)(ic:iCmp)(c:Cmp)(s:System): mapping iCmp Cmp :=
    let oldrunning := running (state s) in
    map_add iCmp_eq oldrunning ic c.

(* Función capaz de otorgar un id de instancia en ejecución que no se encuentre en la lista proveída *)
Parameter iCmpGenerator : list iCmp -> iCmp.
(* Constancia de que efectivamente el generador hace eso *)
Axiom generatorWorksWell : forall usedcmps:list iCmp, ~In (iCmpGenerator usedcmps) usedcmps.

(* Retorna el proveedor de contenido que tiene el recurso apuntado por u *)
Definition getAnyCProviderWithUri (u:uri) (s:System) : CProvider :=
    let allCmps := getAllComponents s in
    let allCProviders := getSomes Cmp CProvider (fun cmp => match cmp with | cmpCP cp => Some cp | _ => None end) allCmps in
    let filteredCPs := filter (fun cp => existsResBool cp u s) allCProviders in
    hd defaultCProvider filteredCPs.

(* Se le otorga el permiso temporal pt sobre el recurso u del proveedor de contenido cp a la instancia ic *)
Definition performGrantTempPerm (pt:PType) (u:uri) (cp:CProvider) (ic:iCmp) (s:System) : mapping (iCmp*CProvider*uri) PType :=
    let oldDelTPerms := delTPerms (state s) in
    map_add deltpermsdomeq oldDelTPerms (ic,cp,u) pt.

(* Se le otorga el permiso permanente pt a la clave idx *)
Definition addDelPPerm (oldPPerms: mapping (idApp * CProvider * uri) PType) (idx:(idApp * CProvider * uri)) (pt:PType) : mapping (idApp * CProvider * uri) PType :=
    map_add delppermsdomeq oldPPerms idx (
        match map_apply delppermsdomeq oldPPerms idx with
        | Value _ pt' => ptplus pt' pt
        | _ => pt
        end).

(* Se revoca los permisos de efectuar pt en el mapa mp sobre el uri u del proveedor de contenido cp *)
Definition removeAllPerms (A:Set) (domeq: forall (id1 id2 : (A*CProvider*uri)), {id1 = id2} + {id1 <> id2}) (mp:mapping (A*CProvider*uri) PType) (cp:CProvider) (u:uri) (pt:PType) : mapping (A*CProvider*uri) PType :=
    let willupdate := filter (fun tuple => If CProvider_eq cp (snd (fst tuple)) then (If uri_eq u (snd tuple) then true else false) else false) (map_getKeys mp) in
    let willdrop := filter (fun tuple => match map_apply domeq mp tuple with | Error _ _ => false | Value _ pt' => negb (isSomethingBool PType (ptminus pt' pt)) end) willupdate in
    let overrideKeys := filter (fun tuple => match map_apply domeq mp tuple with | Error _ _ => false | Value _ pt' => isSomethingBool PType (ptminus pt' pt) end) willupdate in
    let overrideKeyVals := map (fun tuple => (tuple,match map_apply domeq mp tuple with | Error _ _ => Both (*no ocurre*) | Value _ pt' => match ptminus pt' pt with None => Both (*no ocurre*) | Some pt'' => pt'' end end)) overrideKeys in
    dropAll (A*CProvider*uri) PType domeq willdrop (addAll (A*CProvider*uri) PType domeq overrideKeyVals mp).


(* Retorna, dada una llamada al sistema, los permisos necesarios para su ejecución *)
Parameter getMandatoryPerms : SACall -> list Perm.
(* Constancia de que no pueden especificarse necesarios permisos definidos por aplicaciones *)
Axiom mandatoryPermsAllSystem : forall (sac:SACall) (p:Perm), In p (getMandatoryPerms sac) -> isSystemPerm p.
(* Constancia de que se comporta según la especificación *)
Axiom mandatoryPermsCorrect : forall (sac:SACall) (p:Perm) (sysPerm : isSystemPerm p), permSAC p sysPerm sac <-> In p (getMandatoryPerms sac).

End AuxDefinitions.

(* En las siguientes secciones se codifican las pre y post condiciones de las acciones. Ver el archivo Semantica.v para detalles. *)

Section ImplInstall.

Definition install_pre (app:idApp) (m:Manifest) (c:Cert) (lRes : list res) (s:System) : option ErrorCode :=
    if isAppInstalledBool app s then (Some app_already_installed) else
    if (has_duplicates idCmp idCmp_eq (map getCmpId (cmp m))) then (Some duplicated_cmp_id) else
    if (has_duplicates idPerm idPerm_eq (map idP (usrP m))) then (Some duplicated_perm_id) else
    if (existsb (fun c => cmpIdInStateBool c s) (cmp m)) then (Some cmp_already_defined) else
    if (negb (authPermsBool m s)) then (Some perm_already_defined) else
    if (anyDefinesIntentFilterIncorrectly (cmp m)) then (Some faulty_intent_filter) else
    None.

Definition install_post (app:idApp) (m:Manifest) (c:Cert) (lRes : list res) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (app :: (apps oldstate))
            (alreadyVerified oldstate)
            (map_add idApp_eq (grantedPermGroups oldstate) app nil)
            (map_add idApp_eq (perms oldstate) app nil)
            (running oldstate)
            (delPPerms oldstate)
            (delTPerms oldstate)
            (addNewResCont app (resCont oldstate) lRes)
            (sentIntents oldstate)
        )
        (env
            (map_add idApp_eq (manifest oldenv) app m)
            (map_add idApp_eq (cert oldenv) app c)
            (map_add idApp_eq (defPerms oldenv) app (nonSystemUsrP m))
            (systemImage oldenv)
        ).

Definition install_safe (app:idApp) (m:Manifest) (c:Cert) (lRes : list res) (s:System) : Result :=
    match install_pre app m c lRes s with
    | Some ec => result (error ec) s
    | None => result ok (install_post app m c lRes s)
    end.


End ImplInstall.

Section ImplUninstall.

Definition uninstall_pre (app:idApp) (s:System) : option ErrorCode :=
    if (negb (InBool idApp idApp_eq app (apps (state s)))) then Some no_such_app else
    if (isAnyCmpRunning app s) then Some app_is_running else
    None.


Definition uninstall_post (app:idApp) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (remove idApp_eq app (apps oldstate))
            (alreadyVerified oldstate)
            (map_drop idApp_eq (grantedPermGroups oldstate) app)
            (dropAppPerms s app)
            (running oldstate)
            (dropAllPPerms s app)
            (dropAllTPerms s app)
            (dropAllRes (resCont oldstate) app)
            (sentIntents oldstate)
        )
        (env
            (map_drop idApp_eq (manifest oldenv) app)
            (map_drop idApp_eq (cert oldenv) app)
            (map_drop idApp_eq (defPerms oldenv) app)
            (systemImage oldenv)
        ).

Definition uninstall_safe (app:idApp) (s:System) : Result :=
    match uninstall_pre app s with
    | Some ec => result (error ec) s
    | None => result ok (uninstall_post app s)
    end.
End ImplUninstall.

Section ImplGrant.

Definition grant_pre (p:Perm) (app:idApp) (s:System) : option ErrorCode :=
    if (negb (InBool idPerm idPerm_eq (idP p) (permsInUse app s))) then Some perm_not_in_use else
    if (negb (InBool Perm Perm_eq p (getAllPerms s))) then Some no_such_perm else
    if (InBool Perm Perm_eq p (grantedPermsForApp app s)) then Some perm_already_granted else
    if (If permLevel_eq (pl p) (dangerous) then false else true) then Some perm_not_dangerous else
    (* Si el permiso está agrupado y algún otro permiso del grupo ya fue otorgado, fallamos *)
    if (groupIsGranted app p s) then Some perm_should_auto_grant else
    None.

Definition grant_post (p:Perm) (app:idApp) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    let newGrantedPermGroups := match maybeGrp p with
      | None => grantedPermGroups oldstate
      | Some g => grantPermissionGroup app g (grantedPermGroups oldstate)
      end
    in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            newGrantedPermGroups
            (grantPermission app p (perms oldstate))
            (running oldstate)
            (delPPerms oldstate)
            (delTPerms oldstate)
            (resCont oldstate)
            (sentIntents oldstate)
        )
        oldenv.

Definition grant_safe (p:Perm) (app:idApp) (s:System) : Result :=
    match grant_pre p app s with
    | Some ec => result (error ec) s
    | None => result ok (grant_post p app s)
    end.

End ImplGrant.

Section ImplGrantAuto.

Definition grantAuto_pre (p:Perm) (app:idApp) (s:System) : option ErrorCode :=
    if (negb (InBool idPerm idPerm_eq (idP p) (permsInUse app s))) then Some perm_not_in_use else
    if (negb (InBool Perm Perm_eq p (getAllPerms s))) then Some no_such_perm else
    if (InBool Perm Perm_eq p (grantedPermsForApp app s)) then Some perm_already_granted else
    if (If permLevel_eq (pl p) (dangerous) then false else true) then Some perm_not_dangerous else
    (* Si el permiso no está agrrupado, fallamos.  *)
    if (negb (isSomethingBool idGrp (maybeGrp p))) then Some perm_not_grouped else
    (*Si el permiso está agrupado pero no fue 'otorgado' previamente, fallamos. *)
    if (negb (groupIsGranted app p s)) then Some cannot_auto_grant else
    None.


Definition grantAuto_post (p:Perm) (app:idApp) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            (grantedPermGroups oldstate)
            (grantPermission app p (perms oldstate))
            (running oldstate)
            (delPPerms oldstate)
            (delTPerms oldstate)
            (resCont oldstate)
            (sentIntents oldstate)
        )
        oldenv.

Definition grantAuto_safe (p:Perm) (app:idApp) (s:System) : Result :=
    match grantAuto_pre p app s with
    | Some ec => result (error ec) s
    | None => result ok (grantAuto_post p app s)
    end.
End ImplGrantAuto.

Section ImplRevoke.

Definition revoke_pre (p:Perm) (app:idApp) (s:System) : option ErrorCode :=
    if negb (InBool Perm Perm_eq p (grantedPermsForApp app s)) then Some perm_wasnt_granted else
    if (isSomethingBool idGrp (maybeGrp p)) then Some perm_is_grouped else
    None.


Definition revoke_post (p:Perm) (app:idApp) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            (grantedPermGroups oldstate)
            (revokePermission app p (perms oldstate))
            (running oldstate)
            (delPPerms oldstate)
            (delTPerms oldstate)
            (resCont oldstate)
            (sentIntents oldstate)
        )
        oldenv.


Definition revoke_safe (p:Perm) (app:idApp) (s:System) : Result :=
    match revoke_pre p app s with
    | Some ec => result (error ec) s
    | None => result ok (revoke_post p app s)
    end.

End ImplRevoke.

Section ImplRevokeGroup.

Definition revokegroup_pre (g:idGrp) (app:idApp) (s:System) : option ErrorCode :=
    match map_apply idApp_eq (grantedPermGroups (state s)) app with
    | Error _ _ => Some group_wasnt_granted
    | Value _ lGrp => if InBool idGrp idGrp_eq g lGrp then None else Some group_wasnt_granted
    end.

Definition revokegroup_post (g:idGrp) (app:idApp) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            (revokePermissionGroup app g (grantedPermGroups oldstate))
            (revokeAllPermsOfGroup app g s)
            (running oldstate)
            (delPPerms oldstate)
            (delTPerms oldstate)
            (resCont oldstate)
            (sentIntents oldstate)
        )
        oldenv.


Definition revokegroup_safe (g:idGrp) (app:idApp) (s:System) : Result :=
    match revokegroup_pre g app s with
    | Some ec => result (error ec) s
    | None => result ok (revokegroup_post g app s)
    end.

End ImplRevokeGroup.


Section ImplRead.

Definition read_pre (icmp:iCmp) (cp:CProvider) (u:uri) (s:System) : option ErrorCode :=
    if negb (existsResBool cp u s) then Some no_such_res else
    match map_apply iCmp_eq (running (state s)) icmp with
    | Error _ _ => Some instance_not_running
    | Value _ c => if canReadBool c cp s || delPermsBool c cp u Read s then None else Some not_enough_permissions
    end.
    

Definition read_post (icmp:iCmp) (cp:CProvider) (u:uri) (s:System) : System := s.

Definition read_safe (icmp:iCmp) (cp:CProvider) (u:uri) (s:System) : Result :=
    match read_pre icmp cp u s with
    | Some ec => result (error ec) s
    | None => result ok (read_post icmp cp u s)
    end.

End ImplRead.

Section ImplWrite.

Definition write_pre (icmp:iCmp) (cp:CProvider) (u:uri) (v:Val) (s:System) : option ErrorCode :=
    if negb (existsResBool cp u s) then Some no_such_res else
    match map_apply iCmp_eq (running (state s)) icmp with
    | Error _ _ => Some instance_not_running
    | Value _ c => if canWriteBool c cp s || delPermsBool c cp u Write s then None else Some not_enough_permissions
    end.

Definition write_post (icmp:iCmp) (cp:CProvider) (u:uri) (v:Val) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            (grantedPermGroups oldstate)
            (perms oldstate)
            (running oldstate)
            (delPPerms oldstate)
            (delTPerms oldstate)
            (writeResCont icmp cp u v s)
            (sentIntents oldstate)
        )
        oldenv.

Definition write_safe (icmp:iCmp) (cp:CProvider) (u:uri) (v:Val) (s:System) : Result :=
    match write_pre icmp cp u v s with
    | Some ec => result (error ec) s
    | None => result ok (write_post icmp cp u v s)
    end.

End ImplWrite.

Section ImplStartActivity.

Definition startActivity_pre (intt:Intent) (icmp:iCmp) (s:System) : option ErrorCode := 
    if negb (intTypeEqBool (intType intt) intActivity) then Some incorrect_intent_type else
    if isSomethingBool Perm (brperm intt) then Some faulty_intent else
    if negb (isiCmpRunningBool icmp s) then Some instance_not_running else
    if existsb (fun pair => If idInt_eq (idI intt) (idI (snd pair)) then true else false) (sentIntents (state s)) then Some intent_already_sent else
    None.

Definition startActivity_post (intt:Intent) (icmp:iCmp) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            (grantedPermGroups oldstate)
            (perms oldstate)
            (running oldstate)
            (delPPerms oldstate)
            (delTPerms oldstate)
            (resCont oldstate)
            ((icmp,createIntent intt None ) :: (sentIntents oldstate))
        )
        oldenv.

Definition startActivity_safe (intt:Intent) (icmp:iCmp) (s:System) : Result :=
    match startActivity_pre intt icmp s with
    | Some ec => result (error ec) s
    | None => result ok (startActivity_post intt icmp s)
    end.

End ImplStartActivity.

Section ImplStartService.

Definition startService_pre (intt:Intent) (icmp:iCmp) (s:System) : option ErrorCode := 
    if negb (intTypeEqBool (intType intt) intService) then Some incorrect_intent_type else
    if isSomethingBool Perm (brperm intt) then Some faulty_intent else
    if negb (isiCmpRunningBool icmp s) then Some instance_not_running else
    if existsb (fun pair => If idInt_eq (idI intt) (idI (snd pair)) then true else false) (sentIntents (state s)) then Some intent_already_sent else
    None.

Definition startService_post (intt:Intent) (icmp:iCmp) (s:System) : System :=
    startActivity_post intt icmp s. (* es igual *)

Definition startService_safe (intt:Intent) (icmp:iCmp) (s:System) : Result :=
    match startService_pre intt icmp s with
    | Some ec => result (error ec) s
    | None => result ok (startService_post intt icmp s)
    end.

End ImplStartService.


Section ImplSendBroadcast.

Definition sendBroadcast_pre (intt:Intent) (icmp:iCmp) (p:option Perm) (s:System) : option ErrorCode := 
    if negb (intTypeEqBool (intType intt) intBroadcast) then Some incorrect_intent_type else
    if isSomethingBool Perm (brperm intt) then Some faulty_intent else
    if negb (isiCmpRunningBool icmp s) then Some instance_not_running else
    if existsb (fun pair => If idInt_eq (idI intt) (idI (snd pair)) then true else false) (sentIntents (state s)) then Some intent_already_sent else
    None.

Definition sendBroadcast_post (intt:Intent) (icmp:iCmp) (p:option Perm) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            (grantedPermGroups oldstate)
            (perms oldstate)
            (running oldstate)
            (delPPerms oldstate)
            (delTPerms oldstate)
            (resCont oldstate)
            ((icmp,createIntent intt p) :: (sentIntents oldstate))
        )
        oldenv.

Definition sendBroadcast_safe (intt:Intent) (icmp:iCmp) (p:option Perm) (s:System) : Result :=
    match sendBroadcast_pre intt icmp p s with
    | Some ec => result (error ec) s
    | None => result ok (sendBroadcast_post intt icmp p s)
    end.

End ImplSendBroadcast.

Section ImplSendStickyBroadcast.

Definition sendStickyBroadcast_pre (intt:Intent) (icmp:iCmp) (s:System) : option ErrorCode := 
    sendBroadcast_pre intt icmp None s.

Definition sendStickyBroadcast_post (intt:Intent) (icmp:iCmp) (s:System) : System :=
    startActivity_post intt icmp s. (* es igual *)

Definition sendStickyBroadcast_safe (intt:Intent) (icmp:iCmp) (s:System) : Result :=
    match sendStickyBroadcast_pre intt icmp s with
    | Some ec => result (error ec) s
    | None => result ok (sendStickyBroadcast_post intt icmp s)
    end.

End ImplSendStickyBroadcast.

Section ImplResolveIntent.


Definition resolveIntent_pre (i:Intent) (a:idApp) (s:System) : option ErrorCode := 
    let allCmpsA := getAllCmps a s in
    let allActsA := filter isActivityBool allCmpsA in
    let allServsA := filter isServiceBool allCmpsA in
    let allBroadsA := filter isBroadReceiverBool allCmpsA in
    let theId := idI i in
    if negb (isAppInstalledBool a s) then Some no_such_intt else
    if existsb (fun pair => let ic := fst pair in let intt := snd pair in
        negb (isSomethingBool idCmp (cmpName intt))
        && (If idInt_eq (idI intt) theId then true else false)
        && match map_apply iCmp_eq (running (state s)) ic with
        | Error _ _ => false
        | Value _ c1 => let startableCmps := match intType intt with
                | intActivity => filter (fun c2 => canStartBool c1 c2 s) allActsA
                | intService => filter (fun c2 => canStartBool c1 c2 s) allServsA
                | intBroadcast  => filter (fun c2 => canStartBool c1 c2 s) allBroadsA
                end
                in
                existsb (fun iFil => actionTestBool intt iFil s && categoryTestBool intt iFil s && dataTestBool intt iFil s) (concat (map getFilters startableCmps))
        end) (sentIntents (state s)) then None else Some no_such_intt.



Definition resolveIntent_post (intt:Intent) (a:idApp) (s:System) : System := 
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            (grantedPermGroups oldstate)
            (perms oldstate)
            (running oldstate)
            (delPPerms oldstate)
            (delTPerms oldstate)
            (resCont oldstate)
            (resolveImplicitToExplicitIntent intt a s)
        )
        oldenv.


Definition resolveIntent_safe (intt:Intent) (a:idApp) (s:System) : Result :=
    match resolveIntent_pre intt a s with
    | Some ec => result (error ec) s
    | None => result ok (resolveIntent_post intt a s)
    end.

End ImplResolveIntent.


Section ImplReceiveIntent.


Definition receiveIntent_pre (i:Intent) (ic:iCmp) (a:idApp) (s:System) : option ErrorCode := 
    match maybeIntentForAppCmp i a ic s with
    | None => Some no_such_intt
    | Some c => if isCProviderBool c then Some cmp_is_CProvider else
                if negb (canRunBool a s) then Some should_verify_permissions else
                match map_apply iCmp_eq (running (state s)) ic with
                | Error _ _ => Some instance_not_running
                | Value _ c' => if isCProviderBool c' then Some cmp_is_CProvider else
                        if negb (canStartBool c' c s) then Some a_cant_start_b else
                        match intType i with
                        | intBroadcast => match brperm i with
                            | None => None
                            | Some p => if appHasPermissionBool a p s then None else Some not_enough_permissions
                            end
                        | intActivity => match path (data i) with
                            | None => None
                            | Some u => let allComponents := getAllComponents s in
                                    if (existsb (receiveIntentCmpRequirements c' u s (intentActionType i)) allComponents) then None else Some no_CProvider_fits
                            end
                        | _ => None
                        end
                end
    end.

Definition receiveIntent_post (intt:Intent) (ic:iCmp) (a:idApp) (s:System) : System :=
    match maybeIntentForAppCmp intt a ic s with
    | None => s (* Nunca pasa *)
    | Some c =>
        let oldstate := state s in
        let oldenv := environment s in
        let runningicmps := map_getKeys (running oldstate) in
        let newAlreadyVerified := cons a (alreadyVerified oldstate) in
        let ic' := iCmpGenerator runningicmps in
        let newTPerms := match intType intt with
            | intActivity => match path (data intt) with
                | None => delTPerms oldstate
                | Some u => let cp := getAnyCProviderWithUri u s in
                        performGrantTempPerm (intentActionType intt) u cp ic' s
                end
            | _ => delTPerms oldstate
            end in
        sys (st
                (apps oldstate)
                newAlreadyVerified
                (grantedPermGroups oldstate)
                (perms oldstate)
                (performRunCmp intt ic' c s)
                (delPPerms oldstate)
                newTPerms
                (resCont oldstate)
                (remove sentIntentsElems_eq (ic, intt) (sentIntents oldstate))
            )
            oldenv
    end.


Definition receiveIntent_safe (intt:Intent) (ic:iCmp) (a:idApp) (s:System) : Result :=
    match receiveIntent_pre intt ic a s with
    | Some ec => result (error ec) s
    | None => result ok (receiveIntent_post intt ic a s)
    end.

End ImplReceiveIntent.

Section ImplStop.

Definition stop_pre (icmp:iCmp) (s:System) : option ErrorCode := 
    if is_ValueBool (map_apply iCmp_eq (running (state s)) icmp) then None else Some instance_not_running.

Definition stop_post (icmp:iCmp) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            (grantedPermGroups oldstate)
            (perms oldstate)
            (map_drop iCmp_eq (running oldstate) icmp)
            (delPPerms oldstate)
            (removeTPerms icmp oldstate)
            (resCont oldstate)
            (sentIntents oldstate)
        )
        oldenv.

Definition stop_safe (icmp:iCmp) (s:System) : Result :=
    match stop_pre icmp s with
    | Some ec => result (error ec) s
    | None => result ok (stop_post icmp s)
    end.

End ImplStop.


Section ImplGrantP.

Definition grantP_pre (icmp:iCmp) (cp:CProvider) (a:idApp) (u:uri) (pt:PType) (s:System) : option ErrorCode := 
    if negb (canGrantBool cp u s) then Some CProvider_not_grantable else 
    if negb (existsResBool cp u s) then Some no_such_res else
    if negb (isAppInstalledBool a s) then Some no_such_app else
    match map_apply iCmp_eq (running (state s)) icmp with
    | Error _ _ => Some instance_not_running
    | Value _ c => let thiscanread := (canReadBool c cp s || delPermsBool c cp u Read s) in
                let thiscanwrite := (canWriteBool c cp s || delPermsBool c cp u Write s) in
            match pt with
            | Read => if negb thiscanread then Some not_enough_permissions else None
            | Write => if negb thiscanwrite then Some not_enough_permissions else None
            | Both => if negb thiscanread || negb thiscanwrite then Some not_enough_permissions else None
            end
    end.

Definition grantP_post (icmp:iCmp) (cp:CProvider) (a:idApp) (u:uri) (pt:PType) (s:System) : System :=
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            (grantedPermGroups oldstate)
            (perms oldstate)
            (running oldstate)
            (addDelPPerm (delPPerms oldstate) (a,cp,u) pt)
            (delTPerms oldstate)
            (resCont oldstate)
            (sentIntents oldstate)
        )
        oldenv.

Definition grantP_safe (icmp:iCmp) (cp:CProvider) (a:idApp) (u:uri) (pt:PType) (s:System) : Result :=
    match grantP_pre icmp cp a u pt s with
    | Some ec => result (error ec) s
    | None => result ok (grantP_post icmp cp a u pt s)
    end.

End ImplGrantP.


Section ImplRevokeDel.

Definition revokeDel_pre (icmp:iCmp) (cp:CProvider) (u:uri) (pt:PType) (s:System) : option ErrorCode := 
    if negb (existsResBool cp u s) then Some no_such_res else
    match map_apply iCmp_eq (running (state s)) icmp with
    | Error _ _ => Some instance_not_running
    | Value _ c => let thiscanread := canReadBool c cp s || delPermsBool c cp u Read s in
                 let thiscanwrite := canWriteBool c cp s || delPermsBool c cp u Write s in
            match pt with
            | Read => if negb thiscanread then Some not_enough_permissions else None
            | Write => if negb thiscanwrite then Some not_enough_permissions else None
            | Both => if negb thiscanread || negb thiscanwrite then Some not_enough_permissions else None
            end
    end.

Definition revokeDel_post (icmp:iCmp) (cp:CProvider) (u:uri) (pt:PType) (s:System) : System := 
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (alreadyVerified oldstate)
            (grantedPermGroups oldstate)
            (perms oldstate)
            (running oldstate)
            (removeAllPerms idApp delppermsdomeq (delPPerms oldstate) cp u pt)
            (removeAllPerms iCmp deltpermsdomeq (delTPerms oldstate) cp u pt)
            (resCont oldstate)
            (sentIntents oldstate)
        )
        oldenv.

Definition revokeDel_safe (icmp:iCmp) (cp:CProvider) (u:uri) (pt:PType) (s:System) : Result :=
    match revokeDel_pre icmp cp u pt s with
    | Some ec => result (error ec) s
    | None => result ok (revokeDel_post icmp cp u pt s)
    end.

End ImplRevokeDel.


Section ImplCall.

Definition call_pre (icmp:iCmp) (sac:SACall) (s:System) : option ErrorCode := 
    match map_apply iCmp_eq (running (state s)) icmp with
    | Error _ _ => Some instance_not_running
    | Value _ c => let a := getAppFromCmp c s in
            if existsb (fun p => negb (appHasPermissionBool a p s)) (getMandatoryPerms sac) then Some not_enough_permissions else None
    end.


Definition call_post (icmp:iCmp) (sac:SACall) (s:System) : System := s.

Definition call_safe (icmp:iCmp) (sac:SACall) (s:System) : Result :=
    match call_pre icmp sac s with
    | Some ec => result (error ec) s
    | None => result ok (call_post icmp sac s)
    end.

End ImplCall.

Section VerifyOldApp.

Definition isOldAppBool (app: idApp) (s: System) : bool :=
    let m := getManifestForApp app s in
    match targetSdk m with
        | None => false
        | Some n => n <? vulnerableSdk
    end.

Definition verifyOldApp_pre (app: idApp) (s: System) : option ErrorCode :=
    if negb (isAppInstalledBool app s) then Some no_such_app else
    if (InBool idApp idApp_eq app (alreadyVerified (state s))) then Some already_verified else
    if (negb (isOldAppBool app s)) then Some no_verification_needed else None.


Definition verifyOldApp_post (app: idApp) (s: System) : System := 
    let oldstate := state s in
    let oldenv := environment s in
    sys (st
            (apps oldstate)
            (app :: (alreadyVerified oldstate))
            (map_add idApp_eq (grantedPermGroups oldstate) app nil)
            (map_add idApp_eq (perms oldstate) app nil)
            (running oldstate)
            (delPPerms oldstate)
            (delTPerms oldstate)
            (resCont oldstate)
            (sentIntents oldstate)
        )
        oldenv.

Definition verifyOldApp_safe (a: idApp) (s: System) : Result :=
    match verifyOldApp_pre a s with
    | Some ec => result (error ec) s
    | None => result ok (verifyOldApp_post a s)
    end.

End VerifyOldApp.

Section ImplStep.

(* Función principal: dado un sistema y una acción, retorna el sistema resultante y "ok" si la ejecución fue correcta o un código de error si fue incorrecta *)
Definition step (s:System) (a:Action) : Result := 
    match a with
    | install app m c lRes => install_safe app m c lRes s
    | uninstall app => uninstall_safe app s
    | grant p app => grant_safe p app s
    | grantAuto p app => grantAuto_safe p app s
    | revoke p app => revoke_safe p app s
    | revokePermGroup grp app => revokegroup_safe grp app s
    | hasPermission a p => result ok s
    | read ic cp u => read_safe ic cp u s
    | write ic cp u v => write_safe ic cp u v s
    | startActivity intt ic => startActivity_safe intt ic s
    | startActivityForResult intt n ic => startActivity_safe intt ic s
    | startService intt ic => startService_safe intt ic s
    | sendBroadcast intt ic p => sendBroadcast_safe intt ic p s
    | sendOrderedBroadcast intt ic p => sendBroadcast_safe intt ic p s
    | sendStickyBroadcast intt ic => sendStickyBroadcast_safe intt ic s
    | resolveIntent intt a => resolveIntent_safe intt a s
    | receiveIntent intt ic a => receiveIntent_safe intt ic a s
    | stop ic => stop_safe ic s
    | grantP ic cp a u pt => grantP_safe ic cp a u pt s
    | revokeDel ic cp u pt => revokeDel_safe ic cp u pt s
    | call ic sac => call_safe ic sac s
    | verifyOldApp a => verifyOldApp_safe a s
    end.
End ImplStep.
