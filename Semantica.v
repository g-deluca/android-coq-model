(* En este archivo se formalizan las pre y post condiciones de las
 * acciones capaces de mutar el sistema *)
Require Import Estado.
Require Import EqTheorems.
Require Import Operaciones.
Require Import RuntimePermissions.
Require Import Maps.

Section SemInstall.

(* Indica si un elemento pertenece a una lista *)
Definition InBool (A:Set) (aeq : forall x y:A, {x=y} + {x<>y}) (a:A) (list:list A) : bool :=
    existsb (fun a' => If aeq a a' then true else false) list.

(* Indica si una lista tiene duplicados *)
Function has_duplicates (A:Set) (aeq : forall x y:A, {x=y} + {x<>y}) (list:list A) {struct list} : bool :=
    match list with
    | nil => false
    | a::rest => orb (InBool A aeq a rest) (has_duplicates A aeq rest)
    end.

(* Predicado que se cumple cuando no existe en el sistema un componente con igual identificador que c *)
Definition cmpNotInState (c:Cmp) (s:System) : Prop := 
forall (c':Cmp) (a:idApp),
inApp c' a s ->
getCmpId c <> getCmpId c'.

(* Certificado del fabricante del dispositivo *)
Parameter manufactCert : Cert.

(* Indica si el permiso p tiene igual identificador que uno de sistema *)
Definition isSystemPermId (p:Perm) : Prop :=
    (exists p':Perm, isSystemPerm p' /\ idP p' = idP p).

(* Predicado que se cumple cuando los permisos que define el manifiesto no fueron definidos por otra aplicación en el sistema *)
Definition authPerms (m:Manifest)(s:System) : Prop := 
forall (p :Perm),
In p (usrP m) -> (* todos los permisos que define la aplicacion *)
~(isSystemPermId p) -> (* y no sean de sistema (en tal caso se permite pero se ignora!), *)
~(exists p':Perm, usrDefPerm p' s /\ idP p' = idP p). (* no estan ya definidos *)

(* Predicado que se cumple si un componente define correctamente sus intentFilters *)
Definition cmpDeclareIntentFilterCorrectly (c:Cmp): Prop :=
(* Si hay filtros de datos o de categorías, debe haber filtros de actividad *)
match c with
   | cmpAct a => forall (iFil: intentFilter),
                       (In iFil (intFilterA a)) -> ((dataFilter iFil) <> nil \/ (catFilter iFil)<> nil) -> 
                        (actFilter iFil) <> nil
   | cmpSrv s => forall (iFil: intentFilter),
                       (In iFil (intFilterS s)) -> ((dataFilter iFil) <> nil \/ (catFilter iFil)<> nil) -> 
                        (actFilter iFil) <> nil
   | cmpCP _ => True
   | cmpBR br => forall (iFil: intentFilter),
                       (In iFil (intFilterB br)) -> ((dataFilter iFil) <> nil \/ (catFilter iFil)<> nil) -> 
                        (actFilter iFil) <> nil
end.                                      

(* Precondición de install *)
Definition pre_install (a:idApp)(m:Manifest)(c:Cert)(lRes: (list res))(s:System) : Prop := 
(* la aplicación no estaba instalada en el sistema *)
(~isAppInstalled a s) /\
(* no hay dos componentes iguales en la aplicación a instalar *)
(has_duplicates idCmp idCmp_eq (map getCmpId (cmp m)) = false ) /\
(* no hay dos permisos iguales en la aplicación a instalar *)
(has_duplicates idPerm idPerm_eq (map idP (usrP m)) = false ) /\
(* no existe en el sistema ningún componente con igual identificador que los definidos en la aplicación *)
(forall c:Cmp, In c (cmp m) -> cmpNotInState c s) /\
(* no intenta redefinir ningún permiso *)
authPerms m s /\
(* no hay componentes que definan mal los intent filters *)
(forall (c:Cmp), In c (cmp m) -> cmpDeclareIntentFilterCorrectly c).

(* Valor incial para los recursos de las aplicaciones *)
Parameter initVal : Val.

(* Agrega el Manifesto al estado estático del sistema *)
Definition addManifest (m:Manifest)(a:idApp)(s s':System): Prop :=
(forall (a':idApp)(m':Manifest), 
map_apply idApp_eq (manifest (environment s)) a' = Value idApp m' ->
map_apply idApp_eq (manifest (environment s')) a' = Value idApp m') /\
(forall (a':idApp)(m':Manifest),
map_apply idApp_eq (manifest (environment s')) a' = Value idApp m' ->
map_apply idApp_eq (manifest (environment s)) a' = Value idApp m' \/ a = a')/\
map_apply idApp_eq (manifest (environment s')) a = Value idApp m /\
map_correct (manifest (environment s')).

(* Agrega el Certificado al estado estático del sistema *)
Definition addCert (c:Cert)(a:idApp)(s s':System): Prop :=
(forall (a':idApp)(c':Cert), 
map_apply idApp_eq (cert (environment s)) a' = Value idApp c' ->
map_apply idApp_eq (cert (environment s')) a' = Value idApp c') /\
(forall (a':idApp)(c':Cert),
map_apply idApp_eq (cert (environment s')) a' = Value idApp c' ->
map_apply idApp_eq (cert (environment s)) a' = Value idApp c' \/ a = a')/\
map_apply idApp_eq (cert (environment s')) a = Value idApp c /\
map_correct (cert (environment s')).

(* Agrega la aplicación al estado dinámico del sistema *)
Definition addApp (a:idApp)(s s':System) : Prop :=
(forall a':idApp,
In a' (apps (state s)) -> 
In a' (apps (state s')) ) /\
(forall a':idApp,
In a' (apps (state s')) -> 
In a' (apps (state s)) \/ (a' = a)) /\
In a (apps (state s')).

(* Agrega recursos al estado dinámico del sistema *)
Definition addRes (a:idApp)(lRes: list res)(s s':System) : Prop :=
(forall (a':idApp)(r:res)(v:Val),
map_apply rescontdomeq (resCont (state s)) (a', r) = Value (idApp*res) v -> 
map_apply rescontdomeq (resCont (state s')) (a', r) = Value (idApp*res) v) /\
(forall (a':idApp)(r:res)(v:Val),
map_apply rescontdomeq (resCont (state s')) (a', r) = Value (idApp*res) v -> 
map_apply rescontdomeq (resCont (state s)) (a', r) = Value (idApp*res) v \/ 
(a' = a /\ In r lRes /\ v = initVal)) /\
(forall r:res, In r lRes -> map_apply rescontdomeq (resCont (state s')) (a, r) = Value (idApp*res) initVal) /\
map_correct (resCont (state s')).

(* Agrega los permisos definidos por el usuario *)
Definition addDefPerms (a:idApp)(m:Manifest)(s s':System) : Prop :=
(forall (a':idApp)(lPerm:list Perm), 
map_apply idApp_eq (defPerms (environment s)) a' = Value idApp lPerm ->
map_apply idApp_eq (defPerms (environment s')) a' = Value idApp lPerm)  /\
(forall (a':idApp)(lPerm:list Perm), 
map_apply idApp_eq (defPerms (environment s')) a' = Value idApp lPerm ->
map_apply idApp_eq (defPerms (environment s)) a' = Value idApp lPerm \/ (a=a')) /\
(exists (lPerm: (list Perm)),
map_apply idApp_eq (defPerms (environment s')) a = Value idApp lPerm /\
(forall (p:Perm), 
In p (usrP m) /\ ~ isSystemPermId p <->
In p lPerm)) /\
map_correct (defPerms (environment s')).

Definition initializePermLists (a:idApp) (s s':System) : Prop :=
(* Se inicializan permisos y grupos otorgados a la aplicación como vacíos *)
(forall (a':idApp)(lPerm: list Perm),
map_apply idApp_eq (perms (state s)) a' = Value idApp lPerm -> 
map_apply idApp_eq (perms (state s')) a' = Value idApp lPerm) /\
(forall (a':idApp)(lPerm:list Perm),
map_apply idApp_eq (perms (state s')) a' = Value idApp lPerm -> 
map_apply idApp_eq (perms (state s)) a' = Value idApp lPerm \/
(a=a' /\ lPerm=nil)) /\
(map_apply idApp_eq (perms (state s')) a = Value idApp nil) /\
(forall (a':idApp)(lGrp: list idGrp),
map_apply idApp_eq (grantedPermGroups (state s)) a' = Value idApp lGrp -> 
map_apply idApp_eq (grantedPermGroups (state s')) a' = Value idApp lGrp) /\
(forall (a':idApp)(lGrp:list idGrp),
map_apply idApp_eq (grantedPermGroups (state s')) a' = Value idApp lGrp -> 
map_apply idApp_eq (grantedPermGroups (state s)) a' = Value idApp lGrp \/
(a=a' /\ lGrp=nil)) /\
(map_apply idApp_eq (grantedPermGroups (state s')) a = Value idApp nil) /\
map_correct (grantedPermGroups (state s'))/\
map_correct (perms (state s')).


(* Postcondición de install *)
Definition post_install (a:idApp) (m:Manifest) (c:Cert) (lRes: (list res)) (s s':System) : Prop := 
(* Agregar manifesto, certificado, lista de recursos y permisos definidos al estado estático del sistema *)
addManifest m a s s' /\
addCert c a s s' /\
addDefPerms a m s s' /\
(* Agregar la aplicación, recursos y permisos al estado dinámico del sistema *)
addApp a s s' /\
addRes a lRes s s' /\
initializePermLists a s s' /\
(* el resto de los campos no cambian *)
running (state s) = running (state s') /\ 
delPPerms (state s) = delPPerms (state s') /\ 
delTPerms (state s) = delTPerms (state s') /\
systemImage (environment s) = systemImage (environment s') /\
sentIntents (state s) = sentIntents (state s').

End SemInstall.


Section SemUninstall.

(* Precondición de uninstall *)
Definition pre_uninstall (a:idApp)(s:System) : Prop :=
(* La aplicación está instalada *)
In a (apps (state s))  /\
(* y ninguno de sus componentes está en ejecución *)
(forall (ic:iCmp)(c:Cmp), 
map_apply iCmp_eq (running (state s)) ic = Value iCmp c -> 
~inApp c a s).

(* Quitar el Manifesto del sistema *)
Definition removeManifest (a:idApp) (s s':System) : Prop :=
(forall (a':idApp)(m':Manifest), 
map_apply idApp_eq (manifest (environment s')) a' = Value idApp m' ->
map_apply idApp_eq (manifest (environment s)) a' = Value idApp m') /\
(forall (a':idApp)(m':Manifest),
map_apply idApp_eq (manifest (environment s)) a' = Value idApp m' ->
map_apply idApp_eq (manifest (environment s')) a' = Value idApp m' \/ a = a')/\
~is_Value (map_apply idApp_eq (manifest (environment s')) a) /\
map_correct (manifest (environment s')).

(* Quitar el Certificado al estado estático del sistema *)
Definition removeCert (a:idApp)(s s':System): Prop :=
(forall (a':idApp)(c':Cert), 
map_apply idApp_eq (cert (environment s')) a' = Value idApp c' ->
map_apply idApp_eq (cert (environment s)) a' = Value idApp c') /\
(forall (a':idApp)(c':Cert),
map_apply idApp_eq (cert (environment s)) a' = Value idApp c' ->
map_apply idApp_eq (cert (environment s')) a' = Value idApp c' \/ a = a')/\
~is_Value (map_apply idApp_eq (cert (environment s')) a) /\
map_correct (cert (environment s')).

(* Quitar la aplicación del sistema *)
Definition removeApp (a:idApp)(s s':System) : Prop :=
(forall a':idApp, In a' (apps (state s')) -> In a' (apps (state s))) /\
(forall a':idApp, In a' (apps (state s)) -> In a' (apps (state s')) \/ a' = a) /\
~ In a (apps (state s'))/\
removeManifest a s s' /\
removeCert a s s'.

(* Revocar los permisos otorgados a la aplicación *)
Definition revokePerms (a:idApp) (s s': System) : Prop := 
(forall (a':idApp) (lPerm': list Perm),
map_apply idApp_eq (perms (state s')) a' = Value idApp lPerm' ->
exists lPerm:list Perm,
map_apply idApp_eq (perms (state s)) a' = Value idApp lPerm) /\
(forall (a':idApp)(lPerm: list Perm),
map_apply idApp_eq (perms (state s)) a' = Value idApp lPerm ->
(exists lPerm',
map_apply idApp_eq (perms (state s')) a' = Value idApp lPerm' /\
forall (defPermsA : list Perm) (p:Perm),
map_apply idApp_eq (defPerms (environment s)) a = Value idApp defPermsA ->
((In p lPerm /\ ~In p defPermsA) <-> In p lPerm')) \/
a = a')/\
~is_Value (map_apply idApp_eq (perms (state s')) a) /\
map_correct (perms (state s')).

(* Revocar los permisos otorgados a la aplicación *)
Definition revokePermGroups (a:idApp) (s s': System) : Prop := 
(forall (a':idApp)(lGrps: list idGrp),
map_apply idApp_eq (grantedPermGroups (state s')) a' = Value idApp lGrps ->
map_apply idApp_eq (grantedPermGroups (state s)) a' = Value idApp lGrps) /\
(forall (a':idApp)(lGrps: list idGrp),
map_apply idApp_eq (grantedPermGroups (state s)) a' = Value idApp lGrps ->
map_apply idApp_eq (grantedPermGroups (state s')) a' = Value idApp lGrps \/
a = a')/\
~is_Value (map_apply idApp_eq (grantedPermGroups (state s')) a) /\
map_correct (grantedPermGroups (state s')).

(* Borrar los permisos definidos por la aplicación *)
Definition removeDefPerms (a:idApp) (s s':System) : Prop :=
(forall (a':idApp)(lPerm: list Perm),
map_apply idApp_eq (defPerms (environment s')) a' = Value idApp lPerm ->
map_apply idApp_eq (defPerms (environment s)) a' = Value idApp lPerm) /\
(forall (a':idApp)(lPerm: list Perm),
map_apply idApp_eq (defPerms (environment s)) a' = Value idApp lPerm ->
map_apply idApp_eq (defPerms (environment s')) a' = Value idApp lPerm \/
a = a')/\
~is_Value(map_apply idApp_eq (defPerms (environment s')) a) /\
map_correct (defPerms (environment s')).

(* Quitar los recursos de la aplicación *)
Definition removeRes (a:idApp) (s s':System) : Prop :=
(forall (a':idApp)(r:res)(v:Val), map_apply rescontdomeq (resCont (state s')) (a', r) = Value (idApp*res) v -> map_apply rescontdomeq (resCont (state s)) (a', r) = Value (idApp*res) v) /\
(forall (a':idApp)(r:res)(v:Val), map_apply rescontdomeq (resCont (state s)) (a', r) = Value (idApp*res) v -> map_apply rescontdomeq (resCont (state s')) (a', r) = Value (idApp*res) v \/ a = a') /\
(forall (r:res), ~is_Value (map_apply rescontdomeq (resCont (state s')) (a, r))) /\
map_correct (resCont (state s')).

(* Borrar los permisos delegados de forma temporal a otras instancias 
en ejecución sobre recursos de algún CProvider de la aplicación *)
Definition revokeOtherTPerm (a:idApp)(s s': System) : Prop :=
(forall (ic:iCmp)(cp:CProvider)(u:uri)(pt:PType),
map_apply deltpermsdomeq (delTPerms (state s')) (ic, cp, u) = Value (iCmp*CProvider*uri) pt -> map_apply deltpermsdomeq (delTPerms (state s)) (ic, cp, u) = Value (iCmp*CProvider*uri) pt) /\
(forall (ic:iCmp)(cp:CProvider)(u:uri)(pt:PType),
map_apply deltpermsdomeq (delTPerms (state s)) (ic, cp, u) = Value (iCmp*CProvider*uri) pt -> map_apply deltpermsdomeq (delTPerms (state s')) (ic, cp, u) = Value (iCmp*CProvider*uri) pt \/ 
inApp (cmpCP cp) a s) /\
(forall (ic:iCmp)(cp:CProvider)(u:uri)(pt:PType),
inApp (cmpCP cp) a s -> 
~ is_Value (map_apply deltpermsdomeq (delTPerms (state s')) (ic, cp, u))) /\
map_correct (delTPerms (state s')).

(* Borrar los permisos delegados de forma permanente a la aplicación y los permisos delegados de forma permanente 
a otras aplicaciones sobre recursos de algún CProvider de la aplicación *)
Definition revokePPerm (a:idApp) (s s':System) : Prop :=
(forall (a':idApp)(cp:CProvider)(u:uri)(pt:PType),
map_apply delppermsdomeq (delPPerms (state s')) (a', cp, u) = Value (idApp*CProvider*uri) pt -> map_apply delppermsdomeq (delPPerms (state s)) (a', cp, u) = Value (idApp*CProvider*uri) pt) /\
(forall (a':idApp)(cp:CProvider)(u:uri)(pt:PType),
map_apply delppermsdomeq (delPPerms (state s)) (a', cp, u) = Value (idApp*CProvider*uri) pt -> map_apply delppermsdomeq (delPPerms (state s')) (a', cp, u) = Value (idApp*CProvider*uri) pt \/ a = a' \/ 
inApp (cmpCP cp) a s) /\
(forall (cp:CProvider)(u:uri)(pt:PType), ~ is_Value (map_apply delppermsdomeq (delPPerms (state s')) (a, cp, u))) /\
(forall (a':idApp)(cp:CProvider)(u:uri)(pt:PType),
inApp (cmpCP cp) a s->
~ is_Value (map_apply delppermsdomeq (delPPerms (state s')) (a', cp, u))) /\
map_correct (delPPerms (state s')).

(* Postcondición de uninstall *)
Definition post_uninstall (a:idApp)(s s':System) : Prop := 
(* Se quita la aplicación de la lista de apps instaladas, *)
removeApp a  s s' /\
(* Se quitan los permisos otorgados a ella *)
revokePerms a s s' /\
revokePermGroups a s s' /\
(* Se quitan los permisos que define *)
removeDefPerms a s s' /\
(* Se quitan sus recursos *)
removeRes a s s' /\
(* Se revocan permisos delegados a cproviders de ella *)
revokeOtherTPerm a s s' /\
revokePPerm a s s'/\
(* nada más cambia *)
running (state s) = running (state s') /\
systemImage (environment s) = systemImage (environment s') /\
sentIntents (state s) = sentIntents (state s').

End SemUninstall.

Section SemGrant.

(* Predicado que se cumple cuando el usuario autoriza el otorgamiento de un permiso *)
Parameter usrAuth : Perm -> Prop. (* no entiendo que significa *)

(* Precondición grant *)
Definition pre_grant (p:Perm)(a:idApp)(s:System) : Prop :=
(exists m:Manifest, isManifestOfApp a m s /\
In (idP p) (use m)) /\ (* Solo permito grantear independientemente permisos declarados en el Manifest *)
(isSystemPerm p \/ usrDefPerm p s) /\ (* , que existan *)
~(exists lPerm:list Perm, map_apply idApp_eq (perms (state s)) a = Value idApp lPerm /\ In p lPerm) /\ (* No hayan sido ya granteados *)
pl p = dangerous /\ (* , sean peligrosos *)
(*, el permiso no está agrupado *)
(maybeGrp p = None \/
  (exists (g: idGrp), maybeGrp p = Some g /\ (* o si el permiso está agrupado, ese grupo no debe haber sido 'otorgado' previamente *)
    (forall (lGroup: list idGrp), map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp lGroup -> ~(In g lGroup)))).

(* Agrega los permisos otorgados a la aplicación *)
Definition grantPerm (a:idApp)(p:Perm)(s s':System) : Prop :=
(forall (a':idApp)(lPerm:list Perm),
map_apply idApp_eq (perms (state s)) a' = Value idApp lPerm ->
exists lPerm':list Perm, map_apply idApp_eq (perms (state s')) a' = Value idApp lPerm' /\
forall p':Perm, In p' lPerm -> In p' lPerm') /\

(forall (a':idApp)(lPerm':list Perm),
map_apply idApp_eq (perms (state s')) a' = Value idApp lPerm' ->
exists lPerm:list Perm, map_apply idApp_eq (perms (state s)) a' = Value idApp lPerm /\
forall p':Perm, In p' lPerm' -> ~In p' lPerm -> (a=a' /\ p=p')) /\

(exists (lPerm':(list Perm)), map_apply idApp_eq (perms (state s')) a = Value idApp lPerm' /\ In p lPerm') /\
map_correct (perms (state s')).

(* Marca que un permiso del grupo de permisos g ya fue otorgado a la aplicación *)
Definition grantPermGroup (a:idApp)(g:idGrp)(s s':System) : Prop :=
(forall (a':idApp)(lGrp:list idGrp),
map_apply idApp_eq (grantedPermGroups (state s)) a' = Value idApp lGrp ->
exists lGrp':list idGrp, map_apply idApp_eq (grantedPermGroups (state s')) a' = Value idApp lGrp' /\
forall g':idGrp, In g' lGrp -> In g' lGrp') /\
(forall (a':idApp)(lGrp':list idGrp),
map_apply idApp_eq (grantedPermGroups (state s')) a' = Value idApp lGrp' ->
exists lGrp:list idGrp, map_apply idApp_eq (grantedPermGroups (state s)) a' = Value idApp lGrp /\
forall g':idGrp, In g' lGrp' -> ~In g' lGrp -> (a=a' /\ g=g')) /\
(exists (lGrp':(list idGrp)), map_apply idApp_eq (grantedPermGroups (state s')) a = Value idApp lGrp' /\ In g lGrp') /\
map_correct (grantedPermGroups (state s')).

(* Postcondición grant *)
Definition post_grant (p:Perm)(a:idApp)(s s':System) : Prop :=
(* Se otorga el permiso p a a *)
grantPerm a p s s' /\
(* y si el permiso está agrupado, marcamos al grupo como otorgado *)
(forall (g: idGrp), maybeGrp p = Some g -> grantPermGroup a g s s') /\
(* pero si no lo está, los grupos permanecen iguales *)
(maybeGrp p = None -> (grantedPermGroups (state s)) = (grantedPermGroups (state s'))) /\
(* nada más cambia *)
(environment s) = (environment s') /\
(apps (state s)) = (apps (state s')) /\
(running (state s)) = (running (state s')) /\
(delPPerms (state s)) = (delPPerms (state s')) /\
(delTPerms (state s)) = (delTPerms (state s')) /\
(resCont (state s)) = (resCont (state s')) /\
(sentIntents (state s)) = (sentIntents (state s')).

End SemGrant.

Section SemGrantAuto.

Definition pre_grantAuto (p: Perm) (a: idApp) (s: System) : Prop :=
(* La precondición es casi la misma que la de grant *)
(exists m:Manifest, isManifestOfApp a m s /\
In (idP p) (use m)) /\
(isSystemPerm p \/ usrDefPerm p s) /\
~(exists lPerm:list Perm, map_apply idApp_eq (perms (state s)) a = Value idApp lPerm /\ In p lPerm) /\
pl p = dangerous /\
(* con la diferencia de que el permiso tiene que estar agrupado, y ese grupo ya debe haber sido 'otorgado' antes *)
(exists (g: idGrp), maybeGrp p = Some g /\
    (forall (lGroup: list idGrp), map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp lGroup -> In g lGroup)).

Definition post_grantAuto (p:Perm) (a:idApp) (s s':System) : Prop :=
(* Se otorga el permiso p a a *)
grantPerm a p s s' /\
(* nada más cambia *)
(environment s) = (environment s') /\
(apps (state s)) = (apps (state s')) /\
(grantedPermGroups (state s)) = (grantedPermGroups (state s')) /\
(running (state s)) = (running (state s')) /\
(delPPerms (state s)) = (delPPerms (state s')) /\
(delTPerms (state s)) = (delTPerms (state s')) /\
(resCont (state s)) = (resCont (state s')) /\
(sentIntents (state s)) = (sentIntents (state s')).
End SemGrantAuto.


Section SemRevoke.

(* Precondición revoke *)
Definition pre_revoke (p:Perm)(a:idApp)(s:System) : Prop :=
(* El permiso debe estar otorgado *)
(exists (lPerm : list Perm), map_apply idApp_eq (perms (state s)) a = Value idApp lPerm /\ In p lPerm) /\
(* y no debe esar agrupado*)
maybeGrp p = None.

(* Quita el permiso otorgado a la aplicación *)
Definition revokePerm (a:idApp)(p:Perm)(s s':System) : Prop :=
(forall (a':idApp)(lPerm':list Perm),
map_apply idApp_eq (perms (state s')) a' = Value idApp lPerm' ->
exists lPerm:list Perm, map_apply idApp_eq (perms (state s)) a' = Value idApp lPerm /\
forall p':Perm, In p' lPerm' -> In p' lPerm) /\

(forall (a':idApp)(lPerm:list Perm),
map_apply idApp_eq (perms (state s)) a' = Value idApp lPerm ->
exists lPerm':list Perm, map_apply idApp_eq (perms (state s')) a' = Value idApp lPerm' /\
forall p':Perm, In p' lPerm -> ~In p' lPerm' -> (a=a' /\ p=p')) /\

(exists (lPerm':(list Perm)), map_apply idApp_eq (perms (state s')) a = Value idApp lPerm' /\ ~In p lPerm') /\
map_correct (perms (state s')).


(* Postcondición revoke *)
Definition post_revoke (p:Perm)(a:idApp)(s s':System) : Prop :=
(* Se revoca el permiso p a a *)
revokePerm a p s s' /\

(* nada más cambia *)
(environment s) = (environment s') /\
apps (state s) = apps (state s') /\
grantedPermGroups (state s) = grantedPermGroups (state s') /\
running (state s) = running (state s') /\
delPPerms (state s) = delPPerms (state s') /\
delTPerms (state s) = delTPerms (state s') /\
resCont (state s) = resCont (state s') /\
sentIntents (state s) = sentIntents (state s').

End SemRevoke.

Section SemGrantGroup.

(* Precondición grantGroup *)
Definition pre_grantGroup (g:idGrp)(a:idApp)(s:System) : Prop := 
~(exists lGrp:list idGrp, map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp lGrp /\ In g lGrp) /\ (* Solo permito grantear grupos de permisos que no hayan sido granteados, *)
(exists (m:Manifest) (p:Perm), isManifestOfApp a m s /\
In (idP p) (use m) /\ (* , sean de algun permiso que declara en el manifest, *)
(isSystemPerm p \/ usrDefPerm p s)  /\ maybeGrp p = Some g /\ (* , que existan *)
pl p = dangerous). (* y quien lo define haya dicho que es peligroso *)


(* Postcondición grant *)
Definition post_grantGroup (g:idGrp)(a:idApp)(s s':System) : Prop :=
(* Se otorga el grupo g a a *)
(grantPermGroup a g s s') /\
(* nada más cambia *)
(environment s) = (environment s') /\
(apps (state s)) = (apps (state s')) /\
(perms (state s)) = (perms (state s')) /\
(running (state s)) = (running (state s')) /\
(delPPerms (state s)) = (delPPerms (state s')) /\
(delTPerms (state s)) = (delTPerms (state s')) /\
(resCont (state s)) = (resCont (state s')) /\
(sentIntents (state s)) = (sentIntents (state s')).

End SemGrantGroup.


Section SemRevokeGroup.

(* Precondición revoke *)
Definition pre_revokeGroup (g:idGrp)(a:idApp)(s:System) : Prop :=
(* El permiso debe estar otorgado *)
exists (lGrp : list idGrp), map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp lGrp /\ In g lGrp.

Definition revokePermGroup (a:idApp)(g:idGrp)(s s':System) : Prop :=
(forall (a':idApp)(lGrp':list idGrp),
map_apply idApp_eq (grantedPermGroups (state s')) a' = Value idApp lGrp' ->
exists lGrp:list idGrp, map_apply idApp_eq (grantedPermGroups (state s)) a' = Value idApp lGrp /\
forall g':idGrp, In g' lGrp' -> In g' lGrp) /\

(forall (a':idApp)(lGrp:list idGrp),
map_apply idApp_eq (grantedPermGroups (state s)) a' = Value idApp lGrp ->
exists lGrp':list idGrp, map_apply idApp_eq (grantedPermGroups (state s')) a' = Value idApp lGrp' /\
forall g':idGrp, In g' lGrp -> ~In g' lGrp' -> (a=a' /\ g=g')) /\

(exists (lGrp':(list idGrp)), map_apply idApp_eq (grantedPermGroups (state s')) a = Value idApp lGrp' /\ ~In g lGrp') /\
map_correct (grantedPermGroups (state s')).


(* Postcondición revoke *)
Definition post_revokeGroup (g:idGrp)(a:idApp)(s s':System) : Prop :=
(* Quitamos el grupo g*)
revokePermGroup a g s s' /\

(* Revoco todos los permisos pertenecientes a ese grupo*)
(forall (p: Perm) (lPerm: list Perm),
    map_apply idApp_eq (perms (state s')) a = Value idApp lPerm ->
        In p lPerm ->
          maybeGrp p = Some g ->
            revokePerm a p s s') /\

(* nada más cambia *)
(environment s) = (environment s') /\
apps (state s) = apps (state s') /\
running (state s) = running (state s') /\
delPPerms (state s) = delPPerms (state s') /\
delTPerms (state s) = delTPerms (state s') /\
resCont (state s) = resCont (state s') /\
sentIntents (state s) = sentIntents (state s').

End SemRevokeGroup.

Section SemHasPermission.

(* Precondición haspermission *)
Definition pre_hasPermission (p:Perm)(c:Cmp)(s:System) : Prop :=
(* Nada es necesario para preguntar si un componente tiene permisos *)
True.

(* Postcondición haspermission *)
Definition post_hasPermission (p:Perm)(c:Cmp)(s s':System) : Prop :=
(* Su ejecución no muta el sistema *)
s = s'. 

End SemHasPermission.

Section SemRead.

(* Proposición que se cumple si el mínimo sdk para correr la aplicación es n *)
Definition getCmpMinSdk (c : Cmp) (s:System) (n:nat) : Prop :=
    (exists (idap:idApp) (mfst:Manifest), isManifestOfApp idap mfst s
        /\ inApp c idap s /\ minSdk mfst = Some n).

(* Proposición que se cumple si el sdk objetiv de la aplicación es n *)
Definition getCmpTargetSdk (c : Cmp) (s:System) (n:nat) : Prop :=
    (exists (idap:idApp) (mfst:Manifest), isManifestOfApp idap mfst s
        /\ inApp c idap s /\ targetSdk mfst = Some n).

(* Proposición que se cumple si el mínimo sdk o la versión objetivo para correr la aplicación es menor que 16 *)
Definition getDefaultExp (cp: CProvider) (s:System): Prop :=
exists (m n : nat), getCmpMinSdk (cmpCP cp) s n /\ getCmpTargetSdk (cmpCP cp) s m /\
(n <= 16 \/ m <= 16).

(* Predicado que se cumple si el componente c tiene los permisos necesarios para efectuar la operación thisE sobre el content provider cp *)
Definition canDoThis (c:Cmp)(cp:CProvider)(s:System) (thisE : CProvider -> option Perm) : Prop :=
exists (a1 a2:idApp),
(* c pertenece a a1 *)
inApp c a1 s /\
exists m:Manifest, 
isManifestOfApp a2 m s /\
(* cp pertenece a a2, cuyo manifiesto es m *)
In (cmpCP cp) (cmp m) /\
((((expC cp)= Some true \/
(expC cp = None /\ getDefaultExp cp s))/\ 
forall p:Perm, (thisE cp) = (Some p) \/
(thisE cp = None /\ cmpEC cp = (Some p)) \/ 
(thisE cp = None /\ cmpEC cp = None /\
appE m = Some p) ->
appHasPermission a1 p s (* a1 tiene el permiso necesario para iniciar cp *)
)
\/ a1 = a2). (* o son la misma aplicación *)

(* Proposición que se cumple si el componente c tiene los permisos necesarios para leer el content provider cp *)
Definition canRead (c:Cmp)(cp:CProvider)(s:System) : Prop := canDoThis c cp s readE.

(* El componente c tiene permisos delegados para realizar la operación pt sobre el
  recurso identificado por u del content provider cp *)
Definition delPerms (c:Cmp)(cp:CProvider)(u:uri)(pt:PType)(s:System) :=
exists (a:idApp), 
inApp c a s /\
((exists (ic':iCmp) (c':Cmp), 
map_apply iCmp_eq (running (state s)) ic' = Value iCmp c' /\ 
inApp c' a s /\ (map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp, u) = Value (iCmp*CProvider*uri) Both \/ map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp, u) = Value (iCmp*CProvider*uri) pt)) \/
map_apply delppermsdomeq (delPPerms (state s)) (a, cp, u) = Value (idApp*CProvider*uri) Both \/
map_apply delppermsdomeq (delPPerms (state s)) (a, cp, u) = Value (idApp*CProvider*uri) pt).

(* Precondición de read *)
Definition pre_read (ic:iCmp)(cp:CProvider)(u:uri)(s:System) : Prop :=
(* existe el recurso en el CProvider *)
existsRes cp u s /\
(* existe un componente en una aplicación instalada, que tiene una instancia en ejecución y
  tiene permisos de lectura sobre el recurso *)
(exists (c:Cmp), 
map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
(canRead c cp s \/ delPerms c cp u Read s)).

(* Postcondición de read *)
Definition post_read (ic:iCmp)(cp:CProvider)(u:uri)(s s':System) : Prop :=
(* El sistema no varía *)
s = s'.

End SemRead.


Section SemWrite.

(* Un componente tiene los permisos necesarios para sobreescribir un recurso de un content provider *)
Definition canWrite (c:Cmp)(cp:CProvider)(s:System) : Prop := canDoThis c cp s writeE.

(* Precondición de write *)
Definition pre_write (ic:iCmp)(cp:CProvider)(u:uri)(newV:Val)(s:System) : Prop :=
(* Existe el recurso u en cp *)
existsRes cp u s /\
(exists (c:Cmp),
(* ic es una instancia en ejecución de un componente que puede escribir en u de cp *)
map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
 ~isCProvider c /\ 
(canWrite c cp s \/ delPerms c cp u Write s)).

(* Postcondición de write *)
Definition post_write (ic:iCmp)(cp:CProvider)(u:uri)(val:Val)(s s':System) : Prop :=
(* Actualizamos el contendo del recurso que se escribió *)
(forall (a':idApp)(r:res)(v:Val),
map_apply rescontdomeq (resCont (state s)) (a', r) = Value (idApp*res) v -> map_apply rescontdomeq (resCont (state s')) (a', r) = Value (idApp*res) v \/ 
(inApp (cmpCP cp) a' s /\ 
map_apply uri_eq (map_res cp) u = Value uri r)) /\
(forall (a':idApp)(r:res)(v:Val),
map_apply rescontdomeq (resCont (state s')) (a', r) = Value (idApp*res) v -> map_apply rescontdomeq (resCont (state s)) (a', r) = Value (idApp*res) v \/ 
((inApp (cmpCP cp) a' s)  /\
map_apply uri_eq (map_res cp) u = Value uri r /\ v = val)) /\
(forall (a':idApp)(r:res), inApp (cmpCP cp) a' s ->
map_apply uri_eq (map_res cp) u = Value uri r -> 
map_apply rescontdomeq (resCont (state s')) (a', r) = Value (idApp*res) val) /\
map_correct (resCont (state s')) /\
(* El resto del sistema no varía *)
(environment s) = (environment s') /\
apps (state s) = apps (state s') /\ 
grantedPermGroups (state s) = grantedPermGroups (state s') /\
perms (state s) = perms (state s') /\
running (state s) = running (state s') /\ 
delPPerms (state s) = delPPerms (state s') /\
delTPerms (state s) = delTPerms (state s') /\ 
sentIntents (state s) = sentIntents (state s').

End SemWrite.


Section SemSendIntent.

Definition cmpRunning (ic:iCmp) (s:System): Prop :=
(* existe un componente instalado en una aplicación que está ejecutándose *)
exists (a:idApp) (c:Cmp),
inApp c a s /\
map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\ ~ isCProvider c.

(* Precondición de start activity *)
Definition pre_startActivity (i:Intent)(ic:iCmp)(s:System) : Prop := 
(* el intent va dirigido a una actividad *)
(intType i) = intActivity /\
(* No especifica ningún permiso (esto se resuelve luego) *)
(brperm i) = None /\
(* ic es una instancia en ejecución *)
cmpRunning ic s /\
(* No existe un intent con igual identificador ya enviado *)
~(exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i).

(* Precondición de start activity for result *)
Definition pre_startActivityForResult (i:Intent)(int:nat)(ic:iCmp)(s:System) : Prop := 
(* Es la misma que la de startActivity*)
    pre_startActivity i ic s.

(* Precondición de start service *)
Definition pre_startService (i:Intent)(ic:iCmp)(s:System) : Prop := 
(* el intent va dirigido a un servicio *)
(intType i) = intService /\
(* No especifica ningún permiso (esto se resuelve luego) *)
(brperm i) = None /\
(* ic es una instancia en ejecución *)
cmpRunning ic s /\
(* No existe un intent con igual identificador ya enviado *)
~(exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i).

(* Precondición de send broadcast *)
Definition pre_sendBroadcast (i:Intent)(ic:iCmp)(p:option Perm)(s:System) : Prop := 
(* el intent va dirigido a un broadcast receiver *)
(intType i) = intBroadcast /\
(* No especifica ningún permiso (esto se resuelve luego) *)
(brperm i) = None /\
(* ic es una instancia en ejecución *)
cmpRunning ic s /\
(* No existe un intent con igual identificador ya enviado *)
~(exists (i':Intent) (ic':iCmp), In (ic',i') (sentIntents (state s)) /\ idI i' = idI i).

(* Precondición de send ordered broadcast *)
Definition pre_sendOrderedBroadcast (i:Intent)(ic:iCmp)(p:option Perm)(s:System) : Prop := 
(* Es la misma que la de sendBroadcast *)
    pre_sendBroadcast i ic p s.

(* Precondición de send sticky broadcast *)
Definition pre_sendStickyBroadcast (i:Intent)(ic:iCmp)(s:System) : Prop := 
(* Es la misma que la de sendBroadcast *)
    pre_sendBroadcast i ic None s.

(* Función que retorna un intent idéntico al especificado pero asignándole un permiso *)
Definition createIntent (oldIntent:Intent) (p:option Perm) : Intent :=
     intent (idI oldIntent)
            (cmpName oldIntent)
            (intType oldIntent)
            (action oldIntent)
            (data oldIntent)
            (category oldIntent)
            (extra oldIntent)
            (flags oldIntent)
            p.

(* Agrega el Intent enviado a la lista de Intents enviados del sistema *)
Definition addIntent (i:Intent)(ic:iCmp) (p:option Perm) (s s':System) : Prop :=
(forall (i':Intent)(ic':iCmp), In (ic', i') (sentIntents (state s)) -> In (ic', i') (sentIntents (state s'))) /\
(forall (i':Intent)(ic':iCmp), In (ic', i') (sentIntents (state s')) -> In (ic', i') (sentIntents (state s)) \/
(ic=ic' /\
i'=createIntent i p))/\
In (ic, createIntent i p) (sentIntents (state s')).

(* Solo la lista de intents enviados cambió *)
Definition onlyIntentsChanged (s s':System) : Prop :=
(environment s) = (environment s') /\
(apps (state s)) = (apps (state s')) /\
(grantedPermGroups (state s)) = (grantedPermGroups (state s')) /\
(perms (state s)) = (perms (state s')) /\
(running (state s)) = (running (state s')) /\
(delPPerms (state s)) = (delPPerms (state s')) /\
(delTPerms (state s)) = (delTPerms (state s')) /\
(resCont (state s)) = (resCont (state s')).

(* Postcondición de start activity *)
Definition post_startActivity (i:Intent)(ic:iCmp)(s s':System) : Prop := 
(* Se crea y agrega el intent a la lista de enviados *)
addIntent i ic None s s' /\
(* El resto del sistema no varía *)
onlyIntentsChanged s s'.

(* Postcondición de start activity for result *)
Definition post_startActivityForResult (i:Intent)(int:nat)(ic:iCmp)(s s':System) : Prop := 
(* Es la misma que la de startActivity*)
    post_startActivity i ic s s'.

(* Postcondición de start service *)
Definition post_startService (i:Intent)(ic:iCmp)(s s':System) : Prop := 
(* Es la misma que la de startActivity*)
    post_startActivity i ic s s'.

(* Postcondición de send broadcast *)
Definition post_sendBroadcast (i:Intent)(ic:iCmp)(p:option Perm)(s s':System) : Prop := 
(* Se crea y agrega el intent a la lista de enviados *)
addIntent i ic p s s' /\
(* El resto del sistema no varía *)
onlyIntentsChanged s s'.

(* Postcondición de send ordered broadcast *)
Definition post_sendOrderedBroadcast (i:Intent)(ic:iCmp)(p:option Perm)(s s':System) : Prop := 
(* Es la misma que la de sendBroadcast *)
    post_sendBroadcast i ic p s s'.

(* Postcondición de send sticky broadcast *)
Definition post_sendStickyBroadcast (i:Intent)(ic:iCmp)(s s':System) : Prop := 
    post_startActivity i ic s s'.

End SemSendIntent.


Section SemResolveIntent.

(* El predicado se cumple si la aplicación puede recibir intents con
  la acción especificada *)
Definition actionTest (i:Intent)(iFil:intentFilter): Prop :=
((action i) = None /\ (actFilter iFil) <> nil) \/ 
(exists (iAct:intentAction), (action i) = Some iAct /\ In iAct (actFilter iFil)).


(* El predicado se cumple si la aplicación puede recibir intents con la 
  categoría especificada *)
Definition categoryTest (i:Intent)(iFil:intentFilter): Prop :=
category i = nil \/ 
(exists (lIntent:list Category), (category i) = lIntent /\
(forall cat:Category, In cat lIntent -> In cat (catFilter iFil))).

(* El predicado se cumple si la URI del intent es de tipo 'content' o 'file' *)
Definition isContentOrFile (i:Intent) : Prop :=
(type (data i)) = content \/ (type (data i)) = file.

(* Si el intent no especifica URI ni tipo MIME, pasa el test si el filtro 
  tampoco lo hace *)
Definition notUriAndNotMime (i:Intent)(iFil:intentFilter): Prop :=
path (data i) = None /\ 
mime (data i) =None /\
dataFilter iFil = nil.

(* Si el intent especifica URI pero no tipo MIME, pasa el test
  si el filtro especifica la misma URI y no especifica ningún tipo MIME *)
Definition uriAndNotMime (i:Intent)(iFil:intentFilter) : Prop :=
path (data i) <> None /\
mime (data i) = None /\
exists (d:Data), (data i) = d /\ In d (dataFilter iFil).

(* Si el intent especifica tipo MIME pero no URI, pasa el test
  si el filtro lista el mismo tipo MIME y no especifica ninguna URI *)
Definition notUriAndMime (i:Intent)(iFil:intentFilter) : Prop :=
path (data i) = None /\
mime (data i) <> None /\
exists (d:Data), (data i) = d /\ In d (dataFilter iFil).


(* Si el intent especifica tipo MIME y URI, pasa el test
  si el filtro lista el mismo tipo MIME y 
  el filtro lista la misma URI o 
  la URI contiene un content: o file: y el filtro no lista ninguna URI *)
Definition uriAndMime (i:Intent)(iFil:intentFilter) : Prop :=
path (data i) <> None /\
mime (data i) <> None /\
(exists (dCmp1:Data)(dCmp2:Data),
(mime (data i) = mime dCmp1 /\ In dCmp1 (dataFilter iFil) /\
(path (data i) = path dCmp2 \/ (isContentOrFile i /\ path dCmp2 = None)) /\ In dCmp2 (dataFilter iFil))).

(* El predicado se cumple si se cumplen alguno de los cuatro tests especificados
  anteriormente *)
Definition dataTest (i:Intent)(iFil:intentFilter): Prop :=
notUriAndNotMime i iFil \/
uriAndNotMime i iFil \/
notUriAndMime i iFil \/
uriAndMime i iFil.

(* El componente c tiene definido algún intent filter *)
Definition canBeStarted (c:Cmp) (s:System): Prop :=
 match c with
    | cmpAct a => (expA a = Some true) \/ (expA a = None /\ (intFilterA a) = nil)
    | cmpSrv sr => (expS sr = Some true) \/ (expS sr = None /\ (intFilterS sr) = nil)
    | cmpCP cp => (expC cp = Some true) \/ (expC cp = None /\ getDefaultExp cp s)
    | cmpBR br => (expB br = Some true) \/ (expB br = None /\ (intFilterB br) = nil)
 end.

(* El componente c1 tiene los permisos para iniciar al componente c2 mandando un intent explícito *)
Definition canStart (c1 c2: Cmp)(s:System) : Prop :=
exists (a1 a2:idApp),
inApp c1 a1 s /\ inApp c2 a2 s /\
(* Ambos componentes pertenecen a la misma aplicación o *)
(a1 = a2 \/
(* c2 puede ser iniciado por otro componente y *)
(canBeStarted c2 s /\
(* a1 tiene los permisos de acceso *)
(forall (p:Perm)(m:Manifest),
isManifestOfApp a1 m s /\
match c2 with 
    | cmpAct a => (cmpEA a = Some p \/ (cmpEA a = None /\ (appE m) = Some p))
    | cmpSrv s => (cmpES s = Some p \/ (cmpES s = None /\ (appE m) = Some p))
    | cmpCP cp => (cmpEC cp = Some p \/ (cmpEC cp = None /\ (appE m) = Some p))
    | cmpBR br => (cmpEB br = Some p \/ (cmpEB br = None /\ (appE m) = Some p))
end ->
appHasPermission a1 p s))).

(* Precondición de resolve intent *)
Definition pre_resolveIntent (idi:Intent)(a:idApp)(s:System) : Prop := 
exists (i:Intent),
(* El id del intent que se desea resolver debe existir *)
idI idi = idI i /\
(* , debe ser implícito *)
(cmpName i) = None /\
exists ic:iCmp,
In (ic ,i) (sentIntents (state s)) /\
exists c1:Cmp,
(* fue enviado por una instancia en ejecución de c1 *)
map_apply iCmp_eq (running (state s)) ic = Value iCmp c1 /\
exists c2:Cmp,
(* existe algún componente *)
inApp c2 a s /\
(exists (iFil: intentFilter),
(* uno de cuyos filtros es satisfecho por el intent *)
match (intType i) with
    | intActivity => exists act:Activity, (cmpAct act) = c2 /\ In iFil (intFilterA act)
    | intService => exists sr:Service, (cmpSrv sr) = c2 /\ In iFil (intFilterS sr)
    | intBroadcast => exists br:BroadReceiver, (cmpBR br) = c2 /\ In iFil (intFilterB br)
end /\
actionTest i iFil /\
categoryTest i iFil /\
dataTest i iFil) /\
(* y efectivamente es iniciable por c1 *)
canStart c1 c2 s.

(* El Intent que se resuelve pasa a ser explícito *)
Definition implicitToExplicitIntent (idi:idInt)(a:idApp)(s s':System) : Prop :=
(exists (c c1:Cmp), inApp c a s /\
(* c será el componente receptor del intent, cuya existencia aseguró la precondición *)
(exists (ic:iCmp) (i:Intent),
(cmpName i) = None /\
idi = idI i /\
In (ic ,i) (sentIntents (state s)) /\
map_apply iCmp_eq (running (state s)) ic = Value iCmp c1 /\
(exists (iFil: intentFilter),
match (intType i) with
    | intActivity => exists act:Activity, (cmpAct act) = c /\ In iFil (intFilterA act)
    | intService => exists sr:Service, (cmpSrv sr) = c /\ In iFil (intFilterS sr)
    | intBroadcast => exists br:BroadReceiver, (cmpBR br) = c /\ In iFil (intFilterB br)
end /\
actionTest i iFil /\
categoryTest i iFil /\
dataTest i iFil)) /\
canStart c1 c s /\
(* Todo intent anterior que no es quien se está resolvieno, se mantiene *)
(forall (i:Intent)(ic:iCmp), In (ic,i) (sentIntents (state s)) ->
In (ic,i) (sentIntents (state s')) \/ idi = idI i ) /\
(* Todos los nuevos intents o existían antes (y no son el que se está resolviendo)
*  o son el que se está resolviendo, actualizado *)
(forall (i:Intent)(ic:iCmp), In (ic,i) (sentIntents (state s')) -> 
(In (ic,i) (sentIntents (state s)) /\ idI i <> idi) \/ 
exists (i':Intent), 
In (ic,i') (sentIntents (state s)) /\
idI i' = idi /\
idI i' = idI i /\
cmpName i = Some (getCmpId c) /\
intType i' = intType i /\
action i' = action i /\
data i' = data i /\
category i' = category i /\
extra i' = extra i /\
flags i' = flags i /\
brperm i' = brperm i) /\
(* El intent actualizado forma parte del nuevo estado *)
(forall (ic:iCmp) (i:Intent),
In (ic, i) (sentIntents (state s)) -> 
idI i = idi ->
(exists (i':Intent),
In (ic,i') (sentIntents (state s')) /\
(idI i' = idI i /\
cmpName i' = Some (getCmpId c) /\
intType i' = intType i /\
action i' = action i /\
data i' = data i /\
category i' = category i /\
extra i' = extra i /\
flags i' = flags i /\
brperm i' = brperm i)
))).

(* Postcondición de resolve intent *)
Definition post_resolveIntent (i:Intent)(a:idApp)(s s':System) : Prop :=
(* Se explicita el intent *)
implicitToExplicitIntent (idI i) a s s' /\
(* el resto de los componentes del estado se mantienen iguales *)
(environment s) = (environment s') /\
(apps (state s)) = (apps (state s')) /\
(grantedPermGroups (state s)) = (grantedPermGroups (state s')) /\
(perms (state s)) = (perms (state s')) /\
(running (state s)) = (running (state s')) /\
(delPPerms (state s)) = (delPPerms (state s')) /\
(delTPerms (state s)) = (delTPerms (state s')) /\
(resCont (state s)) = (resCont (state s')).

End SemResolveIntent.


Section SemReceiveIntent.

(* El intent está dirigido a un componente de la aplicación *)
Definition intentForApp (i:Intent)(a:idApp)(c:Cmp)(ic:iCmp)(s:System) : Prop :=
(cmpName i) = Some (getCmpId c) /\ 
In (ic,i) (sentIntents (state s)) /\
inApp c a s.

(* El content provider permite delegar permisos sobre el recurso referido por el id *)
Definition canGrant (cp:CProvider)(u:uri)(s:System) : Prop :=
exists (a:idApp),
(* Si es un componente presente en el sistema y *)
inApp (cmpCP cp) a s /\
(* el cprovider define u como otorgable o *)
(In u (uriP cp)  \/
(* el cprovider no especifica que uris son otorgables y
* dice que todas ellas son otorgables *)
(~(exists u':uri, In u' (uriP cp)) /\ (grantU cp) = true)).

(* Dado un Intent, se necesita conocer el tipo de acceso que efectuará *)
Parameter intentActionType: Intent -> PType. 

(* TODO: Preguntar cómo representar esto. Sabemos el número del sdk a partir del
cual no podría correrse, pero no sé si conviene dejarlo como parámetro o no *)
Parameter vulnerableSdk : nat.

(* Defino un predicado que establece las condiciones en las que una aplicación puede correr *)
Definition canRun (a: idApp) (s: System) : Prop :=
(* Puede ejecutarse si ya fue ejecutada previamente*)
In a (alreadyRun (state s)) \/
(* o si el targetSdk de la aplicación existe y es lo suficientemente alto *)
(forall (m: Manifest),
    map_apply idApp_eq (manifest (environment s)) a = Value idApp m ->
        (exists n: nat, targetSdk m = Some n /\ n > vulnerableSdk)).
        (* TODO: Qué pasa cuando no existe el targetSdk? *)



(* Precondición de receive intent *)
Definition pre_receiveIntent (i:Intent)(ic:iCmp)(a:idApp)(s:System): Prop :=
(* a puede recibir el intent si está en condiciones de ser ejecutada *)
canRun a s /\
(* a puede recibir el intent si está destinado a uno de sus componentes *)
exists (c:Cmp), intentForApp i a c ic s /\
(* que no es un cprovider *)
~isCProvider c /\
exists (c':Cmp),
(* fue enviado por una instancia en ejecución de c' *)
map_apply iCmp_eq (running (state s)) ic = Value iCmp c' /\
~isCProvider c' /\
(* quien puede iniciarlo *)
canStart c' c s /\
((intType i) = intActivity ->
forall (u:uri), path (data i)= Some u ->
(* si el intent es de actividad y accede a u *)
(exists (cp:CProvider), 
(*, u debe existir en algún cprovider cp *)
existsRes cp u s /\
(* u debe soportar otorgamiento de permisos *)
canGrant cp u s /\
(* quien lo envio'debe tener tales permisos *)
match (intentActionType i) with
   | Read => canRead c' cp s \/ delPerms c' cp u Read s (* Se permite la redelegación *)
   | Write => canWrite c' cp s \/ delPerms c' cp u Write s
   | Both => (canRead c' cp s \/ delPerms c' cp u Read s) /\ (canWrite c' cp s \/ delPerms c' cp u Write s)
end)) /\
((intType i) = intBroadcast /\ (brperm i) <> None ->
(* si el intent es de broadcast y define un permiso necesario, *)
(exists (p:Perm),
(brperm i) = Some p /\
(* la aplicación debe contar con él *)
appHasPermission a p s)).


(* El componente ic no se está ejecutando en el sistema *)
Definition insNotInState (ic:iCmp) (s:System) : Prop :=
~is_Value (map_apply iCmp_eq (running (state s)) ic).

(* Ejecución de ic en s' *)
Definition runCmp (i:Intent)(ic:iCmp)(c:Cmp)(s s':System): Prop :=
(* Todo lo que estaba ejecutándose se mantiene *)
(forall (ic':iCmp)(c':Cmp), 
map_apply iCmp_eq (running (state s)) ic' = Value iCmp c' -> 
map_apply iCmp_eq (running (state s')) ic' = Value iCmp c')/\ 
(* Todo lo nuevo en ejecución o existía o es la instancia que estamos iniciando *)
(forall (ic':iCmp)(c':Cmp), 
map_apply iCmp_eq (running (state s')) ic' = Value iCmp c' -> 
map_apply iCmp_eq (running (state s)) ic' = Value iCmp c' \/ (ic=ic'/\ c=c')) /\
(* La instancia que estamos iniciando forma parte del nuevo estado*)
map_apply iCmp_eq (running (state s')) ic = Value iCmp c /\
(* running sigue siendo una func parcial *)
map_correct (running (state s')).

(* Se quitó el Intent de la lista de enviados *)
Definition removeIntent (i:Intent)(ic:iCmp)(s s':System) : Prop :=
(forall (i':Intent)(ic':iCmp), In (ic',i') (sentIntents (state s')) -> In (ic',i') (sentIntents (state s))) /\
(forall (i':Intent)(ic':iCmp), In (ic',i') (sentIntents (state s)) -> In (ic',i') (sentIntents (state s')) \/ 
(i = i' /\ ic = ic')) /\
~(In (ic,i) (sentIntents (state s'))).

(* Se otorga permiso temporal a ic de acceso pt sobre el uri u del cprovider cp *)
Definition grantTempPerm (pt:PType)(u:uri)(cp:CProvider)(ic:iCmp)(s s':System) : Prop :=
((forall (ic':iCmp)(cp':CProvider)(u':uri)(pt':PType),
map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp', u') = Value (iCmp*CProvider*uri) pt' -> map_apply deltpermsdomeq (delTPerms (state s')) (ic', cp', u') = Value (iCmp*CProvider*uri) pt') /\
(forall (ic':iCmp)(cp':CProvider)(u':uri)(pt':PType),
map_apply deltpermsdomeq (delTPerms (state s')) (ic', cp', u') = Value (iCmp*CProvider*uri) pt' -> 
map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp', u') = Value (iCmp*CProvider*uri) pt' \/ (ic=ic'/\cp=cp'/\u=u'/\pt=pt')) /\
map_apply deltpermsdomeq (delTPerms (state s')) (ic, cp, u) = Value (iCmp*CProvider*uri) pt ) /\
map_correct (delTPerms (state s')).

Definition runApp (a: idApp) (s s': System): Prop :=
(* Mantenemos la información sobre las aplicaciones que no son a *)
(forall a':idApp,
    In a' (alreadyRun (state s)) ->
        In a' (alreadyRun (state s'))) /\
(* Todas las aplicaciones que ahora están marcadas como ejecutadas lo estaban desde antes 
   o es la aplicación en cuestión*)
(forall a':idApp,
    In a' (apps (state s')) ->
        In a' (apps (state s)) \/ (a' = a)) /\
(* La aplicación 'a' ahora quedó marcada como ya ejecutada *)
In a (apps (state s')).

(* Postcondición de receive intent *)
Definition post_receiveIntent (i:Intent)(ic:iCmp)(a:idApp)(s s':System):Prop :=
(* Seteamos que la aplicación ya fue ejecutada al menos una vez*)
runApp a s s' /\
(exists (ic':iCmp)(c:Cmp), intentForApp i a c ic s /\
~isCProvider c /\
(* ic' no debe ser el id de una instancia ya en ejecución *)
insNotInState ic' s /\ 
(* se inicia una instancia de c con identificador ic' *)
runCmp i ic' c s s' /\
(* si es una actividad *)
((intType i) = intActivity ->
(exists (u:uri)(cp:CProvider), 
(* y accede a una uri u *)
path (data i)=Some u /\
existsRes cp u s /\
(* se grantea el permiso temporal correspondiente *)
grantTempPerm (intentActionType i) u cp ic' s s')  \/ 
(* si no, los permisos temporales no cambian *)
path (data i) = None /\ (delTPerms (state s)) = (delTPerms (state s'))) /\
(* si es un servicio o un broadcast receiver los permisos temporales no cambian *)
((intType i) = intService ->
(delTPerms (state s)) = (delTPerms (state s'))) /\
((intType i) = intBroadcast ->
(delTPerms (state s)) = (delTPerms (state s')))) /\
(* se quita el intent recibido de la lista de intents enviados *)
removeIntent i ic s s' /\
(* s y s' difieren a lo sumo solo en running y sentIntents y delTPerms *)
(environment s) = (environment s') /\
(apps (state s)) = (apps (state s')) /\
(grantedPermGroups (state s)) = (grantedPermGroups (state s')) /\
(perms (state s)) = (perms (state s')) /\
(delPPerms (state s)) = (delPPerms (state s')) /\
(resCont (state s)) = (resCont (state s')).

End SemReceiveIntent.


Section SemStop.

(* Precondición de stop *)
Definition pre_stop (ic: iCmp)(s: System) : Prop :=
(* ic debe existir entre los ids de instancia en ejecución *)
exists (c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c.

(* Postcondición de stop *)
Definition post_stop (ic:iCmp)(s s':System) : Prop :=
(* stopIns: Borrar la instancia en ejecución *)
(forall (ic':iCmp)(c':Cmp), 
map_apply iCmp_eq (running (state s')) ic' = Value iCmp c' ->
map_apply iCmp_eq (running (state s)) ic' = Value iCmp c')/\
(forall (ic':iCmp)(c':Cmp), 
map_apply iCmp_eq (running (state s)) ic' = Value iCmp c' ->
map_apply iCmp_eq (running (state s')) ic' = Value iCmp c' \/ ic=ic')/\
map_correct (running (state s')) /\
insNotInState ic s' /\
(* revokeTPermsIns: Si se delegó algún permiso temporal a la instancia, revocarlo *)
(forall (ic':iCmp)(cp:CProvider)(u:uri)(pt:PType), map_apply deltpermsdomeq (delTPerms (state s')) (ic', cp, u) = Value (iCmp*CProvider*uri) pt -> 
map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp, u) = Value (iCmp*CProvider*uri) pt) /\
(forall (ic':iCmp)(cp:CProvider)(u:uri)(pt:PType), map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp, u) = Value (iCmp*CProvider*uri) pt -> 
(map_apply deltpermsdomeq (delTPerms (state s')) (ic', cp, u) = Value (iCmp*CProvider*uri) pt \/ ic' = ic)) /\
(forall (cp:CProvider)(u:uri), ~is_Value (map_apply deltpermsdomeq (delTPerms (state s')) (ic, cp, u))) /\
(* asegurar la corrección de la función delTPerms *)
map_correct (delTPerms (state s')) /\
(* el resto de los componentes no cambian *)
(environment s) = (environment s') /\
apps (state s) = apps (state s') /\ 
grantedPermGroups (state s) = grantedPermGroups (state s') /\ 
perms (state s) = perms (state s') /\ 
delPPerms (state s) = delPPerms (state s') /\ 
resCont (state s) = resCont (state s') /\ 
sentIntents (state s) = sentIntents (state s').

End SemStop.


Section SemGrantP.

(* Precondición de grantp *)
Definition pre_grantP (ic:iCmp)(cp:CProvider)(a:idApp)(u:uri)(pt:PType)(s:System) : Prop :=
(* el uri u debe ser otorgable *)
canGrant cp u s /\
(* debe existir en cp *)
existsRes cp u s /\ 
(* a debe ser una aplicación instalada en el sistema *)
isAppInstalled a s /\
exists (c:Cmp),
(* ic es una instancia en ejecución de c *)
map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
(* quien cuenta con el permiso que quiere otorgar *)
match pt with
   | Read => canRead c cp s \/ delPerms c cp u Read s
   | Write => canWrite c cp s \/ delPerms c cp u Write s
   | Both => (canRead c cp s \/ delPerms c cp u Read s) /\ (canWrite c cp s \/ delPerms c cp u Write s)
end.

(* Función que suma dos permisos *)
Definition ptplus (pt pt':PType) : PType :=
match pt with
    | Both => Both
    | Read => match pt' with
        | Read => Read
        | _ => Both
        end
    | Write=> match pt' with
        | Write => Write
        | _ => Both
        end
end.

(* Postcondición de grantp *)
Definition post_grantP (ic:iCmp)(cp:CProvider)(a:idApp)(u:uri)(pt:PType)(s s':System) : Prop :=
(* Todo otorgamiento que no sea el que estamos pisando, permanece igual *)
(forall (a':idApp)(cp':CProvider)(u':uri)(pt':PType),
map_apply delppermsdomeq (delPPerms (state s)) (a', cp', u') = Value (idApp*CProvider*uri) pt' -> 
((a=a'/\cp=cp'/\u=u') ->
map_apply delppermsdomeq (delPPerms (state s')) (a', cp', u') = Value (idApp*CProvider*uri) (ptplus pt pt')) /\
(~(a=a'/\cp=cp'/\u=u') ->
map_apply delppermsdomeq (delPPerms (state s')) (a', cp', u') = Value (idApp*CProvider*uri) pt')
) /\
(* se suma el pt actual al que ya tenía previamente *)
(forall (a':idApp)(cp':CProvider)(u':uri)(pt':PType),
map_apply delppermsdomeq (delPPerms (state s')) (a', cp', u') = Value (idApp*CProvider*uri) pt' -> 
((a=a'/\cp=cp'/\u=u') ->
match map_apply delppermsdomeq (delPPerms (state s)) (a', cp', u') with
    | Value _ pt'' => ptplus pt pt'' = pt'
    | _ => pt = pt'
end
) /\
(~(a=a'/\cp=cp'/\u=u') ->
map_apply delppermsdomeq (delPPerms (state s)) (a', cp', u') = Value (idApp*CProvider*uri) pt')) /\
map_apply delppermsdomeq (delPPerms (state s')) (a, cp, u) =
match map_apply delppermsdomeq (delPPerms (state s)) (a, cp, u) with
    | Value _ pt' => Value (idApp*CProvider*uri) (ptplus pt' pt)
    | _ => Value (idApp*CProvider*uri) pt
end /\
(* se debe asegurar la corrección de delPPerms *)
map_correct (delPPerms (state s')) /\
(* El resto de los campos del estado no cambian *)
(environment s) = (environment s') /\
apps (state s) = apps (state s') /\
grantedPermGroups (state s) = grantedPermGroups (state s') /\
perms (state s) = perms (state s') /\
running (state s) = running (state s') /\
delTPerms (state s) = delTPerms (state s') /\
resCont (state s) = resCont (state s') /\
sentIntents (state s) = sentIntents (state s').

End SemGrantP.


Section SemRevokeDel.

(* Precondición de revokedel *)
Definition pre_revokeDel (ic:iCmp)(cp:CProvider)(u:uri)(pt:PType)(s:System) : Prop :=
(* el recurso apuntado por u debe existir en cp *)
existsRes cp u s /\
exists (c:Cmp),
map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
(* el componente del cual ic es una instancia en ejecución debe tener el permiso que desea revocar *)
match pt with
   | Read => canRead c cp s \/ delPerms c cp u Read s
   | Write => canWrite c cp s \/ delPerms c cp u Write s
   | Both => (canRead c cp s \/ delPerms c cp u Read s) /\ (canWrite c cp s \/ delPerms c cp u Write s)
end.

(* Función de resta de tipos de acceso *)
Definition ptminus (pt pt':PType) : option PType :=
match pt' with
    | Both => None
    | Read => match pt with
        | Read => None
        | _ => Some Write
        end
    | Write=> match pt with
        | Write => None
        | _ => Some Read
        end
end.


(* Postcondición de revokedel *)
Definition post_revokeDel (ic:iCmp)(cp:CProvider)(u:uri)(pt:PType)(s s':System) : Prop :=
(* Todo otorgamiento que no sea el que estamos pisando, permanece igual *)
(forall (ic':iCmp)(cp':CProvider)(u':uri)(pt':PType),
map_apply deltpermsdomeq (delTPerms (state s')) (ic', cp', u') = Value (iCmp*CProvider*uri) pt' -> 
exists pt'':PType, map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp', u') = Value (iCmp*CProvider*uri) pt'' /\
(pt'' = pt' \/
(cp' = cp /\ u' = u /\ ptminus pt'' pt = Some pt'))
) /\
(forall (ic':iCmp)(cp':CProvider)(u':uri)(pt':PType),
map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp', u') = Value (iCmp*CProvider*uri) pt' -> 
(ptminus pt' pt = None /\ cp'=cp /\ u'=u) \/
(exists pt'':PType, map_apply deltpermsdomeq (delTPerms (state s')) (ic', cp', u') = Value (iCmp*CProvider*uri) pt'' /\ 
(pt'' = pt' \/
(cp' = cp /\ u' = u /\ ptminus pt' pt = Some pt'')))) /\
(* se pisa el permiso temporal con la resta entre él y el que se desea quitar *)
(forall ic':iCmp,
match map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp, u) with
    | Error _ _ => ~(is_Value (map_apply deltpermsdomeq (delTPerms (state s')) (ic', cp, u)))
    | Value _ pt' => match ptminus pt' pt with
        | None => ~(is_Value (map_apply deltpermsdomeq (delTPerms (state s')) (ic', cp, u)))
        | Some pt'' => map_apply deltpermsdomeq (delTPerms (state s')) (ic', cp, u) = Value (iCmp*CProvider*uri) pt''
        end
    end) /\
(* se debe asegurar la corrección de delTPerms *)
map_correct (delTPerms (state s')) /\
(* Todo otorgamiento que no sea el que estamos pisando, permanece igual *)
(forall (a':idApp)(cp':CProvider)(u':uri)(pt':PType),
map_apply delppermsdomeq (delPPerms (state s')) (a', cp', u') = Value (idApp*CProvider*uri) pt' -> 
exists pt'':PType, map_apply delppermsdomeq (delPPerms (state s)) (a', cp', u') = Value (idApp*CProvider*uri) pt'' /\
(pt'' = pt' \/
(cp' = cp /\ u' = u /\ ptminus pt'' pt = Some pt'))
) /\
(* se pisa el permiso temporal con la resta entre él y el que se desea quitar *)
(forall (a':idApp)(cp':CProvider)(u':uri)(pt':PType),
map_apply delppermsdomeq (delPPerms (state s)) (a', cp', u') = Value (idApp*CProvider*uri) pt' -> 
(ptminus pt' pt = None /\ cp'=cp /\ u'=u) \/
(exists pt'':PType, map_apply delppermsdomeq (delPPerms (state s')) (a', cp', u') = Value (idApp*CProvider*uri) pt'' /\ 
(pt'' = pt' \/
(cp' = cp /\ u' = u /\ ptminus pt' pt = Some pt'')))) /\
(forall a':idApp,
match map_apply delppermsdomeq (delPPerms (state s)) (a', cp, u) with
    | Error _ _ => ~(is_Value (map_apply delppermsdomeq (delPPerms (state s')) (a', cp, u)))
    | Value _ pt' => match ptminus pt' pt with
        | None => ~(is_Value (map_apply delppermsdomeq (delPPerms (state s')) (a', cp, u)))
        | Some pt'' => map_apply delppermsdomeq (delPPerms (state s')) (a', cp, u) = Value (idApp*CProvider*uri) pt''
    end
end) /\
(* se debe asegurar la corrección de delTPerms *)
map_correct (delPPerms (state s')) /\
(* El resto de los campos no cambian *)
(environment s) = (environment s') /\
apps (state s) = apps (state s') /\ 
grantedPermGroups (state s) = grantedPermGroups (state s') /\ 
perms (state s) = perms (state s') /\ 
running (state s) = running (state s') /\ 
resCont (state s) = resCont (state s') /\ 
sentIntents (state s) = sentIntents (state s').

End SemRevokeDel.


Section SemCall.

(* Predicado para determinar qué permisos requiere determinada llamada a una API del sistema *)
Parameter permSAC : forall p:Perm, isSystemPerm p -> SACall -> Prop.

(* Precondición de call *)
Definition pre_call (ic:iCmp)(sac:SACall)(s:System) : Prop :=
(* El componente del cual ic es una instancia en ejecución debe tener todos los permisos requeridos para efectuar sac *)
exists c:Cmp, 
map_apply iCmp_eq (running (state s)) ic = Value iCmp c /\
forall (a:idApp)(p:Perm)(H:isSystemPerm p), 
inApp c a s -> 
permSAC p H sac -> 
appHasPermission a p s.

(* Postcondición de call *)
Definition post_call (ic:iCmp)(sac:SACall)(s s':System) : Prop :=
(* El sistema permanece invariante *)
s = s'.

End SemCall.

Section SemVerifyOldApp.

Definition pre_verifyOldApp (a: idApp) (s: System) : Prop :=
(* Chequeamos que la aplicación esté instalada ... *)
(In a (apps (state s))) /\
(* ... que no haya sido ejecutada nunca ... *)
~ (In a (alreadyRun (state s))) /\
(* ... y que el targetSdk sea lo suficientemente viejo *)
(forall (m:Manifest),
    isManifestOfApp a m s ->
        (exists n: nat, targetSdk m = Some n /\ n < vulnerableSdk)
).

Definition post_verifyOldApp (a: idApp) (s s': System) :=
(**
 * Removemos todos los permisos que hayan sido otorgados a esta aplicación,
 * porque fueron otorgados en tiempo de instalación. Representamos la idea
 * del popup que le sale al usuario para verificar los permisos con una
 * traza de 'grant's sucesivos.
 *)
(forall (lPerm: list Perm) (p: Perm),
    map_apply idApp_eq (perms (state s)) a = Value idApp lPerm ->
        In p lPerm -> revokePerm a p s s') /\

(**
 * Marcamos a la aplicación como que ya fue ejecutada alguna vez
 * TODO: Quizás queda un poco raro hacer esto.
 *)
runApp a s s' /\
(* Nada más cambia  *)
(environment s = environment s') /\
(apps (state s) = apps (state s')) /\
(running (state s) = running (state s')) /\
(delPPerms (state s) = delPPerms (state s')) /\
(delTPerms (state s) = delTPerms (state s')) /\
(resCont (state s) = resCont (state s')) /\
(sentIntents (state s) = sentIntents (state s')).

End SemVerifyOldApp.
