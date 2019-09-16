(* En este archivo se postulan y demuestran propiedades sobre
*  el modelo y sobre la implementación desarrollada de él *)
Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Import Classical.
Require Import Estado.
Require Import DefBasicas.
Require Import Semantica.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.
Require Import MyList.
Require Import ListAuxFuns.
Require Import ValidStateLemmas.
Require Import SameEnvLemmas.
Require Import Semantica.
Require Import RuntimePermissions.
Require Import EqTheorems.
Require Import Trace.
Require Import DelegateGrantPRevoke.
Require Import RvkAndNotGrant.
Require Import IfPermThenGranted.
Require Import HasPermAndNotGranted.
Require Import DangPermMissing.
Require Import RvkCanStart.

Section ModelProperties.

    (* Permission Groups *)
    (* Prueba 1 *)

(* En un estado valido,no puede otorgarse individualmente un permiso peligroso peligroso agrupado *)
    Theorem noGranularityForIndividualPerms : forall 
        (s s':System)
        (p:Perm)
        (g:idGrp)
        (a:idApp)
        ,maybeGrp p = Some g -> ~ exec s (grant p a) s' ok.
Proof.
    intro.
    intro.
    intro.
    intro.
    intro.
    intro pGrouped.
    unfold not;intros.
    destruct H.
    destruct H0.
    destruct_conj H0.
    simpl in H0.
    unfold pre_grant in H0.
    destruct_conj H0.
    rewrite pGrouped in H7.
    discriminate H7.
    destruct H0.
    destruct_conj H0.
    discriminate H1.
Qed.

    (* Prueba 2*)

(* Existe un estado válido en el cual una app tiene un permiso peligroso ajeno sin tenerlo individualmente otorgado *)
    Theorem hasPermissionAndNotGranted : exists 
        (s:System)
        (p:Perm)
        (a:idApp)
        (permsA : list Perm)
        , validstate s /\ pl p = dangerous /\ map_apply idApp_eq (perms (state s)) a = Value idApp permsA /\ ~In p permsA /\ ~In p (getDefPermsForApp a s) /\ appHasPermission a p s.
Proof.
    apply hasPermissionAndNotGrantedProof.
Qed.

    (*Internet access irrestricted*)

(* En un estado válido, si una llamada al sistema requiere sólo permisos normales, entonces cualquier instancia en ejecución cuya aplicación liste los permisos correspondientes como usados puede ejecutar la llamada *)
    Theorem sacProtectedWithNormalPerms : forall
        (s:System)
        (access_internet:SACall)
        (c:Cmp)
        (ic:iCmp)
        , validstate s -> (forall (p:Perm) (pIsSystem : isSystemPerm p) (pIsRequired : permSAC p pIsSystem access_internet), pl p = normal) -> (forall (p:Perm) (pIsSystem : isSystemPerm p) (pIsRequired : permSAC p pIsSystem access_internet), In (idP p) (use (getManifestForApp (getAppFromCmp c s) s))) -> (map_apply iCmp_eq (running (state s)) ic = Value iCmp c) -> exec s (call ic access_internet) s ok.
Proof.
    intro.
    intro.
    intro.
    intro.
    intro sValid.
    intro allRequiredAreNormal.
    intro allRequiredAreListedAsUsed.
    intro icIsRunningC.
    unfold exec.
    split;auto.
    left.
    split;auto.
    split.
    unfold pre.
    unfold pre_call.
    exists c.
    split;auto.
    intros.
    specialize (allRequiredAreNormal p H H1).
    specialize (allRequiredAreListedAsUsed p H H1).
    unfold appHasPermission.
    right.
    split.
    unfold permExists.
    left;auto.
    assert (getAppFromCmp c s=a).
    apply inAppThenGetAppFromCmp;auto.
    rewrite H2 in *.
    split.
    exists (getManifestForApp a s).
    split;auto.
    apply (isManifestOfAppCorrect s sValid a).
    apply (ifInAppThenIsAppInstalled s sValid c);auto.
    right.
    left;auto.
    simpl.
    unfold post_call.
    auto.
Qed.

    (* Missing permissions *)
    
    (* Existe un estado válido en el que una aplicación instalada no tiene un permiso peligroso existente a pesar de que lo lista como usado *)
    Theorem dangerousPermMissing : exists 
    (s:System)
    (p:Perm)
    (a:idApp)
    , validstate s /\ pl p=dangerous /\ permExists p s /\ In a (apps (state s)) /\ In (idP p) (use (getManifestForApp a s)) /\ ~appHasPermission a p s.
Proof.
    apply dangerousPermMissingProof.
Qed.

    (* Delegated permissions *)

(* En todo estado válido, si se le otorga correctamente un permiso p a una aplicación a que tiene uno de sus componentes ejecutándose con identificador ic; quien luego delega un permiso de lectura a una aplicación a' sobre un uri de un contentProvider de lectura protegida por p, y más tarde se le quita el permiso p a a, posteriormente si una instancia en ejecución de un componente de a' intenta leer dicho uri de cp, podrá hacerlo correctamente *)

    Theorem delegateGrantPRevoke : forall 
        (s:System)
        (p:Perm)
        (a a':idApp)
        (ic ic': iCmp)
        (c c':Cmp)
        (u:uri)
        (cp:CProvider),
        validstate s ->
        response (step s (grant p a)) = ok ->
        getAppFromCmp c s = a ->
        getAppFromCmp c' s = a' ->
        map_apply iCmp_eq (running (state s)) ic = Value iCmp c ->
        map_apply iCmp_eq (running (state s)) ic' = Value iCmp c' ->
        canGrant cp u s ->
        existsRes cp u s ->
        expC cp = Some true ->
        readE cp = Some p ->
        let opsResult := trace s (grant p a:: grantP ic cp a' u Read:: revoke p a::nil) in
        response (step (last opsResult s) (read ic' cp u))=ok.
Proof.
    intros.
    apply (delegateGrantPRevokeProof s H p a a' H0 ic ic' c c');auto.
Qed.


    (* Others *)
(* Para todo estado inicial válido en el cual una aplicación a no tiene un permiso peligroso no agrupado p, si al final de una serie de operaciones a pasa a contar con tal permiso a pesar de nunca haber sido desinstalada, entonces en algún momento le fue otorgado *)
    Theorem ifPermThenGranted : forall
        (initState lastState:System)
        (a:idApp)
        (p:Perm)
        (l:list Action),
        validstate initState->
        In a (apps (state initState))->
        pl p = dangerous->
        maybeGrp p = None->
        appHasPermission a p lastState->
        ~appHasPermission a p initState->
        ~In (uninstall a) l->
         last (trace initState l) initState = lastState->
        In (grant p a) l.
Proof.
    intros.
    apply (ifPermThenGrantedProof initState lastState);auto.
Qed.

(* Si en un estado inicial válido se le revoca correctamente un permiso p a una aplicación a, mientras la aplicación no sea desinstalada ni el permiso reotorgado, la aplicación no contará con él *)
    Theorem revokeAndNotGrant : forall
        (initState sndState lastState:System)
        (a:idApp)
        (p:Perm)
        (l:list Action),
        validstate initState->
        pl p=dangerous->
        maybeGrp p = None->
        (~exists lPerm : list Perm, map_apply idApp_eq (defPerms (environment initState)) a = Value idApp lPerm /\ In p lPerm) ->
        sndState = system (step initState (revoke p a))->
        response (step initState (revoke p a))=ok->
        ~In (uninstall a) l->
        ~In (grant p a) l->
        last (trace sndState l) sndState = lastState->
        ~appHasPermission a p lastState.
Proof.
    intros.
    apply (revokeAndNotGrantProof initState sndState lastState H a p H0 H1 H2 H3 H4 l);auto.
Qed.

(* En todo estado válido en donde un componente c1 tiene la potestad de iniciar a una actividad c2 de otra aplicación protegida por un permiso peligroso no agrupado p que no es definido por la aplicación en donde se encuentra c1, existen ciertas acciones que hacen que pierda la posibilidad de hacerlo a pesar de que ninguna de las dos aplicaciones haya sido desinstalada *)
    Theorem revokeCanStart : forall
        (initState:System)
        (l:list Action)
        (a1 a2:idApp)
        (c1:Cmp)
        (act:Activity)
        (p:Perm),
        validstate initState->
        pl p=dangerous->
        maybeGrp p = None->
        a1<>a2 ->
        (~exists lPerm : list Perm, map_apply idApp_eq (defPerms (environment initState)) a1 = Value idApp lPerm /\ In p lPerm) ->
        inApp c1 a1 initState ->
        inApp (cmpAct act) a2 initState ->
        cmpEA act = Some p ->
        canStart c1 (cmpAct act) initState ->
        exists (l:list Action), 
        ~In (uninstall a1) l /\
        ~In (uninstall a2) l /\
        ~canStart c1 (cmpAct act) (last (trace initState l) initState).
Proof.
    apply revokeCanStartProof.
Qed.


End ModelProperties.
