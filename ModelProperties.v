(* En este archivo se postulan y demuestran propiedades sobre
*  el modelo y sobre la implementación desarrollada de él *)
Require Import Coq.Arith.Lt.
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
Require Import DangPermMissing.
Require Import RvkCanStart.
Require Import IfOldAppRunThenVerified.

Section ModelProperties.

    (* Permission Groups *)
    (*Internet access irrestricted*)

(* En un estado válido, si una llamada al sistema requiere sólo permisos normales, entonces cualquier instancia en ejecución cuya aplicación liste los permisos
 * correspondientes como usados puede ejecutar la llamada *)
    Theorem sacProtectedWithNormalPerms : forall
        (s:System)
        (access_internet:SACall)
        (c:Cmp)
        (ic:iCmp)
        , validstate s -> (forall (p:Perm) (pIsSystem : isSystemPerm p) (pIsRequired : permSAC p pIsSystem access_internet), pl p = normal) -> (forall (p:Perm) (pIsSystem : isSystemPerm p) (pIsRequired : permSAC p pIsSystem access_internet), In p (use (getManifestForApp (getAppFromCmp c s) s))) -> (map_apply iCmp_eq (running (state s)) ic = Value iCmp c) -> exec s (call ic access_internet) s ok.
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
    
    (* Existe un estado válido en el que una aplicación instalada no tiene un permiso peligroso existente a pesar de que lo lista como usado. *)
    Theorem dangerousPermMissing : exists 
    (s:System)
    (p:Perm)
    (a:idApp)
    , validstate s /\ pl p=dangerous /\ permExists p s /\ In a (apps (state s)) /\ In p (use (getManifestForApp a s)) /\ ~appHasPermission a p s.
Proof.
    apply dangerousPermMissingProof.
Qed.

    (* Delegated permissions *)

(* En todo estado válido, si se le otorga correctamente un permiso p a una aplicación a que tiene uno de sus componentes ejecutándose
 * con identificador ic; quien luego delega un permiso de lectura a una aplicación a' sobre un uri de un contentProvider de lectura protegida
 * por p, y más tarde se le quita el permiso p a a, posteriormente si una instancia en ejecución de un componente de a' intenta leer dicho uri
 * de cp, podrá hacerlo correctamente *)

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


(* Para todo estado inicial válido en el cual una aplicación A no tiene un permiso peligroso  P, si al final de una serie de operaciones en
 * la que A no es desinstalada, A pasa a contar con tal permiso; entonces en algún momento el permiso P le fue otorgado *)
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
        In (grant p a) l \/ In (grantAuto p a) l.
Proof.
    intros.
    apply (ifPermThenGrantedProof initState lastState);auto.
Qed.

(* Si en un estado inicial válido se le revoca correctamente un permiso p a una aplicación a, mientras la aplicación no sea desinstalada
 * ni el permiso reotorgado, la aplicación no contará con él *)
    Theorem revokeAndNotGrant : forall
        (initState sndState lastState:System)
        (a:idApp)
        (p:Perm)
        (l:list Action),
        validstate initState->
        pl p=dangerous->
        (~exists lPerm : list Perm, map_apply idApp_eq (defPerms (environment initState)) a = Value idApp lPerm /\ In p lPerm) ->
        sndState = system (step initState (revoke p a))->
        response (step initState (revoke p a))=ok->
        ~In (uninstall a) l->
        ~In (grant p a) l->
        ~In (grantAuto p a) l ->
        last (trace sndState l) sndState = lastState->
        ~appHasPermission a p lastState.
Proof.
    intros.
    apply (revokeAndNotGrantProof initState sndState lastState H a p H0 H1 H2 H3 l);auto.
Qed.

(* En todo estado válido en donde un componente c1 tiene la potestad de iniciar a una actividad c2 de otra aplicación protegida por
 * un permiso peligroso no agrupado p que no es definido por la aplicación en donde se encuentra c1, existen ciertas acciones que hacen
 * que pierda la posibilidad de hacerlo a pesar de que ninguna de las dos aplicaciones haya sido desinstalada *)
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


(* Para todo estado inicial válido en el que existe una aplicación 'a' vieja y no verificada, si luego de una serie de operaciones
 * 'a' en la que 'a' no se desinstala, 'a' está en condiciones de ser ejecutada; entonces alguna de esas operaciones fue la que la
 * verificó *)
    Theorem ifOldAppRunThenVerified : forall 
        (initState lastState: System)
        (a: idApp)
        (l: list Action)
        (aInstalled:In a (apps (state initState)) \/ (exists x0, In x0 (systemImage (environment initState)) /\ idSI x0 = a))
        (vsInit: validstate initState)
        (oldApp: isOldApp a initState)
        (notVerified: ~(In a (alreadyVerified (state initState))))
        (canRunLastState: canRun a lastState)
        (aIsTheSame : ~ In (uninstall a) l)
        (fromInitToLast: last (trace initState l) initState  = lastState),
        In (verifyOldApp a) l.
Proof.
    apply ifOldAppRunThenWasVerifiedProof.
Qed.

(*
 * Este teorema establece que el sistema no puede otorgar automáticamente un permiso (peligroso) 
 * agrupado si el grupo del mismo no ha sido previamente otorgado a través de un grant de usuario.
 *)
Theorem cannotAutoGrantWithoutGroup :
  forall (s s': System) (p: Perm) (g: idGrp) (a: idApp),
    pl p = dangerous ->
    maybeGrp p = Some g ->
    ~ (exists (lGroup: list idGrp),
      map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp lGroup /\ In g lGroup) ->
    ~ exec s (grantAuto p a) s' ok.
Proof.
  intros s s' p g a dangerousPerm groupedPerm notInGrantedGroups.
  unfold not; intro execGrantAuto.
  unfold exec in execGrantAuto.
  destruct execGrantAuto as [_ [ok | notOk]].
- destruct ok as [_ [preGrantAuto _]].
  unfold pre, pre_grantAuto in preGrantAuto.
  destruct preGrantAuto as [_ [_ [_ [_ existsPermGroup]]]].
  destruct existsPermGroup as [g' [lGroup H]].
  destruct H as [groupedPerm' [groupListOfA gInList]].
  rewrite groupedPerm in groupedPerm'.
  inversion groupedPerm' as [gEquals].
  rewrite <- gEquals in gInList.
  destruct notInGrantedGroups.
  exists lGroup. auto.
- destruct notOk as [ec [absurd _]].
  inversion absurd.
Qed.


(* Este teorema postula que una aplicación vieja que no ha sido verificada por el usuario
 * no puede recibir intents. *)
Theorem notVerifiedOldAppCantReceive :
  forall (s s' : System) (i: Intent) (ic: iCmp) (a: idApp),
    validstate s ->
    isOldApp a s -> (* La aplicación es vieja *)
    ~ (In a (alreadyVerified (state s))) -> (* y no está verificada*)
    ~ exec s (receiveIntent i ic a) s' ok.
Proof.
  intros s s' i ic a vs oldApp notVerified.
  unfold not; intro receiveIntent.
  unfold exec in receiveIntent.
  destruct receiveIntent as [_ H].
  destruct H.
- destruct H as [_ [pre _]].
  simpl in pre. unfold pre_receiveIntent in pre.
  destruct pre as [H _].
  unfold canRun, isOldApp in *.
  destruct H.
* contradiction.
* destruct oldApp as [m [n [isM [target H1]]]]. 
  destruct H as [m' [n' [isM' [target' H2]]]].
  assert (m=m').
  apply (sameAppSameManifest s vs a); auto.
  rewrite H in target.
  rewrite target' in target.
  inversion target.
  rewrite H3 in H2.
  assert (n<n).
  apply (lt_trans n vulnerableSdk); auto.
  apply lt_irrefl in H0; auto.
- destruct H as [ec [H _]].
  inversion H.
Qed.

(* Este teorema demuestra que la operación de borrar un grupo respeta la política
 * de granularidad de Android y elimina todos los permisos correspondientes a ese
 * grupo que han sido otorgados individualmente. *)
Theorem revokeGroupRevokesIndividualPerms :
  forall (s s': System) (g: idGrp) (a: idApp),
    validstate s ->
    exec s (Operaciones.revokePermGroup g a) s' ok ->
    ~ (exists (p: Perm) (permsA: list Perm),
        map_apply idApp_eq (perms (state s')) a = Value idApp permsA /\ In p permsA /\ maybeGrp p = Some g).
Proof.
  intros s s' g a vs revoke.
  unfold not; intro H.
  destruct H as [p [permsA [H1 [H2 H3]]]].
  unfold exec in revoke.
  destruct revoke as [_ H].
  destruct H.
- destruct H as [_ [pre post]].
  simpl in post. unfold post_revokeGroup in post.
  destruct post as [_ [_ [postPerms _]]].
  unfold revokeGroupedPerms in postPerms.
  destruct postPerms as [_ [_ [H _]]].
  destruct H as [permsA' [H4 H]].
  rewrite H4 in H1. inversion H1.
  rewrite H5 in H. apply H in H3.
  contradiction.
- destruct H as [ec [H _]].
  inversion H.
Qed.



End ModelProperties.
