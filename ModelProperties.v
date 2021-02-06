(* In this file we have the main properties about the model and the implementaion *)
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
Require Import DangPermAutoGranted.

Section ModelProperties.

 (*Internet access irrestricted*)

 (* In a valid state, if a system call requires only a normal permission, then any instance in
 execution of an app that lists that permission as used can execute the call. Particularly, this is
 used to show that any app that lists the Internet permission (its protection level is Normal) as
 used, can access it without explicit user consent. *)
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
    
    (* Exists a valids state where  an app doesn't have a permission  even though it is listed as
    used. This was introduced to show the changes from Android 5 to Android 6, where dangerous
    permissions were granted at runtime. *)
    Theorem dangerousPermMissing : exists 
    (s:System)
    (p:Perm)
    (a:idApp)
    , validstate s /\ pl p=dangerous /\ permExists p s /\ In a (apps (state s)) /\ In p (use (getManifestForApp a s)) /\ ~appHasPermission a p s.
Proof.
    apply dangerousPermMissingProof.
Qed.

    (* Delegated permissions *)

    (* In every valid state, if a permission p is granted to an app A that later delegates this
    permission to an application B, B can still have access to that permission even when p is revoked
    from A*)

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


 (* For every initial state where an app A doesn't have a dangerous permission P, if after a bunch of
 operations A has that permission; then it was granted by the system *)
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

 (* This property states that the only way for an app to obtain a dangerous permission after it was
 revoked, is if the system grants it again *)
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

(* This property proves that the privilege of starting a component from another app that is protected
by some permission, is revokable *)
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


 (* This property states that if an old aplication is able to run, then it had been previously verified by the user *)
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

 (* This theorem states that the system cannot grant automatically a grouped permission if any other
  * permission of the same group has been granted previously. The first permission should have been
  * obtained via explicit user approval or due to a normal protection level (see property DangerousPermissionAutoGranted)
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


(* This theorm states that an old application that is not verified by the user yet, cannot receive
intents *)
Theorem notVerifiedOldAppCantReceive :
  forall (s s' : System) (i: Intent) (ic: iCmp) (a: idApp),
    isOldApp a s -> (* The app is old *)
    ~ (In a (alreadyVerified (state s))) -> (* and it's not verified *)
    ~ exec s (receiveIntent i ic a) s' ok.
Proof.
  intros s s' i ic a oldApp notVerified.
  unfold not; intro receiveIntent.
  unfold exec in receiveIntent.
  destruct receiveIntent as [vs H].
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

 (* This property establishes that revoking a permission group implies revoking every individual
 permission that belongs to that group *)
Theorem revokeGroupRevokesIndividualPerms :
  forall (s s': System) (g: idGrp) (a: idApp),
    exec s (Operaciones.revokePermGroup g a) s' ok ->
    ~ (exists (p: Perm) (permsA: list Perm),
        map_apply idApp_eq (perms (state s')) a = Value idApp permsA /\ In p permsA /\ maybeGrp p = Some g).
Proof.
  intros s s' g a revoke.
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

 (* This property proves that if a dangerous and a normal permission shares a group, then the system
 is able to automatically grant the dangerous permission without explicit user consent *)
Theorem DangerousPermissionAutoGranted : forall
  (s s': System)
  (a: idApp)
  (m: Manifest)
  (c: Cert)
  (resources: list res)
  (pDang pNorm : Perm)
  (g: idGrp),
  permExists pDang s'->
  pl pDang = dangerous ->
  pl pNorm = normal ->
  In pNorm (use m) ->
  In pDang (use m) ->
  maybeGrp pNorm = Some g ->
  maybeGrp pDang = Some g ->
  exec s (install a m c resources) s' ok -> 
  pre_grantAuto pDang a s'.
Proof.
  apply DangerousPermissionAutoGrantedProof.
Qed.


End ModelProperties.
