(* In this file we prove the property that states that the privilege of starting a component from
another app that is protected by some permission, is revokable *)
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
Require Export PropertiesAuxFuns.
Require Export RvkAndNotGrant.


    Theorem revokeCanStartProof : forall
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
    intro.
    intro.
    intro.
    intro.
    intro.
    intro.
    intro.
    intro initStateValid.
    intro pDangerous.
    intro pUngrouped.
    intro asdif.
    intro notPIna1.
    intro c2ina1.
    intro actina2.
    intro actprotectedbyp.
    intro c1couldstart.
    exists (revoke p a1::nil).
    split.
    unfold not;intros.
    inversion H; inversion H0.
    split.
    unfold not;intros.
    inversion H; inversion H0.
    unfold trace.
    destruct c1couldstart.
    destruct H.
    destruct H.
    destruct H0.
    assert (x=a1).
    apply (inAppSameCmp initState initStateValid c1);auto. 
    assert (x0=a2).
    apply (inAppSameCmp initState initStateValid (cmpAct act));auto. 
    rewrite H2 in *.
    rewrite H3 in *.
    destruct H1.
    contradiction.
    destruct H1.
    specialize (H4 p).
    assert (isAppInstalled a1 initState).
    apply ifInAppThenIsAppInstalled with (c:=c1);auto.
    apply isManifestOfAppCorrect in H5;auto.
    specialize (H4 (getManifestForApp a1 initState)).
    assert (appHasPermission a1 p initState).
    apply H4.
    split;auto.
    destruct H6.
    destruct H6.
    destruct H6.
    
    assert (revoke_pre p a1 initState = None).
    unfold revoke_pre.
    unfold grantedPermsForApp.
    rewrite H6.
    assert (InBool Perm Perm_eq p x1=true).
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    destruct Perm_eq;auto.
    rewrite H8. simpl.
    rewrite pUngrouped.
    auto.
    assert (~appHasPermission a1 p (system (step initState (revoke p a1)))).
    apply revokeAndNotGrantProof with (initState:=initState) (sndState := (system (step initState (revoke p a1)))) (l:=nil);auto.
    simpl.
    unfold revoke_safe.
    rewrite H8;auto.
    simpl in *.
    unfold revoke_safe in *.
    rewrite H8 in *.
    simpl in *.
    unfold not;intros.
    apply H9.
    destruct H10.
    destruct H10.
    destruct H10.
    destruct H11.
    assert (environment initState = environment (revoke_post p a1 initState)).
    auto.
    assert (validstate (revoke_post p a1 initState)).
    assert (revoke_post p a1 initState = system (step initState (revoke p a1))).
    simpl.
    unfold revoke_safe.
    rewrite H8;auto.
    rewrite H14.
    apply stepIsInvariant;auto.
    assert (inApp c1 a1 (revoke_post p a1 initState)).
    apply (inAppS'InAppS a1 initState (revoke_post p a1 initState) );auto.
    assert (inApp (cmpAct act) a2 (revoke_post p a1 initState)).
    apply (inAppS'InAppS a2 initState (revoke_post p a1 initState) );auto.
    apply inAppSameCmp with (a:=x2) in H15;auto. 
    apply inAppSameCmp with (a:=x3) in H16;auto. 
    rewrite H15 in *.
    rewrite H16 in *.
    destruct H12.
    contradiction.
    destruct H12.
    specialize (H17 p).
    assert (isAppInstalled a1 (revoke_post p a1 initState)).
    apply ifInAppThenIsAppInstalled with (c:=c1);auto.
    apply isManifestOfAppCorrect in H18;auto.
    specialize (H17 (getManifestForApp a1 (revoke_post p a1 initState))).
    apply H17.
    auto.
    destruct H6.
    destruct H7.
    destruct H8.
    destruct H8.
    destruct notPIna1.
    exists x1;auto.
    rewrite pDangerous in H8.
    destruct H8.
    inversion H8.
    destruct H8.
    destruct H8.
    destruct H8; inversion H8.
    destruct H8; inversion H8.
Qed.
