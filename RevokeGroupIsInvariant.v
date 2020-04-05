(* En este archivo se demuestra que la ejecución de
*  la acción revokeGroup preserva los invariantes del sistema *)
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

Section RevokeGroupInv.

    
Lemma RevokeGroupIsInvariant : forall (s s':System) (sValid:validstate s) (g:idGrp) (a:idApp) ,pre_revokeGroup g a s -> post_revokeGroup g a s s' -> validstate s'.
Proof.
    intros.
    unfold validstate.
    unfold post_revokeGroup in H0.
    unfold pre_revokeGroup in H.
    destruct_conj H0.
    split.

    unfold allCmpDifferent.
    intros.
    apply (inAppS'InAppS a1 s) in H8;auto.
    apply (inAppS'InAppS a2 s) in H10;auto.
    apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
    split.

    unfold notRepeatedCmps.
    intros.
    apply (inAppS'InAppS a1 s) in H8;auto.
    apply (inAppS'InAppS a2 s) in H10;auto.
    apply (inAppSameCmp s sValid c a1 a2);auto.
    split.
    
    unfold notCPrunning.
    rewrite <-H4.
    destructVS sValid.
    auto.
    split.

    apply (delTmpRunS' s);auto.
    split.

    apply (cmpRunAppInsS' s);auto.
    split.

    apply (resContAppInstS' s);auto.
    split.

    unfold statesConsistency.
    rewrite <- H3.
    rewrite <- H2.
    intros.
    assert (sv2:=sValid).
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    repeat (split;intros; auto).
  - destruct H.
    apply individualInstanceOfGroupedPermVS in H.
    destruct H as [p H]. destruct H as [pList H].
    destruct H. destruct H10.
    specialize (H0 p pList H H10 H11).
    destruct H0.
    apply (ifInAppsOrSysAppThenPerms s sv2 a0) in H8.
    destruct H8. apply H12 in H8.
    destruct H8. destruct H8.
    exists x1. auto.
  - destruct H.
    apply individualInstanceOfGroupedPermVS in H.
    destruct H as [p H]. destruct H as [pList H].
    destruct H. destruct H10.
    specialize (H0 p pList H H10 H11).
    destruct H0. destruct H8.
    apply H0 in H8.
    destruct H8. destruct H8.
    apply (ifPermsThenInApp s sv2 a0) in H8. auto.
  - apply (ifInAppsOrSysAppThenGrantedGroups s sv2 a0) in H8.
    destruct H1.
    destruct grantedPermGroupsSC.
    destruct H8. apply H10 in H8.
    destruct H8. destruct H8.
    exists x0. auto.
  - destruct H1. destruct H8.
    apply H1 in H8. destruct grantedPermGroupsSC.
    apply H12. destruct H8. destruct H8.
    exists x0. auto.
  - split.
    unfold notDupApp.
    rewrite <- H2.
    rewrite<-H3.
    destructVS sValid.
    auto. split.
    
    unfold notDupSysApp.
    rewrite <-H2.
    destructVS sValid.
    auto. split.

    apply (notDupPermS' s);auto.
    split.

    unfold allMapsCorrect.
    destruct H1.
    destruct_conj H8.
    rewrite <-H2, <-H4, <-H5, <- H6, <-H7.
    repeat (split;auto; try mapcorrect sValid).
    destruct_conj grantedPermsExistVS.
    unfold individualInstanceOfGroupedPerm in H24.
    destruct H. apply H24 in H.
    do 3 destruct H. destruct H22.
    specialize (H0 x0 x1 H H22 H25).
    destruct H0. destruct H26. destruct H27. auto.
    split.

    unfold grantedPermsExist. intros.
    destruct H as [lGrp H]. assert (sValid' := sValid).
    destructVS sValid.
    apply individualInstanceOfGroupedPermVS in H.
    destruct H as [perm [lPerm [H11 [H12 H13]]]].
    specialize (H0 perm lPerm H11 H12 H13).
    destruct H0.
    specialize (H a0 l H8). destruct H.
    apply (permExistsSpermExistsS' s);auto.
    destruct H.
    specialize (H14 p H10).
    unfold grantedPermsExist in grantedPermsExistVS.
    apply (grantedPermsExistVS a0 p x); auto.
    split.

    unfold noDupSentIntents.
    rewrite<- H9.
    destructVS sValid.
    auto.

    clear H2 H3 H4 H5 H6 H7 H9.

    destructVS sValid.
    clear allCmpDiffVS notRepCompsVS notCPRunningVS delTmpRunVS
      cmpRunAppInsVS resContAppInstVS statesConsistencyVS notDupAppVS
        notDupSysAppVS notDupPermVS allMapsCorrectVS grantedPermsExistVS sentIntentsCorrectVS.

    destruct H as [lGrp H].
    apply individualInstanceOfGroupedPermVS in H.
    destruct H as [p [lPerm [H [H2 H3]]]].
    specialize (H0 p lPerm H H2 H3).

    unfold individualInstanceOfGroupedPerm.
    intros a' g' lGrp' H4. assert (H4' := H4).
    destruct H4 as [H4 H5].
    destruct H1 as [H1 [H6 H7]]. 
    apply H1 in H4. destruct H4 as [lGrp'' [H4 H8]].
    apply H8 in H5.

    assert (map_apply idApp_eq (grantedPermGroups (state s)) a' = Value idApp lGrp'' /\ In g' lGrp''); auto.
    apply individualInstanceOfGroupedPermVS in H9.
    destruct H9 as [p' [lPerm' [H9 [H10 H11]]]].

    destruct H0 as [H0 [H12 [H13 H14]]].
    apply H12 in H9.
    destruct H9 as [lPermWitness [H9 H15]].
    elim (classic (In p' lPermWitness)); intros.
 -- exists p', lPermWitness. auto.
 -- specialize (H15 p' H10 H16). destruct H15 as [H15 H17].
    rewrite <- H15. rewrite <- H15 in H9.    
    rewrite <- H17 in H11. 
    rewrite H3 in H11.
    inversion H11.
    
    rewrite <- H19, <- H15 in H4'.
    destruct H7 as [[grpList [H7 H20]] _].
    destruct H4' as [H4' H5']. rewrite H7 in H4'.
    inversion H4'. rewrite <- H21 in H5'. contradiction.



Qed.



End RevokeGroupInv.

