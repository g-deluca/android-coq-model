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
    destruct H0 as [verified H0].
    unfold pre_revokeGroup in H.
    destruct_conj H0.
    
    unfold allCmpDifferent.
    split.
    intros.
    
    
    apply (inAppS'InAppS a1 s) in H8;auto.
    apply (inAppS'InAppS a2 s) in H10;auto.
    apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
    
    
    unfold notRepeatedCmps.
    split.
    intros.
    apply (inAppS'InAppS a1 s) in H8;auto.
    apply (inAppS'InAppS a2 s) in H10;auto.
    apply (inAppSameCmp s sValid c a1 a2);auto.
    
    
    unfold notCPrunning.
    split.
    rewrite <-H4.
    destructVS sValid.
    auto.
    
    
    split.
    apply (delTmpRunS' s);auto.
    
    split.
    apply (cmpRunAppInsS' s);auto.
    
    split.
    apply (resContAppInstS' s);auto.
    
    
    
    
    unfold statesConsistency.
    split.
    rewrite <- H3.
    rewrite <- H2.
    intros.
    assert (sv2:=sValid).
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    repeat (split;intros; auto).
  - destruct H0.
    apply permsSC in H8. destruct H8 as [lPerm H8].
    destruct_conj H10.
    apply H11 in H8.
    destruct H8 as [lPerm' [H8 _]]. exists lPerm'. auto.
  - destruct H8 as [lPerm' H8].
    destruct H0. apply H0 in H8.
    destruct H8 as [lPerm [H8 _]].
    apply (ifPermsThenInApp s sv2 a0 lPerm).
    auto.
  - apply grantedPermGroupsSC in H8.
    destruct H8 as [lPerm H8].
    destruct H1. destruct_conj H10.
    apply H11 in H8.
    destruct H8 as [lPerm' [H8 _]].
    exists lPerm'. auto.
  - destruct H8 as [lPerm' H8].
    destruct H1. apply H1 in H8.
    destruct H8 as [lPerm [H8 _]].
    apply (ifGroupedPermsThenInApp s sv2 a0 lPerm).
    auto.
  - unfold notDupApp.
    split.
    rewrite <- H2.
    rewrite <- H3.
    destructVS sValid.
    auto.

    unfold notDupSysApp.
    split.
    rewrite <- H2.
    destructVS sValid.
    auto.

    split.
    apply (notDupPermS' s);auto.

    unfold allMapsCorrect.
    split.
    destruct H1.
    destruct_conj H8.
    destruct H0.
    destruct_conj H11.
    rewrite <-H2, <-H4, <-H5, <- H6, <-H7.
    repeat (split;auto; try mapcorrect sValid).

    split.
    unfold grantedPermsExist. intros.
    destruct H0.
    apply H0 in H8.
    destruct H8 as [lPerm' [H8 H12]].
    apply (permExistsSpermExistsS' s);auto.
    apply H12 in H10.
    apply (grantedPermsExistVS s sValid a0 p lPerm');auto.

    unfold noDupSentIntents.
    rewrite<- H9.
    destructVS sValid.
    auto.
Qed.



End RevokeGroupInv.

