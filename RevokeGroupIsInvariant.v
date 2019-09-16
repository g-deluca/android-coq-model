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
    rewrite <- H0.
    rewrite <- H2.
    intros.
    assert (sv2:=sValid).
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    repeat (split;intros; auto).
    destruct H1.
    destruct grantedPermGroupsSC.
    specialize (H11 H8).
    destruct H11.
    destruct_conj H10.
    specialize (H13 a0 x H11).
    destruct H13.
    destruct H13.
    exists x0;auto.
    destruct H8.
    destruct grantedPermGroupsSC.
    apply H11.
    destruct H1.
    specialize (H1 a0 x H8).
    destruct H1.
    destruct H1.
    exists x0;auto.
    
    unfold notDupApp.
    split.
    rewrite <- H2.
    rewrite<-H0.
    destructVS sValid.
    auto.
    
    unfold notDupSysApp.
    split.
    rewrite <-H0.
    destructVS sValid.
    auto.
    
    
    split.
    apply (notDupPermS' s);auto.
    
    unfold allMapsCorrect.
    split.
    destruct H1.
    destruct_conj H8.
    rewrite <-H0, <-H4, <-H5, <- H6, <-H7, <-H3.
    repeat (split;auto; try mapcorrect sValid).
    
    
    split.
    apply (grantedPermsExistS' s);auto.

    unfold noDupSentIntents.
    rewrite<- H9.
    destructVS sValid.
    auto.
Qed.



End RevokeGroupInv.

