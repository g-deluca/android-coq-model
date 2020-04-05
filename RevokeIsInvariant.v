(* En este archivo se demuestra que la ejecución de
*  la acción revoke preserva los invariantes del sistema *)
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

Section RevokeInv.

    
Lemma RevokeIsInvariant : forall (s s':System) (sValid:validstate s) (p:Perm) (a:idApp) ,pre_revoke p a s -> post_revoke p a s s' -> validstate s'.
Proof.
    intros.
    unfold validstate.
    unfold post_revoke in H0.
    unfold pre_revoke in H.
    destruct H as [H maybeGrp].
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
    rewrite <- H0.
    rewrite <- H3.
    rewrite <- H2.
    intros.
    assert (sv2:=sValid).
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    repeat (split;intros; auto).
    destruct permsSC.
    specialize (H10 H8).
    destruct H10.
    destruct H1.
    destruct_conj H12.
    specialize (H13 a0 x H10).
    destruct H13.
    destruct H12.
    destruct H13.
    exists x0;auto.
    destruct H8.
    destruct permsSC.
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
    rewrite <-H0, <-H3, <-H5, <- H6, <-H7, <-H4.
    repeat (split;auto; try mapcorrect sValid).
    
    unfold grantedPermsExist.
    split.
    intros.
    destruct H1.
    specialize (H1 a0 l H8).
    destruct H1.
    apply (permExistsSpermExistsS' s);auto. 
    destruct H1.
    specialize (H12 p0 H10).
    apply (grantedPermsExistVS s sValid a0 p0 x);auto.
    split.

    unfold noDupSentIntents in *.
    rewrite<- H9.
    destructVS sValid. auto.

    unfold individualInstanceOfGroupedPerm.
    intros. destructVS sValid.
    rewrite <- H3 in H8.
    apply individualInstanceOfGroupedPermVS in H8.
    destruct H8 as [pWitness [lPerm' [H8 [H10 H11]]]].
    destruct H1. 
    destruct H12. specialize (H12 a0 lPerm' H8).
    destruct H12 as [lPermWitness [H12 H14]].
    
    destruct (classic (In pWitness lPermWitness));intros.
 -- exists pWitness, lPermWitness. auto.
 -- specialize (H14 pWitness H10 H15). destruct H14.
    rewrite <- H16 in H11. rewrite -> H11 in maybeGrp.
    inversion maybeGrp.
Qed.
End RevokeInv.

