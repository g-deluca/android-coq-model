(* En este archivo se demuestra que la ejecución de
*  la acción grant preserva los invariantes del sistema *)
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

Section GrantInv.

    
Lemma GrantIsInvariant : forall (s s':System) (sValid:validstate s) (p:Perm) (a:idApp) ,pre_grant p a s -> post_grant p a s s' -> validstate s'.
Proof.
    intros.
    unfold validstate.
    unfold post_grant in H0.
    unfold pre_grant in H.
    destruct H.
    destruct_conj H0.
    
    unfold allCmpDifferent.
    split.
    intros.
    
    
    apply (inAppS'InAppS a1 s) in H9;auto.
    apply (inAppS'InAppS a2 s) in H11;auto.
    apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
    
    
    unfold notRepeatedCmps.
    split.
    intros.
    apply (inAppS'InAppS a1 s) in H9;auto.
    apply (inAppS'InAppS a2 s) in H11;auto.
    apply (inAppSameCmp s sValid c a1 a2);auto.
    
    
    unfold notCPrunning.
    split.
    rewrite <-H5.
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
    rewrite <- H4.
    intros.
    assert (sv2:=sValid).
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    repeat (split;intros; auto).
    destruct H2.
    destruct permsSC.
    specialize (H12 H9).
    destruct H12.
    specialize (H2 a0 x H12).
    destruct H2.
    destruct H2.
    exists x0;auto.
    destruct H9.
    destruct H2.
    destruct H11.
    specialize (H11 a0 x H9).
    destruct H11.
    destruct H11.
    apply (ifPermsThenInApp s sv2 a0 x0);auto.
    
    
    
    unfold notDupApp.
    split.
    rewrite <- H3.
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
    destruct H2.
    destruct_conj H9.
    rewrite <-H0, <-H4, <-H5, <- H6, <-H7, <-H8.
    repeat (split;auto; try mapcorrect sValid).
    
    unfold grantedPermsExist.
    split.
    intros.
    destruct H2.
    destruct_conj H12.
    specialize (H13 a0 l H9).
    destruct H13.
    destruct H13.
    specialize (H2 a0 x H13).
    destruct H2.
    destruct H2.
    rewrite H9 in H2.
    inversion H2.
    rewrite<-H18 in *.
    specialize (H14 p0 H11).
    elim (classic (In p0 x));intros.
    specialize (H16 p0 H17).
    apply (permExistsSpermExistsS' s);auto.
    apply (grantedPermsExistVS s sValid a0 p0 x);auto.
    specialize (H14 H17).
    destruct H14.
    rewrite <-H19.
    apply (permExistsSpermExistsS' s);auto.
    destruct H1.
    auto.

    unfold noDupSentIntents.
    rewrite<- H10.
    destructVS sValid.
    auto.
Qed.



End GrantInv.

