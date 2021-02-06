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

Section SendBroadcastInv.

    
Lemma SendBroadcastIsInvariant : forall (s s':System) (sValid:validstate s) (intt:Intent) (ic:iCmp) (maybeP:option Perm), pre_sendBroadcast intt ic maybeP s -> post_sendBroadcast intt ic maybeP s s' -> validstate s'.
Proof.
    intro.
    intro.
    intro.
    intro.
    intro.
    intro.
    intros.
    unfold validstate.
    unfold pre_sendBroadcast in H.
    unfold post_sendBroadcast in H0.
    destruct H0.
    unfold onlyIntentsChanged in H1.
    destruct_conj H1.
    assert (verified:= H10). clear H10.
    assert (H9 := H8). clear H8.
    
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
    rewrite <-H5.
    destructVS sValid.
    auto.
    
    
    split.
    apply (delTmpRunS' s);auto.
    
    split.
    apply (cmpRunAppInsS' s);auto.
    
    split.
    apply (resContAppInstS' s);auto.
    
    split.
    apply (consistencyUnchanged s);auto.
    
    unfold notDupApp.
    split.
    rewrite <- H1.
    rewrite<-H2.
    destructVS sValid.
    auto.
    
    unfold notDupSysApp.
    split.
    rewrite <-H2.
    destructVS sValid.
    auto.
    
    
    split.
    apply (notDupPermS' s);auto.
    
    unfold allMapsCorrect.
    split.
    rewrite <-H2, <-H3, <-H4, <- H5, <-H6, <-H7, <-H9.
    repeat (split;auto; try mapcorrect sValid).
    
    split.
    apply (grantedPermsExistS' s);auto.
    

    unfold noDupSentIntents.
    intros.
    destruct H.
    destruct_conj H12.
    unfold addIntent in H0.
    destruct_conj H0.
    assert (H':=H0).
    specialize (H' i ic0 H8).
    assert (H'':=H0).
    specialize (H'' i' ic' H10).
    destruct H'.
    destruct H''.
    destructVS sValid.
    apply sentIntentsCorrectVS;auto.
    destruct H18.
    destruct H15.
    exists i, ic0.
    split;auto.
    rewrite H11.
    unfold createIntent in H19.
    rewrite H19.
    simpl.
    auto.

    destruct H''.
    destruct H16.
    destruct H15.
    exists i', ic'.
    split;auto.
    rewrite<- H11.
    unfold createIntent in H19.
    rewrite H19.
    simpl.
    auto.
    destruct H16, H18.
    split.
    rewrite<- H16;auto.
    rewrite H19;auto.
Qed.



End SendBroadcastInv.

