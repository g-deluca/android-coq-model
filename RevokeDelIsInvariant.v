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

Section RevokeDelInv.

    
Lemma RevokeDelIsInvariant : forall (s s':System) (sValid:validstate s) (ic:iCmp) (cp:CProvider) (u:uri) (pt:PType) , pre_revokeDel ic cp u pt s -> post_revokeDel ic cp u pt s s' -> validstate s'.
Proof.
    intros.
    unfold validstate.
    unfold pre_revokeDel in H.
    unfold post_revokeDel in H0.
    destruct H0 as [verifeid H0].
    destruct_conj H0.
    
    unfold allCmpDifferent.
    split.
    intros.
    
    
    apply (inAppS'InAppS a1 s) in H14;auto.
    apply (inAppS'InAppS a2 s) in H16;auto.
    apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
    
    
    unfold notRepeatedCmps.
    split.
    intros.
    apply (inAppS'InAppS a1 s) in H14;auto.
    apply (inAppS'InAppS a2 s) in H16;auto.
    apply (inAppSameCmp s sValid c a1 a2);auto.
    
    
    unfold notCPrunning.
    split.
    rewrite <-H12.
    destructVS sValid.
    auto.
    
    
    split.
    unfold delTmpRun.
    intros.
    specialize (H1 ic0 cp0 u0 pt0 H14).
    destruct H1.
    destruct H1.
    destructVS sValid.
    destruct (delTmpRunVS ic0 cp0 u0 x);auto.
    split.
    destruct H17.
    exists x0.
    apply (inAppS'InAppS x0 s);auto.
    destruct H18.
    destruct H18.
    destruct H18.
    exists x0,x1.
    split.
    apply (inAppS'InAppS x1 s);auto.
    rewrite<-H12;auto.
    
    split.
    apply (cmpRunAppInsS' s);auto.
    
    split.
    apply (resContAppInstS' s);auto.
    
    split.
    apply (consistencyUnchanged s);auto.
    
    unfold notDupApp.
    split.
    rewrite <- H8.
    rewrite<-H9.
    destructVS sValid.
    auto.
    
    unfold notDupSysApp.
    split.
    rewrite <-H8.
    destructVS sValid.
    auto.
    
    
    split.
    apply (notDupPermS' s);auto.
    
    unfold allMapsCorrect.
    split.
    rewrite <-H8, <-H10, <-H11, <- H12, <-H13.
    repeat (split;auto; try mapcorrect sValid).
    
    
    split.
    apply (grantedPermsExistS' s);auto.

    unfold noDupSentIntents.
    rewrite<- H15.
    destructVS sValid.
    auto.
Qed.



End RevokeDelInv.

