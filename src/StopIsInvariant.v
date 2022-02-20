(* En este archivo se demuestra que la ejecución de
*  la acción stop preserva los invariantes del sistema *)
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

Section StopInv.



    
Lemma StopIsInvariant : forall (s s':System) (sValid:validstate s) (ic:iCmp), pre_stop ic s -> post_stop ic s s' -> validstate s'.
Proof.
    intros.
    unfold validstate.
    unfold pre_stop in H.
    unfold post_stop in H0.
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
    intros.
    apply (notCPRunningVS s sValid ic0).
    apply H1;auto.
    
    
    
    split.
    unfold delTmpRun.
    intros.
    specialize (H4 ic0 cp u pt H14).
    destructVS sValid.
    unfold delTmpRun in delTmpRunVS.
    apply (delTmpRunVS ic0 cp u pt) in H4;auto.
    destruct H4.
    destruct H4.
    destruct H16.
    destruct H16.
    destruct H16.
    specialize (H0 ic0 x0 H17).
    split.
    exists x.
    apply (inAppS'InAppS x s);auto.
    destruct H0.
    exists x0, x1.
    split; auto.
    apply (inAppS'InAppS x1 s);auto.
    rewrite<-H0 in *.
    specialize (H6 cp u).
    destruct H6.
    unfold is_Value.
    rewrite H14.
    auto.
    
    
    split.
    unfold cmpRunAppIns.
    intros.
    specialize (H1 ic0 c H14).
    apply ifRunningThenInApp in H1;auto.
    destruct H1.
    exists x.
    apply (inAppS'InAppS x s);auto.
    
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
    rewrite <-H8, <-H10, <- H11, <-H12, <-H13.
    repeat (split;auto; try mapcorrect sValid).
    split.
    apply (grantedPermsExistS' s);auto.

    unfold noDupSentIntents.
    rewrite<- H15.
    destructVS sValid.
    auto.
Qed.



End StopInv.

