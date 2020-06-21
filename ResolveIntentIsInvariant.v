(* En este archivo se demuestra que la ejecución de
*  la acción resolveIntent preserva los invariantes del sistema *)
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
Require Import EqTheorems.

Section ResolveIntentInv.

    
Lemma ResolveIntentIsInvariant : forall (s s':System) (sValid:validstate s) (intt:Intent) (a:idApp) , pre_resolveIntent intt a s -> post_resolveIntent intt a s s' -> validstate s'.
Proof.
    intros.
    unfold validstate.
    unfold pre_resolveIntent in H.
    unfold post_resolveIntent in H0.
    destruct H0 as [verified H0].
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
    rewrite <- H0.
    rewrite<-H2.
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
    rewrite <-H0, <-H3, <-H4, <- H5, <-H6, <-H7, <-H9.
    repeat (split;auto; try mapcorrect sValid).
    
    split.    
    apply (grantedPermsExistS' s);auto.


    unfold implicitToExplicitIntent in H1.

    unfold noDupSentIntents;intros.
    destruct H1.
    destruct H1.
    destruct_conj H1.
    assert (H15' := H15).
    specialize (H15 i ic H8).
    specialize (H15' i' ic' H10).

    clear H H1 H17 H14.

    destructVS sValid.

    destruct H15.
    destruct H.
    destruct H15'.
    destruct H14.
    apply sentIntentsCorrectVS;auto.
    destruct H14.
    destruct_conj H14.
    rewrite H11 in H1.
    rewrite <- H16 in H1.
    contradiction.
    destruct H15'.
    destruct H1.
    destruct H.
    destruct_conj H.
    rewrite <- H11 in H14.
    rewrite<- H16 in H14.
    contradiction.
    destruct H.
    destruct H1.
    destruct_conj H.
    destruct_conj H1.

    assert (ic=ic' /\ x1=x2).
    apply sentIntentsCorrectVS;auto.
    rewrite H1;auto.
    destruct H33.
    split;auto.
    rewrite H35 in *.

    rewrite <-H16 in H26.
    rewrite H17 in H27.
    rewrite H18 in H28.
    rewrite H19 in H29.
    rewrite H20 in H30.
    rewrite H21 in H31.
    rewrite H22 in H32.
    rewrite H24 in H34.

    destruct i;simpl in *.
    destruct i';simpl in *.
    rewrite H11 ,H26 ,H27 ,H28 ,H29 ,H30 ,H31 ,H32 ,H34.
    auto.


Qed.



End ResolveIntentInv.

