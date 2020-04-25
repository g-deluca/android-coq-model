(* En este archivo se demuestra que la ejecución de
*  la acción startActivity preserva los invariantes del sistema *)
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

Section StartActivityInv.

    
Lemma StartActivityIsInvariant : forall (s s':System) (sValid:validstate s) (intt:Intent) (ic:iCmp), pre_startActivity intt ic s -> post_startActivity intt ic s s' -> validstate s'.
Proof.
    intro.
    intro.
    intro.
    intro.
    intro.
    intro preS.
    intro.
    unfold validstate.
    unfold post_startActivity in H.
    destruct H.
    unfold onlyIntentsChanged in H0.
    destruct_conj H0.
    
    unfold allCmpDifferent.
    split.
    intros.
    
    
    apply (inAppS'InAppS a1 s) in H7;auto.
    apply (inAppS'InAppS a2 s) in H9;auto.
    apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
    
    
    unfold notRepeatedCmps.
    split.
    intros.
    apply (inAppS'InAppS a1 s) in H7;auto.
    apply (inAppS'InAppS a2 s) in H9;auto.
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
    
    split.
    apply (consistencyUnchanged s);auto.
    
    unfold notDupApp.
    split.
    rewrite <- H0.
    rewrite<-H1.
    destructVS sValid.
    auto.
    
    unfold notDupSysApp.
    split.
    rewrite <-H1.
    destructVS sValid.
    auto.
    
    
    split.
    apply (notDupPermS' s);auto.
    
    unfold allMapsCorrect.
    split.
    rewrite <-H2, <-H3, <-H4, <- H5, <-H6, <-H8, <-H1.
    repeat (split;auto; try mapcorrect sValid).
    
    
    split.
    apply (grantedPermsExistS' s);auto.
    split.

    unfold noDupSentIntents.
    intros.
    destruct preS.
    destruct_conj H12.
    unfold addIntent in H.
    destruct_conj H.
    assert (H':=H).
    specialize (H' i ic0 H7).
    assert (H'':=H).
    specialize (H'' i' ic' H9).
    clear H9 H7 H8 H6 H4 H5 H3 H2 H1 H0.
    destruct H'.
    destruct H''.
    destructVS sValid.
    apply sentIntentsCorrectVS;auto.
    destruct H1.
    destruct H15.
    exists i, ic0.
    split;auto.
    rewrite H10.
    unfold createIntent in H2.
    rewrite H2.
    simpl.
    auto.

    destruct H''.
    destruct H0.
    destruct H15.
    exists i', ic'.
    split;auto.
    rewrite<- H10.
    unfold createIntent in H2.
    rewrite H2.
    simpl.
    auto.
    destruct H0, H1.
    split.
    rewrite<- H0;auto.
    rewrite H3;auto.

    apply (individualInstanceOfGroupedPermS' s); auto.
Qed.



End StartActivityInv.

