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
    destruct H0 as [verified H0].
    unfold pre_grant in H.
    destruct H.
    destruct_conj H0.
    
    unfold allCmpDifferent.
    split.
  + intros.
    apply (inAppS'InAppS a1 s) in H10;auto.
    apply (inAppS'InAppS a2 s) in H12;auto.
    apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
  + unfold notRepeatedCmps.
    split. 
 ++ intros.
    apply (inAppS'InAppS a1 s) in H10;auto.
    apply (inAppS'InAppS a2 s) in H12;auto.
    apply (inAppSameCmp s sValid c a1 a2);auto.
 ++ unfold notCPrunning.
    split.

    rewrite <-H6.
    destructVS sValid.
    auto.

    split.
    apply (delTmpRunS' s);auto.

    split.
    apply (cmpRunAppInsS' s);auto.
   
    split.
    apply (resContAppInstS' s);auto.
  
    split.
+++ unfold statesConsistency.
    rewrite <- H4.
    rewrite <- H5.
    intros.
    assert (sv2:=sValid).
    destructVS sValid.
    destructSC statesConsistencyVS a0.


    repeat (split;intros; auto).
  - destruct H2.
    destruct permsSC.
    specialize (H13 H10).
    destruct H13.
    specialize (H2 a0 x H13).
    destruct H2.
    destruct H2.
    exists x0;auto.
  - destruct H10.
    destruct H2.
    destruct H12.
    specialize (H12 a0 x H10).
    destruct H12.
    destruct H12.
    apply (ifPermsThenInApp s sv2 a0 x0);auto.
  - elim (classic (maybeGrp p = None));intros.
    apply H3 in H12. rewrite <- H12. destruct grantedPermGroupsSC.
    apply H13 in H10. auto.
    apply (ifNotNoneThenSomething (maybeGrp p)) in H12.
    destruct H12. 
    apply (H0 x) in H12.
    destruct H12. destruct grantedPermGroupsSC.
    specialize (H14 H10).
    destruct H14.
    specialize (H12 a0 x0 H14).
    destruct H12. destruct H12.
    exists x1. auto.
  - destruct H10.    
    elim (classic (maybeGrp p = None));intros.
    apply H3 in H12.
    apply (ifGroupedPermsThenInApp s sv2 a0 x);auto.
    rewrite -> H12. auto.
    apply (ifNotNoneThenSomething (maybeGrp p)) in H12.

    destruct H12. 
    apply (H0 x0) in H12.
    destruct H12. destruct H13.
    specialize (H13 a0 x H10).
    destruct H13. destruct H13.
    destruct grantedPermGroupsSC.
    apply H17. exists x1. auto.
+++ unfold notDupApp.
    split.
    rewrite <- H5.
    rewrite <- H4.
    destructVS sValid.
    auto.
    
    unfold notDupSysApp.
    split.
    rewrite <-H4.
    destructVS sValid.
    auto.
    
    
    split.
    apply (notDupPermS' s);auto.
    
    unfold allMapsCorrect.
    split.
  - elim (classic (maybeGrp p = None));intros.
 -- apply H3 in H10.
    destruct H2.
    destruct_conj H12.
    rewrite <-H4, <-H10, <- H6, <-H7, <-H8, <-H9.
    repeat (split;auto; try mapcorrect sValid).
 -- apply (ifNotNoneThenSomething (maybeGrp p)) in H10.
    destruct H10. apply H0 in H10.
    destruct H10. destruct_conj H12.
    destruct H2. destruct_conj H14.
    rewrite <-H4, <- H6, <-H7, <-H8, <-H9.
    repeat (split;auto; try mapcorrect sValid).
  - unfold grantedPermsExist.
    split.
 -- intros.
    destruct H2.
    destruct_conj H13.
    specialize (H14 a0 l H10).
    destruct H14.
    destruct H14.
    specialize (H2 a0 x H14).
    destruct H2.
    destruct H2.
    rewrite H10 in H2.
    inversion H2.
    rewrite <- H19 in *.
    specialize (H15 p0 H12).
    elim (classic (In p0 x));intros.
    apply (permExistsSpermExistsS' s);auto.
    apply (grantedPermsExistVS s sValid a0 p0 x); auto.
    specialize (H15 H18).
    destruct H15.
    rewrite <- H20.
    apply (permExistsSpermExistsS' s);auto.
    destruct H1.
    auto.
 -- unfold noDupSentIntents.
    rewrite<- H11.
    destructVS sValid.
    auto.
Qed.



End GrantInv.

