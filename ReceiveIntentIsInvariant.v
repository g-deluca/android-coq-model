Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Import Classical.
Require Import Estado.
Require Import DefBasicas.
Require Import EqTheorems.
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

Section ReceiveIntentInv.

Lemma sameTPermsDelTmpRun : forall (s s' : System) (sValid : validstate s) (ic0 : iCmp) (cp : CProvider) (u : uri) (pt : PType) (addrun : forall (ic' : iCmp) (c' : Cmp), map_apply iCmp_eq (running (state s)) ic' = Value iCmp c' -> map_apply iCmp_eq (running (state s')) ic' = Value iCmp c') (samedeltperms: map_apply deltpermsdomeq (delTPerms (state s)) (ic0, cp, u) = Value (iCmp * CProvider * uri) pt) (sameenv : environment s = environment s') , (exists a1 : idApp, inApp (cmpCP cp) a1 s') /\ (exists (c : Cmp) (a0 : idApp), inApp c a0 s' /\ map_apply iCmp_eq (running (state s')) ic0 = Value iCmp c).
Proof.
    intros.
    assert ( (exists a1 : idApp, inApp (cmpCP cp) a1 s) /\ (exists (c : Cmp) (a0 : idApp), inApp c a0 s /\ map_apply iCmp_eq (running (state s)) ic0 = Value iCmp c)).
    destructVS sValid.
    unfold delTmpRun in delTmpRunVS.
    apply (delTmpRunVS ic0 cp u pt);auto.
    destruct H.
    destruct H.
    destruct H0.
    destruct H0.
    destruct H0.
    split.
    exists x.
    apply (inAppS'InAppS x s);auto.
    exists x0,x1.
    split.
    apply (inAppS'InAppS x1 s);auto.
    apply addrun;auto.
Qed.


    
Lemma ReceiveIntentIsInvariant : forall (s s':System) (sValid:validstate s) (intt:Intent) (ic:iCmp) (a:idApp) , pre_receiveIntent intt ic a s -> post_receiveIntent intt ic a s s' -> validstate s'.
Proof.
    intros.
    unfold validstate.
    unfold pre_receiveIntent in H.
    unfold post_receiveIntent in H0.
    destruct_conj H0.
    assert (verified := H9). clear H9.
    assert (H8 := H7). clear H7.
    
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
    destruct H1.
    destruct H1.
    destruct_conj H1.
    destruct H10.
    destruct_conj H13.
    intros.
    specialize (H15 ic0 c H16).
    destruct H15.
    apply (notCPRunningVS s sValid ic0);auto.
    destruct H15.
    rewrite H18 in *;auto.
    
    
    split.
    unfold delTmpRun.
    destruct H1.
    destruct H1.
    destruct_conj H1.
    destruct H10.
    destruct_conj H13.
    intros.
    destruct (intType intt).
    assert (intActivity=intActivity);auto.
    specialize (H11 H18).
    destruct H11.
    destruct H11.
    destruct H11.
    destruct_conj H11.
    destruct H21.
    destruct_conj H20.
    specialize (H20 ic0 cp u pt H16).
    destruct H20.
    apply (sameTPermsDelTmpRun s s' sValid ic0 cp u pt);auto.
    destruct_conj H20.
    rewrite <- H23, H20, H25 in *.
    destruct H11.
    destruct H11.
    split.
    exists x3.
    apply (inAppS'InAppS x3 s);auto.
    exists x0.
    destruct H7.
    destruct H28.
    exists a.
    split.
    apply (inAppS'InAppS a s);auto.
    auto.
    
    destruct H11.
    rewrite <- H19 in *.
    apply (sameTPermsDelTmpRun s s' sValid ic0 cp u pt);auto.
    
    assert (intService=intService);auto.
    specialize (H12 H18).
    rewrite <- H12 in *.
    apply (sameTPermsDelTmpRun s s' sValid ic0 cp u pt);auto.
    
    assert (intBroadcast=intBroadcast);auto.
    specialize (H14 H18).
    rewrite <- H14 in *.
    apply (sameTPermsDelTmpRun s s' sValid ic0 cp u pt);auto.
    
    split.
    unfold cmpRunAppIns.
    intros.
    destruct H1.
    destruct H1.
    destruct_conj H1.
    destruct H11.
    destruct H14.
    specialize (H14 ic0 c H7).
    destruct H14.
    apply ifRunningThenInApp in H14;auto.
    destruct H14.
    exists x1.
    apply (inAppS'InAppS x1 s);auto.
    destruct H14.
    rewrite <- H14, H17 in *.
    destruct H9.
    destruct H18.
    exists a.
    apply (inAppS'InAppS a s);auto.
    
    split.
    apply (resContAppInstS' s);auto.
    
    split.
    apply (consistencyUnchanged s);auto.
    
    unfold notDupApp.
    split.
    rewrite <- H2.
    rewrite<-H3.
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
    destruct H1.
    destruct H1.
    destruct_conj H1.
    destruct H10.
    destruct_conj H13.
    rewrite <-H2, <-H4, <- H5, <-H6, <-H8.
    destruct (intType intt).
    
    assert (intActivity=intActivity);auto.
    specialize (H11 H16).
    destruct H11.
    destruct H11.
    destruct H11.
    destruct_conj H11.
    destruct H20.
    repeat (split;auto; try mapcorrect sValid).
    destruct H11.
    rewrite<-H18.
    repeat (split;auto; try mapcorrect sValid).
    
    assert (intService=intService);auto.
    specialize (H12 H16).
    rewrite<-H12.
    repeat (split;auto; try mapcorrect sValid).
    
    assert (intBroadcast=intBroadcast);auto.
    specialize (H14 H16).
    rewrite<-H14.
    repeat (split;auto; try mapcorrect sValid).
    
    split.
    apply (grantedPermsExistS' s);auto.

    clear H H1.
    unfold removeIntent in H0.
    unfold noDupSentIntents;intros.
    destruct H0.
    assert (H0':=H0).
    specialize (H0 i ic0 H).
    specialize (H0' i' ic' H1).
    destructVS sValid.
    apply sentIntentsCorrectVS;auto.



Qed.



End ReceiveIntentInv.

