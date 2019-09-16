(* En este archivo se demuestra que la ejecución de
*  la acción uninstall preserva los invariantes del sistema *)
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

Section UninstallInv.


Lemma UnInAppS'InAppS : forall (a a1:idApp) (s s':System) (rapp : removeApp a s s') (sysimgs : systemImage (environment s) = systemImage (environment s')) (c1 : Cmp) (inapps' : inApp c1 a1 s'), inApp c1 a1 s.
Proof.
    intros.
    destruct inapps'.
    destruct H.
    unfold inApp.
    exists x;split;auto.
    destruct H.
    left.
    destruct rapp.
    destruct_conj H2.
    destruct H4.
    destruct_conj H5.
    apply H4;auto.
    right.
    destruct H.
    destruct_conj H.
    rewrite sysimgs in *.
    exists x0;auto.
Qed.

Lemma inAppSMaybeS' : forall (s s' : System) (x : Cmp) (a x0 : idApp) (H15 : inApp x x0 s) (H2 : removeApp a s s') (H9 : systemImage (environment s) = systemImage (environment s')), inApp x x0 s' \/ a=x0.
Proof.
    intros.
    destruct H15.
    destruct H.
    destruct H.
    destruct H2.
    destruct_conj H2.
    destruct H4.
    destruct_conj H5.
    specialize (H7 x0 x1 H).
    destruct H7.
    left.
    unfold inApp.
    exists x1.
    split;auto.
    auto.
    left.
    unfold inApp.
    destruct H.
    destruct_conj H.
    exists x1.
    split;auto.
    right.
    rewrite <-H9.
    exists x2;auto.
Qed.


Lemma isAppInstalledSMaybeS' : forall (s s' : System) (a x0 : idApp) (H15 : isAppInstalled x0 s) (H2 : removeApp a s s') (H9 : systemImage (environment s) = systemImage (environment s')), isAppInstalled x0 s' \/ a=x0.
Proof.
    intros.
    destruct H15.
    destruct H2.
    destruct_conj H1.
    specialize (H2 x0 H).
    unfold isAppInstalled.
    destruct H2;auto.
    left.
    unfold isAppInstalled.
    rewrite H9 in *.
    auto.
Qed.

Lemma scGen : forall (s s': System)(X Y:Set) (a a0 : idApp) (f1 : System -> X) (f2 : X -> mapping idApp Y) (H10 : forall a' : idApp, In a' (apps (state s')) -> In a' (apps (state s))) (H2 : forall a' : idApp, In a' (apps (state s)) -> In a' (apps (state s')) \/ a' = a) (H12 : ~ In a (apps (state s'))) (H14 : forall (a' : idApp) (m' : Y), map_apply idApp_eq (f2 (f1 s')) a' = Value idApp m' -> map_apply idApp_eq (f2 (f1 s)) a' = Value idApp m') (H13 : forall (a' : idApp) (m' : Y), map_apply idApp_eq (f2 (f1 s)) a' = Value idApp m' -> map_apply idApp_eq (f2 (f1 s')) a' = Value idApp m' \/ a = a') (H16 : ~ is_Value (map_apply idApp_eq (f2 (f1 s')) a)) (YSC: In a0 (apps (state s)) <-> (exists m : Y, map_apply idApp_eq (f2 (f1 s)) a0 = Value idApp m)), In a0 (apps (state s')) <-> (exists m : Y, map_apply idApp_eq (f2 (f1 s')) a0 = Value idApp m).
Proof.
    split;intros.
    specialize (H10 a0 H).
    destruct YSC.
    specialize (H0 H10).
    destruct H0.
    exists x.
    specialize (H13 a0 x H0).
    destruct H13; auto.
    rewrite H3 in *.
    contradiction.
    destruct YSC.
    destruct H.
    specialize (H14 a0 x H).
    assert (In a0 (apps (state s))).
    apply H1.
    exists x;auto.
    specialize (H2 a0 H3).
    destruct H2;auto.
    rewrite H2 in *.
    unfold is_Value in H16.
    rewrite H in H16.
    destruct H16;auto.
Qed.

Lemma defPermsS' : forall (s s' : System) (a : idApp) (H4 : removeDefPerms a s s') (H9 : systemImage (environment s) = systemImage (environment s')) (a0 : idApp) (l : list Perm) (H10 : defPermsForApp s' a0 l), defPermsForApp s a0 l.
Proof.
    intros.
    unfold defPermsForApp.
    destruct H10.
    left.
    destruct H4.
    apply H0.
    auto.
    right.
    rewrite H9;auto.
Qed.

Lemma UninstallIsInvariant : forall (s s':System) (sValid:validstate s) (a:idApp) ,pre_uninstall a s -> post_uninstall a s s' -> validstate s'.
Proof.
    intros.
    unfold validstate.
    unfold post_uninstall in H0.
    unfold pre_uninstall in H.
    destruct H.
    destruct_conj H0.
    
    unfold allCmpDifferent.
    split.
    intros.
    apply (UnInAppS'InAppS a a1 s) in H10;auto.
    apply (UnInAppS'InAppS a a2 s) in H12;auto.
    apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
    
    
    unfold notRepeatedCmps.
    split.
    intros.
    apply (UnInAppS'InAppS a a1 s) in H10;auto.
    apply (UnInAppS'InAppS a a2 s) in H12;auto.
    apply (inAppSameCmp s sValid c a1 a2);auto.
    
    
    unfold notCPrunning.
    split.
    rewrite <-H8.
    destructVS sValid.
    auto.
    
    unfold delTmpRun.
    split.
    rewrite <- H8.
    intros.
    destruct H6.
    specialize (H6 ic cp u pt H10).
    destruct H12.
    destructVS sValid.
    unfold delTmpRun in delTmpRunVS.
    specialize (delTmpRunVS ic cp u pt H6).
    destruct delTmpRunVS.
    destruct H15.
    destruct H15.
    destruct H15.
    destruct H14.
    split.
    exists x1;auto.
    assert ( inApp (cmpCP cp) x1 s' \/ a=x1).
    apply (inAppSMaybeS' s);auto.
    destruct H17;auto.
    destruct H13.
    rewrite <-H17 in *.
    specialize (H13 ic cp u pt H14).
    unfold is_Value in H13.
    rewrite H10 in H13.
    destruct H13.
    auto.
    exists x, x0.
    split;auto.
    assert ( inApp x x0 s' \/ a=x0).
    apply (inAppSMaybeS' s);auto.
    destruct H17;auto.
    rewrite <-H17 in *.
    specialize (H1 ic x H16).
    contradiction.
    
    
    
    
    unfold cmpRunAppIns.
    split.
    rewrite <- H8.
    intros.
    assert (sV2:=sValid).
    destructVS sValid.
    unfold cmpRunAppIns in cmpRunAppInsVS.
    specialize (cmpRunAppInsVS ic c H10).
    destruct cmpRunAppInsVS.
    exists x.
    assert ( inApp c x s' \/ a=x).
    apply (inAppSMaybeS' s);auto.
    destruct H13;auto.
    rewrite <-H13 in *.
    specialize (H1 ic c H10).
    contradiction.
    
    
    unfold resContAppInst.
    split.
    intros.
    destruct H5.
    destruct_conj H12.
    specialize (H5 a0 r v H10).
    specialize (H13 a0 r v H5).
    assert (isAppInstalled a0 s).
    apply NNPP;unfold not;intros.
    absurd (is_Value (map_apply rescontdomeq (resCont (state s)) (a0,r))).
    apply notInstalledNoResCont;auto.
    unfold is_Value.
    rewrite H5;auto.
    assert (isAppInstalled a0 s' \/ a=a0).
    apply (isAppInstalledSMaybeS' s);auto.
    destruct H16;auto.
    rewrite <- H16 in *.
    specialize (H12 r).
    unfold is_Value in H12.
    rewrite H10 in H12.
    destruct H12;auto.
    
    
    unfold statesConsistency.
    split.
    split.
    unfold removeApp in H2.
    destruct_conj H2.
    unfold removeManifest in H13.
    destruct_conj H13.
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    apply (scGen s s' Environment Manifest a);auto.
    
    split.
    unfold removeApp in H2.
    destruct_conj H2.
    unfold removeCert in H15.
    destruct_conj H15.
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    apply (scGen s s' Environment Cert a);auto.
    
    split.
    unfold removeApp in H2.
    destruct_conj H2.
    unfold removeDefPerms in H4.
    destruct_conj H4.
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    apply (scGen s s' Environment (list Perm) a);auto.
    
    split.
    unfold removeApp in H2.
    destruct_conj H2.
    unfold revokePerms in H0.
    destruct_conj H0.
    assert (sValid2 := sValid).
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    assert (sameimg:=H9).
    assert (awasinstalled := H).
    clear allCmpDiffVS notRepCompsVS notCPRunningVS delTmpRunVS cmpRunAppInsVS resContAppInstVS notDupSysAppVS notDupPermVS allMapsCorrectVS grantedPermsExistVS H H1 H13 H15 H18 H3 H4 H5 H6 H7 H8 H9 H11 mfstSC certSC defPermsSC grantedPermGroupsSC .
    destruct permsSC.
    split;intros.
    assert (In a0 (apps (state s)) \/ (exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a0)).
    rewrite sameimg.
    destruct H3.
    left.
    apply H10.
    auto.
    right.
    auto.
    specialize (H H4).
    destruct H.
    specialize (H0 a0 x H).
    destruct H0.
    destruct H0.
    destruct H0.
    exists x0;auto.
    rewrite H0 in *.
    destruct H3.
    contradiction.
    destruct H3.
    rewrite<- sameimg in *.
    assert (~(In a0 (apps (state s)) /\ In x0 (systemImage (environment s)) /\ idSI x0 = a0)).
    apply sysAppInApps;auto.
    destruct H5.
    split;auto.


    destruct H3.
    specialize (H14 a0 x H3).
    destruct H14.
    assert ( In a0 (apps (state s)) \/ (exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a0)).
    apply H1.
    exists x0;auto.
    destruct H5.
    specialize (H2 a0 H5).
    destruct H2;auto.
    rewrite H2 in *.
    unfold is_Value in H16.
    rewrite H3 in H16.
    destruct H16;auto.
    right.
    rewrite<- sameimg;auto.
    
    


    unfold removeApp in H2.
    destruct_conj H2.
    unfold revokePermGroups in H3.
    destruct_conj H3.
    assert (sValid2 := sValid).
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    assert (sameimg:=H9).
    assert (awasinstalled := H).
    clear allCmpDiffVS notRepCompsVS notCPRunningVS delTmpRunVS cmpRunAppInsVS resContAppInstVS notDupSysAppVS notDupPermVS allMapsCorrectVS grantedPermsExistVS H H1 H13 H15 H18 H0 H4 H5 H6 H7 H8 H9 H11 mfstSC certSC defPermsSC permsSC.
    destruct grantedPermGroupsSC.
    split;intros.
    assert (In a0 (apps (state s)) \/ (exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a0)).
    rewrite sameimg.
    destruct H1.
    left.
    apply H10.
    auto.
    right.
    auto.
    specialize (H H4).
    destruct H.
    specialize (H3 a0 x H).
    destruct H3.
    exists x;auto.
    rewrite H3 in *.
    destruct H1.
    contradiction.
    destruct H1.
    rewrite<- sameimg in *.
    assert (~(In a0 (apps (state s)) /\ In x0 (systemImage (environment s)) /\ idSI x0 = a0)).
    apply sysAppInApps;auto.
    destruct H5.
    split;auto.


    destruct H1.
    specialize (H14 a0 x H1).
    assert ( In a0 (apps (state s)) \/ (exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a0)).
    apply H0.
    exists x;auto.
    destruct H4.
    specialize (H2 a0 H4).
    destruct H2;auto.
    rewrite H2 in *.
    unfold is_Value in H16.
    rewrite H1 in H16.
    destruct H16;auto.
    right.
    rewrite<- sameimg;auto.
    





    
    unfold notDupApp.
    split.
    intros.
    rewrite <-H9.
    destruct H2.
    specialize (H2 a0 H10).
    unfold not;intros.
    destruct H13.
    destruct (sysAppInApps s sValid a0 x);auto.
    
    
    unfold notDupSysApp.
    split.
    rewrite <-H9.
    destructVS sValid.
    auto.
    
    unfold notDupPerm.
    split.
    intros.
    assert (defPermsForApp s a0 l).
    apply (defPermsS' s s' a);auto.
    assert (defPermsForApp s a' l').
    apply (defPermsS' s s' a);auto.
    apply (notDupPermVS s sValid a0 a' p p' l l');auto.
    
    
    unfold allMapsCorrect.
    split.
    destruct H2.
    destruct_conj H10.
    destruct H13, H15, H0, H3, H4, H5, H6, H7.
    destruct_conj H14.
    destruct_conj H16.
    destruct_conj H17.
    destruct_conj H18.
    destruct_conj H19.
    destruct_conj H20.
    destruct_conj H21.
    destruct_conj H22.
    mapcorrect sValid.
    rewrite <-H8.
    repeat (split;auto).
    
    unfold grantedPermsExist.
    split.
    intros.
    destruct H0.
    specialize (H0 a0 l H10).
    destruct H0.
    destruct_conj H13.
    specialize (H14 a0 x H0).
    destruct H14.
    destruct H14.
    destruct H14.
    rewrite H10 in H14.
    inversion H14.
    rewrite <- H18 in *.
    assert (exists defPermsA, map_apply idApp_eq (defPerms (environment s)) a = Value idApp defPermsA).
    apply (ifInAppThenDefPerms);auto.
    destruct H17.
    specialize (H15 x1 p H17).
    destruct H15.
    specialize (H19 H12).
    destruct H19.
    assert (permExists p s).
    apply (grantedPermsExistVS s sValid a0 p x);auto.
    unfold permExists.
    destruct H21.
    left;auto.
    right.
    unfold usrDefPerm.
    destruct H21.
    destruct H21.
    destruct H21.
    destruct H21.
    destruct H4.
    destruct_conj H23.
    specialize (H24 x2 x3 H21).
    destruct H24.
    left.
    exists x2, x3;auto.
    rewrite <-H24 in *.
    rewrite H21 in H17.
    inversion H17.
    rewrite H27 in *;contradiction.
    right.
    rewrite <- H9;auto.
    unfold is_Value in H13.
    rewrite<-H14 in *.
    rewrite H10 in H13.
    destruct H13;auto.

    unfold noDupSentIntents.
    rewrite<- H11.
    destructVS sValid.
    auto.
Qed.




End UninstallInv.

