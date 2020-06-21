(* En este archivo se demuestra que la ejecución de
*  la acción install preserva los invariantes del sistema *)
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

Section InstallInv.

Lemma has_dups_maps :forall (A B:Set) B_eq f (l:list A) (c1: A) (c2:A), has_duplicates B B_eq (map f l) = false -> In c1 l -> In c2 l -> f c1 = f c2 -> c1 = c2.
Proof.
    intros.
    induction l.
    inversion H0.
    rewrite map_cons in H.
    unfold has_duplicates in H.
    apply orb_false_iff in H.
    destruct H.
    fold has_duplicates in H3.
    inversion H0.
    rewrite <-H4 in *.
    unfold InBool in H.
    apply NNPP.
    unfold not;intros.
    rewrite <-not_true_iff_false in H.
    inversion H1.
    apply H5;auto.
    apply H.
    rewrite existsb_exists.
    exists (f a).
    split.
    rewrite in_map_iff.
    exists c2;auto.
    destruct (B_eq (f a) (f a));auto.
    inversion H1.
    rewrite <-H5 in *.
    unfold InBool in H.
    apply NNPP.
    unfold not;intros.
    rewrite <-not_true_iff_false in H.
    apply H.
    rewrite existsb_exists.
    exists (f a).
    split.
    rewrite in_map_iff.
    exists c1;auto.
    destruct (B_eq (f a) (f a));auto.
    apply IHl;auto.
Qed.

Lemma inAppS' : forall s s' : System, validstate s -> forall (a : idApp) (m : Manifest), ~ isAppInstalled a s -> has_duplicates idCmp idCmp_eq (map getCmpId (cmp m)) = false -> (forall c : Cmp, In c (cmp m) -> cmpNotInState c s) -> (forall (a' : idApp) (m' : Manifest), map_apply idApp_eq (manifest (environment s)) a' = Value idApp m' -> map_apply idApp_eq (manifest (environment s')) a' = Value idApp m') -> (forall (a' : idApp) (m' : Manifest), map_apply idApp_eq (manifest (environment s')) a' = Value idApp m' -> map_apply idApp_eq (manifest (environment s)) a' = Value idApp m' \/ a = a') -> map_apply idApp_eq (manifest (environment s')) a = Value idApp m -> (forall a' : idApp, In a' (apps (state s)) -> In a' (apps (state s'))) -> (forall a' : idApp, In a' (apps (state s')) -> In a' (apps (state s)) \/ a' = a) /\ In a (apps (state s')) -> systemImage (environment s) = systemImage (environment s') -> forall (c1 : Cmp) (a1 : idApp), inApp c1 a1 s' -> inApp c1 a1 s \/ a = a1 /\ In c1 (cmp m).
Proof.
    intros.
    destruct H9.
    destruct H9.
    destruct H9.
    specialize (H4 a1 x H9).
    destruct H4.
    left.
    unfold inApp.
    exists x.
    split;auto.
    right.
    rewrite H4 in *.
    rewrite H9 in H5.
    inversion H5.
    rewrite H12 in *.
    auto.
    left.
    unfold inApp.
    exists x.
    rewrite H8 in *.
    auto.
Qed.

Lemma ifInAppSThenInAppS': forall (s s':System) (sValid:validstate s) (a x:idApp) (c:Cmp) (m:Manifest) , systemImage (environment s) = systemImage (environment s') -> addManifest m a s s' -> addApp a s s' -> inApp c x s -> inApp c x s'.
Proof.
    intros.
    unfold inApp.
    destruct H2.
    destruct H2.
    exists x0.
    split;auto.
    destruct H2.
    left.
    destruct H0.
    apply H0;auto.
    right.
    rewrite <-H;auto.
Qed.


Lemma ifExistsResSThenExistsResS': forall (s s':System) (sValid:validstate s) (a:idApp) (cp:CProvider) (u:uri) (m:Manifest) (lRes:list res) (addRes2 : addRes a lRes s s') , systemImage (environment s) = systemImage (environment s') -> addManifest m a s s' -> addApp a s s' -> existsRes cp u s -> existsRes cp u s'.

Proof.
    intros.
    unfold existsRes.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H3.
    destruct H4.
    exists x.
    split.
    apply (ifInAppSThenInAppS' s s' sValid a x (cmpCP cp) m);auto.
    exists x0.
    split;auto.
    destruct addRes2.
    exists x1.
    apply H5;auto.
Qed.


Lemma isAppInstSThenS': forall (s s':System) (a a0:idApp), addApp a s s' -> systemImage (environment s) = systemImage (environment s') -> isAppInstalled a0 s -> isAppInstalled a0 s'.
Proof.
    intros.
    unfold isAppInstalled.
    destruct H1.
    left.
    destruct H.
    apply H;auto.
    right.
    rewrite <-H0.
    auto.
Qed.


Lemma stateConsGen : forall (s s' : System) (X Y:Set) (a : idApp) (m : Y) (f1 : System -> X) (f2 : X -> mapping idApp Y), (forall (a' : idApp) (m' : Y), map_apply idApp_eq (f2 (f1 s)) a' = Value idApp m' -> map_apply idApp_eq (f2 (f1 s')) a' = Value idApp m') -> (forall (a' : idApp) (m' : Y), map_apply idApp_eq (f2 (f1 s')) a' = Value idApp m' -> map_apply idApp_eq (f2 (f1 s)) a' = Value idApp m' \/ a = a') -> map_apply idApp_eq (f2 (f1 s')) a = Value idApp m -> addApp a s s' -> forall a0 : idApp, (In a0 (apps (state s)) <-> (exists m0 : Y, map_apply idApp_eq (f2 (f1 s)) a0 = Value idApp m0)) -> (In a0 (apps (state s')) <-> (exists m0 : Y, map_apply idApp_eq (f2 (f1 s')) a0 = Value idApp m0)).
Proof.
    split;intros; destruct H2; destruct H5.
    specialize (H5 a0 H4).
    destruct H5.
    destruct H3.
    specialize (H3 H5).
    destruct H3.
    exists x.
    apply H.
    auto.
    exists m.
    rewrite H5.
    auto.
    destruct H4.
    specialize (H0 a0 x H4).
    destruct H0.
    destruct H3.
    apply H2.
    apply H7.
    exists x;auto.
    rewrite H0 in *.
    auto.
Qed.



Lemma stateConsGen2 : forall (s s' : System) (X Y:Set) (a : idApp) (m : Y) (f1 : System -> X) (f2 : X -> mapping idApp Y), (forall (a' : idApp) (m' : Y), map_apply idApp_eq (f2 (f1 s)) a' = Value idApp m' -> map_apply idApp_eq (f2 (f1 s')) a' = Value idApp m') -> (forall (a' : idApp) (m' : Y), map_apply idApp_eq (f2 (f1 s')) a' = Value idApp m' -> map_apply idApp_eq (f2 (f1 s)) a' = Value idApp m' \/ a = a') -> map_apply idApp_eq (f2 (f1 s')) a = Value idApp m -> addApp a s s' -> forall a0 : idApp, (In a0 (apps (state s)) \/ (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a0) <-> (exists m0 : Y, map_apply idApp_eq (f2 (f1 s)) a0 = Value idApp m0)) ->
systemImage (environment s) = systemImage (environment s')
    -> (In a0 (apps (state s')) \/ (exists sysapp:SysImgApp, In sysapp (systemImage (environment s')) /\ idSI sysapp = a0) <-> (exists m0 : Y, map_apply idApp_eq (f2 (f1 s')) a0 = Value idApp m0)).
Proof.
    split;intros; destruct H2; destruct H5.
    destruct H6.


    specialize (H6 a0 H5).
    destruct H6.
    destruct H3.
    assert ( In a0 (apps (state s)) \/ (exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a0)).
    left;auto.
    specialize (H3 H9).
    destruct H3.
    exists x.
    apply H.
    auto.
    exists m.
    rewrite H6.
    auto.
    destruct H5.
    assert ( In a0 (apps (state s)) \/ (exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a0)).
    right.
    rewrite H4.
    exists x;auto.
    destruct H3.
    specialize (H3 H7).
    destruct H3.
    specialize (H a0 x0 H3).
    exists x0;auto.

    specialize (H0 a0 x H5).
    destruct H0.
    destruct H3.
    rewrite<- H4 in *.
    assert ( In a0 (apps (state s)) \/ (exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a0)).
    apply H7.
    exists x;auto.
    destruct H8;auto.
    destruct H6.
    rewrite H0 in *.
    left;auto.
Qed.

Lemma defPermsS': forall s s' : System, validstate s -> forall (a : idApp) (m : Manifest), has_duplicates idCmp idCmp_eq (map getCmpId (cmp m)) = false -> addManifest m a s s' -> (forall (a' : idApp) (lPerm : list Perm), map_apply idApp_eq (defPerms (environment s)) a' = Value idApp lPerm -> map_apply idApp_eq (defPerms (environment s')) a' = Value idApp lPerm) -> (forall (a' : idApp) (lPerm : list Perm), map_apply idApp_eq (defPerms (environment s')) a' = Value idApp lPerm -> map_apply idApp_eq (defPerms (environment s)) a' = Value idApp lPerm \/ a = a') -> forall x : list Perm, map_apply idApp_eq (defPerms (environment s')) a = Value idApp x -> (forall p : Perm, In p (usrP m) /\ ~ isSystemPermId p <-> In p x) -> addApp a s s' -> systemImage (environment s) = systemImage (environment s') -> forall (a0 : idApp) (l : list Perm), defPermsForApp s' a0 l -> defPermsForApp s a0 l \/ a0 = a /\ l = x.
Proof.
    intros.
    destruct H8.
    specialize (H3 a0 l H8).
    destruct H3.
    left.
    unfold defPermsForApp.
    left.
    auto.
    right.
    rewrite H3 in *.
    rewrite H8 in H4.
    inversion H4.
    auto.
    left.
    unfold defPermsForApp.
    right.
    rewrite H7.
    auto.
Qed.

Lemma permWasDef: forall s s' : System, validstate s -> forall (a : idApp) (m : Manifest), authPerms m s -> forall x : list Perm, map_apply idApp_eq (defPerms (environment s')) a = Value idApp x -> (forall p : Perm, In p (usrP m) /\ ~ isSystemPermId p <-> In p x) -> forall (a0 : idApp) (p p' : Perm) (l : list Perm), In p l -> In p' x -> idP p = idP p' -> defPermsForApp s a0 l -> p = p' /\ a0 = a.
Proof.
    intros.
    specialize (H2 p').
    destruct H2.
    specialize (H7 H4).
    destruct H7.
    destruct (H0 p');auto.
    exists p.
    split;auto.
    unfold usrDefPerm.
    destruct H6.
    left.
    exists a0, l;auto.
    right.
    destruct H6.
    destruct_conj H6.
    rewrite <-H6 in *.
    exists x0;auto.
Qed.


Lemma InstallIsInvariant : forall (s s':System) (sValid:validstate s) (a:idApp) (m:Manifest) (c:Cert) (lRes: list res),pre_install a m c lRes s -> post_install a m c lRes s s' -> validstate s'.
Proof.
    intros.
    unfold validstate.
    unfold post_install in H0.
    destruct H0 as [verified H0].
    unfold pre_install in H.
    destruct H.
    destruct H1.
    destruct H2 as [nodupperm H3].
    destruct_conj H3.
    destruct_conj H0.
    
    unfold allCmpDifferent.
    split.
    clear H3 H5 H0 H6 H8 H9 H10 H11 H12 H15 nodupperm.
    destruct H7.
    intros.
    destruct H4.
    destruct H8.
    destruct H9.
    clear H10.
    assert (inApp c1 a1 s \/ (a=a1 /\ In c1 (cmp m))).
    
    apply (inAppS' s s');auto.
    assert (inApp c2 a2 s \/ (a=a2 /\ In c2 (cmp m))).
    
    apply (inAppS' s s');auto.
    destruct H10.
    destruct H11.
    apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
    destruct H11.
    rewrite<- H11 in *.
    specialize (H2 c2 H12).
    unfold cmpNotInState in H2.
    absurd (getCmpId c2 = getCmpId c1).
    apply (H2 c1 a1);auto.
    auto.
    
    destruct H11.
    destruct H10.
    specialize (H2 c1 H12).
    unfold cmpNotInState in H2.
    absurd (getCmpId c1 = getCmpId c2).
    apply (H2 c2 a2);auto.
    auto.
    
    destruct H11.
    destruct H10.
    apply (has_dups_maps Cmp idCmp idCmp_eq getCmpId (cmp m));auto.
    
    
    unfold notRepeatedCmps.
    split.
    clear H3 c lRes H0 H6 H8 H9 H10 H11 H12 H15.
    intros.
    destruct H7.
    destruct H4.
    destruct H8.
    destruct H9.
    clear H10.
    assert (inApp c a2 s \/ (a=a2 /\ In c (cmp m))).
    apply (inAppS' s s');auto.
    assert (inApp c a1 s \/ (a=a1 /\ In c (cmp m))).
    apply (inAppS' s s');auto.
    destruct H10.
    destruct H11.
    apply (inAppSameCmp s sValid c);auto.
    destruct H11.
    rewrite <-H11 in *.
    specialize (H2 c H12).
    unfold cmpNotInState in H2.
    specialize (H2 c a2 H10).
    destruct H2.
    auto.
    destruct H10.
    destruct H11.
    specialize (H2 c H12).
    unfold cmpNotInState in H2.
    specialize (H2 c a1 H11).
    destruct H2.
    auto.
    destruct H11.
    rewrite <-H10.
    auto.
    
    unfold notCPrunning.
    split.
    rewrite <-H10.
    destructVS sValid.
    auto.
    
    unfold delTmpRun.
    split.
    rewrite <-H12.
    rewrite <- H10.
    intros.
    assert (sV2:=sValid).
    destructVS sValid.
    unfold delTmpRun in delTmpRunVS.
    specialize (delTmpRunVS ic cp u pt H14).
    destruct delTmpRunVS.
    destruct H16.
    destruct H17.
    destruct H17.
    destruct H17.
    apply ifDelTPermsThenRunning in H14;auto.
    split.
    exists x.
    apply (ifInAppSThenInAppS' s s' sV2 a x (cmpCP cp) m);auto.
    exists x0.
    exists x1.
    split;auto.
    apply (ifInAppSThenInAppS' s s' sV2 a x1 x0 m);auto.
    
    
    unfold cmpRunAppIns.
    split.
    rewrite <- H10.
    intros.
    assert (sV2:=sValid).
    destructVS sValid.
    unfold cmpRunAppIns in cmpRunAppInsVS.
    specialize (cmpRunAppInsVS ic c0 H14).
    destruct cmpRunAppInsVS.
    exists x.
    apply (ifInAppSThenInAppS' s s' sV2 a x c0 m);auto.
    
    
    unfold resContAppInst.
    split.
    assert (sV2:=sValid).
    assert (addRes2:=H8).
    destruct H8.
    destruct H14.
    intros.
    specialize (H14 a0 r v H17).
    destruct H14.
    destructVS sValid.
    unfold resContAppInst in resContAppInstVS.
    specialize (resContAppInstVS a0 r v).
    specialize (resContAppInstVS H14).
    apply (isAppInstSThenS' s s' a);auto.
    destruct_conj H14.
    rewrite H18 in *.
    unfold isAppInstalled.
    left.
    destruct H7.
    destruct H19.
    auto.
    
    unfold statesConsistency.
    split.
    split.
    unfold addManifest in H4.
    destruct_conj H4.
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    apply (stateConsGen s s' Environment Manifest a m);auto.
    
    split.
    unfold addCert in H0.
    destruct_conj H0.
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    apply (stateConsGen s s' Environment Cert a c);auto.
    
    split.
    unfold addDefPerms in H6.
    destruct_conj H6.
    clear H18.
    destruct H16.
    destruct_conj H16.
    destructVS sValid.
    destructSC statesConsistencyVS a0.
    apply (stateConsGen s s' Environment (list Perm) a x);auto.
    
    unfold initializePermLists in H9.
    destruct_conj H9.
    clear H20 H22.
    destructVS sValid.
    destructSC statesConsistencyVS a0.
split.

    apply (stateConsGen2 s s' State (list Perm) a nil);auto.
    intros.
    specialize (H9 a' m' H20).
    destruct H9;try destruct H9;auto.
    
    apply (stateConsGen2 s s' State (list idGrp) a nil);auto.
    intros.
    specialize (H18 a' m' H20).
    destruct H18;try destruct H18;auto.
    
    
    unfold notDupApp.
    split.
    intros.
    destruct H7.
    destruct H16.
    specialize (H16 a0 H14).
    rewrite <-H13.
    destruct H16.
    unfold not;intros.
    destruct H18.
    destruct (sysAppInApps s sValid a0 x);auto .
    rewrite H16 in *.
    unfold not;intros.
    apply H.
    unfold isAppInstalled.
    right;auto.
    
    
    unfold notDupSysApp.
    split.
    rewrite <-H13.
    destructVS sValid.
    auto.
    
    unfold notDupPerm.
    split.
    intros.
    destruct H6.
    destruct H20.
    destruct H21.
    clear H22.
    destruct H21.
    destruct H21.
    assert (defPermsForApp s a0 l \/ a0=a /\ l=x).
    apply (defPermsS' s s' sValid a m);auto.
    assert (defPermsForApp s a' l' \/ a'=a /\ l'=x).
    apply (defPermsS' s s' sValid a m);auto.
    
    
    destruct H23.
    destruct H24.
    apply (notDupPermVS s sValid a0 a' p p' l l');auto.
    destruct H24.
    rewrite H24, H25 in *.
    apply (permWasDef s s' sValid a m H3 x H21 H22 a0 p p' l);auto.
    destruct H23.
    rewrite H23 in *.
    rewrite H25 in *.
    destruct H24.
    assert (p'=p /\ a'=a).
    apply (permWasDef s s' sValid a m H3 x H21 H22 a' p' p l');auto.
    destruct H26;auto.
    destruct H24.
    rewrite H24 in *.
    split;auto.
    rewrite H26 in *.
    assert (H22Bis:=H22).
    specialize (H22 p').
    destruct H22.
    specialize (H27 H18).
    destruct H27.
    specialize (H22Bis p).
    destruct H22Bis.
    specialize (H30 H17).
    destruct H30.
    apply (has_dups_maps Perm idPerm idPerm_eq idP (usrP m));auto.
    
    
    unfold allMapsCorrect.
    split.
    destruct H4.
    destruct_conj H14.
    destruct H0.
    destruct_conj H17.
    destruct H6.
    destruct_conj H20.
    destruct H8.
    destruct_conj H23.
    destruct H9.
    destruct_conj H26.
    mapcorrect sValid.
    rewrite H10, H11,H12 in *.
    repeat (split;auto).
    
    unfold grantedPermsExist.
    split.
    destruct H9.
    destruct_conj H14.
    intros.
    specialize (H16 a0 l H21).
    destruct H16.
    assert (permExists p s).
    apply (grantedPermsExistVS s sValid a0 p l);auto.
    unfold permExists.
    destruct H24.
    left;auto.
    right.
    unfold usrDefPerm.
    destruct H24.
    left.
    destruct H24.
    destruct H24.
    destruct H24.
    exists x, x0.
    split;auto.
    destruct H6.
    apply H6;auto.
    right.
    rewrite<- H13;auto.
    destruct H16.
    absurd (l=nil).
    apply inNotNilExists.
    exists p;auto.
    auto.

    unfold noDupSentIntents.
    rewrite<- H15.
    destructVS sValid.
    auto.
Qed.




End InstallInv.

