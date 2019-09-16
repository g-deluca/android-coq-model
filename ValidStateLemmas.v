(* En este archivo se definen lemas que cumplen
*  los estados válidos y se utilizan en las pruebas *)
Require Import Implementacion.
Require Import DefBasicas.
Require Import EqTheorems.
Require Import Estado.
Require Import Semantica.
Require Import Maps.
Require Import MyList.
Require Import Coq.Lists.List.
Require Import Classical.
Require Import Tacticas.
Require Import RuntimePermissions.
Require Import ListAuxFuns.
Require Import Omega.

Section VSLemmas.

Lemma ifManifestThenInApps : forall (s : System) (sValid : validstate s) (a : idApp) (m : Manifest), map_apply idApp_eq (manifest (environment s)) a = Value idApp m -> In a (apps (state s)).
Proof.
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply mfstSC.
    exists m.
    auto.
Qed.

Lemma ifInAppsThenManifest : forall (s : System) (sValid : validstate s) (a : idApp), In a (apps (state s)) -> exists m : Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m.
Proof.
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply mfstSC;auto.
Qed.

Lemma ifRunningThenInApp : forall (s : System) (sValid : validstate s) (c:Cmp) (ic:iCmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c -> (exists a:idApp, inApp c a s).
Proof.
    intros.
    destructVS sValid.
    exact (cmpRunAppInsVS ic c H).
Qed.

Lemma inAppSameCmpId : forall (s : System) (sValid : validstate s) (c c':Cmp) (a a':idApp), inApp c a s -> inApp c' a' s -> getCmpId c = getCmpId c' -> c=c'.
Proof.
    intros.
    destructVS sValid.
    unfold allCmpDifferent in allCmpDiffVS.
    apply (allCmpDiffVS c c' a a' H H0 H1).
Qed.

Lemma inAppSameCmp: forall (s : System) (sValid : validstate s) (c :Cmp) (a a':idApp), inApp c a s -> inApp c a' s -> a=a'.
Proof.
    intros.
    destructVS sValid.
    unfold notRepeatedCmps in notRepCompsVS.
    apply (notRepCompsVS c);auto.
Qed.

Lemma sysAppInApps : forall (s : System) (sValid : validstate s) (a:idApp) (sysapp:SysImgApp), ~(In a (apps (state s)) /\ In sysapp (systemImage (environment s)) /\ idSI sysapp = a).
Proof.
    intros.
    destructVS sValid.
    unfold notDupApp in notDupAppVS.
    specialize (notDupAppVS a).
    unfold not;intros.
    destruct H.
    apply notDupAppVS.
    auto.
    exists sysapp.
    auto.
Qed.

Lemma notDupSysAppVS : forall (s : System) (sValid : validstate s) (sysapp sysapp':SysImgApp), In sysapp (systemImage (environment s)) -> In sysapp' (systemImage (environment s)) -> idSI sysapp = idSI sysapp' -> sysapp=sysapp'.
Proof.
    intros.
    destructVS sValid.
    unfold notDupSysApp in notDupSysAppVS.
    apply notDupSysAppVS.
    auto.
Qed.

Lemma ifInAppThenDefPerms : forall (s : System) (sValid : validstate s) (a : idApp), In a (apps (state s)) -> exists l : list Perm, map_apply idApp_eq (defPerms (environment s)) a = Value idApp l.
Proof.
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply defPermsSC.
    auto.
Qed.

Lemma ifDefPermsThenInApps : forall (s : System) (sValid : validstate s) (a : idApp) (l : list Perm), map_apply idApp_eq (defPerms (environment s)) a = Value idApp l -> In a (apps (state s)).
Proof.
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply defPermsSC.
    exists l;auto.
Qed.

Lemma ifCertThenInApps : forall (s : System) (sValid : validstate s) (a : idApp) (c : Cert), map_apply idApp_eq (cert (environment s)) a = Value idApp c -> In a (apps (state s)).
Proof.
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply certSC.
    exists c;auto.
Qed.

Lemma ifInAppThenCert : forall (s : System) (sValid : validstate s) (a : idApp), In a (apps (state s)) -> exists c : Cert, map_apply idApp_eq (cert (environment s)) a = Value idApp c.
Proof.
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply certSC.
    auto.
Qed.

Lemma notDupPermVS : forall (s:System) (sValid : validstate s) (a a':idApp) (p p':Perm) (l l':list Perm), defPermsForApp s a l -> defPermsForApp s a' l' -> In p l -> In p' l' -> idP p = idP p' -> (p=p' /\ a=a').
Proof.
    intro.
    intro.
    destructVS sValid.
    unfold notDupPerm in notDupPermVS.
    auto.
Qed.

Lemma runningCorrect : forall (s:System) (sValid:validstate s), map_correct (running (state s)).
Proof.
    intros.
    destructVS sValid.
    unfold allMapsCorrect in allMapsCorrectVS.
    destruct_conj allMapsCorrectVS.
    auto.
Qed.

Lemma delTPermsCorrect : forall (s:System) (sValid:validstate s), map_correct (delTPerms (state s)).
Proof.
    intros.
    destructVS sValid.
    unfold allMapsCorrect in allMapsCorrectVS.
    destruct_conj allMapsCorrectVS.
    auto.
Qed.

Lemma delPPermsCorrect : forall (s:System) (sValid:validstate s), map_correct (delPPerms (state s)).
Proof.
    intros.
    destructVS sValid.
    unfold allMapsCorrect in allMapsCorrectVS.
    destruct_conj allMapsCorrectVS.
    auto.
Qed.

Lemma resContCorrect : forall (s:System) (sValid:validstate s), map_correct (resCont (state s)).
Proof.
    intros.
    destructVS sValid.
    unfold allMapsCorrect in allMapsCorrectVS.
    destruct_conj allMapsCorrectVS.
    auto.
Qed.

Lemma permsCorrect : forall (s:System) (sValid:validstate s), map_correct (perms (state s)).
Proof.
    intros.
    destructVS sValid.
    unfold allMapsCorrect in allMapsCorrectVS.
    destruct_conj allMapsCorrectVS.
    auto.
Qed.

Lemma grantedPermGroupsCorrect : forall (s:System) (sValid:validstate s), map_correct (grantedPermGroups (state s)).
Proof.
    intros.
    destructVS sValid.
    unfold allMapsCorrect in allMapsCorrectVS.
    destruct_conj allMapsCorrectVS.
    auto.
Qed.

Lemma notInstalledNoResCont : forall (s : System) (sValid : validstate s) (a:idApp) (r:res), ~ (isAppInstalled a s) -> ~(is_Value (map_apply rescontdomeq (resCont (state s)) (a,r))).
Proof.
    intros.
    assert (sV := sValid).
    destructVS sValid.
    unfold resContAppInst in resContAppInstVS.
    unfold not;intros.
    unfold is_Value in H0.
    case_eq (map_apply rescontdomeq (resCont (state s)) (a, r));intros.
    specialize (resContAppInstVS a r v H1).
    destruct H;auto.
    rewrite H1 in H0.
    destruct H0.
Qed.

Lemma ifDelTPermsThenRunning : forall (s : System) (sValid : validstate s) (ic:iCmp) (cp:CProvider) (u:uri) (pt:PType), map_apply deltpermsdomeq (delTPerms (state s)) (ic, cp, u) = Value (iCmp*CProvider*uri) pt -> exists c:Cmp, map_apply iCmp_eq (running (state s)) ic = Value iCmp c.
Proof.
    intros.
    destructVS sValid.
    destruct (delTmpRunVS ic cp u pt);auto.
    destruct H1.
    destruct H1.
    destruct H1.
    exists x.
    auto.
Qed.

Lemma ifPermsThenInApp : forall (s : System) (sValid : validstate s) (a : idApp) (l : list Perm), map_apply idApp_eq (perms (state s)) a = Value idApp l -> (In a (apps (state s))) \/ (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a).
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply permsSC.
    exists l;auto.
Qed.

Lemma ifInAppsThenGrantedGroups: forall (s : System) (sValid : validstate s) (a : idApp), In a (apps (state s)) -> exists v : list idGrp, map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp v.
Proof.
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply grantedPermGroupsSC;auto.
Qed.

Lemma ifInAppsOrSysAppThenGrantedGroups: forall (s : System) (sValid : validstate s) (a : idApp), In a (apps (state s)) \/ (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a) -> exists v : list idGrp, map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp v.
Proof.
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply grantedPermGroupsSC;auto.
Qed.

Lemma ifInAppsThenPerms: forall (s : System) (sValid : validstate s) (a : idApp), In a (apps (state s)) -> exists l : list Perm, map_apply idApp_eq (perms (state s)) a = Value idApp l.
Proof.
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply permsSC;auto.
Qed.

Lemma ifInAppsOrSysAppThenPerms: forall (s : System) (sValid : validstate s) (a : idApp), In a (apps (state s)) \/ (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a) -> exists l : list Perm, map_apply idApp_eq (perms (state s)) a = Value idApp l.
Proof.
    intros.
    destructVS sValid.
    destructSC statesConsistencyVS a.
    apply permsSC;auto.
Qed.

Lemma grantedPermsExistVS : forall (s : System) (sValid : validstate s) (a : idApp) (p:Perm) (l : list Perm), map_apply idApp_eq (perms (state s)) a = Value idApp l -> In p l -> permExists p s.
Proof.
    intro.
    intro.
    destructVS sValid.
    auto.
Qed.

Lemma notCPRunningVS : forall (s : System) (sValid : validstate s) (ic:iCmp)(c:Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c ->  ~isCProvider c.
Proof.
    intro.
    intro.
    destructVS sValid.
    auto.
Qed.

End VSLemmas.
