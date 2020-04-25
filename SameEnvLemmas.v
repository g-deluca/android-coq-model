(* En este archivo se demuestran lemas que predican sobre sistemas con igual
* entorno y son utilizados en las demostraciones de invarianza y de las
* propiedades postuladas *)
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
Require Import RuntimePermissions.
Require Import Maps.
Require Import Tacticas.
Require Import MyList.
Require Import ListAuxFuns.
Require Import ValidStateLemmas.

Section SameEnvLemmas.

Lemma inAppS'InAppS : forall (a:idApp) (s s':System) (sameEnv :environment s = environment s') (c1 : Cmp),inApp c1 a s'<-> inApp c1 a s.
Proof.
    intros.
    unfold inApp.
    rewrite sameEnv.
    split;auto.
Qed.

Lemma existsResS'ExistsResS : forall (s s':System) (sameResCont:resCont (state s) = resCont (state s')) (sameEnv :environment s = environment s') (cp:CProvider) (u:uri),existsRes cp u s'<-> existsRes cp u s.
Proof.
    intros.
    unfold existsRes.
    rewrite sameResCont.
    split;intros;
    destruct H;
    destruct H;
    exists x;
    destruct H0;
    split.
    apply(inAppS'InAppS x s s');auto.
    exists x0;auto.
    apply(inAppS'InAppS x s s');auto.
    exists x0;auto.
Qed.

Lemma isMfstOfAppSS' : forall (a:idApp) (x:Manifest) (s s':System) (sameEnv :environment s = environment s'),isManifestOfApp a x s'<-> isManifestOfApp a x s.
Proof.
    intros.
    unfold isManifestOfApp.
    rewrite sameEnv.
    split;auto.
Qed.

Lemma appInstalledSAppInstalledS' : forall (a:idApp) (s s':System) (sameApps: apps (state s) = apps (state s')) (sameEnv :environment s = environment s') ,isAppInstalled a s'<-> isAppInstalled a s.
Proof.
    intros.
    unfold isAppInstalled.
    rewrite sameEnv, sameApps.
    split;auto.
Qed.


Lemma defPermsAppSdefPermsAppS' : forall (a:idApp) (s s':System) (sameEnv :environment s = environment s') (l:list Perm), defPermsForApp s' a l <-> defPermsForApp s a l.
Proof.
    intros.
    unfold defPermsForApp.
    rewrite sameEnv.
    split;auto.
Qed.

Lemma permExistsSpermExistsS' : forall (s s':System) (sameEnv :environment s = environment s') (p:Perm), permExists p s' <-> permExists p s.
Proof.
    intros.
    unfold permExists.
    unfold usrDefPerm.
    rewrite sameEnv.
    split;auto.
Qed.


Lemma delTmpRunS': forall (s s' : System) (sValid : validstate s) (H0 : environment s = environment s') (H3 : running (state s) = running (state s')) (H5 : delTPerms (state s) = delTPerms (state s')), delTmpRun s'.
Proof.
    intros.
    unfold delTmpRun.
    rewrite <- H5.
    intros.
    destructVS sValid.
    unfold delTmpRun in delTmpRunVS.
    specialize (delTmpRunVS ic cp u pt H).
    destruct delTmpRunVS.
    split.
    destruct H1.
    exists x.
    apply (inAppS'InAppS x s);auto.
    destruct H2.
    destruct H2.
    destruct H2.
    exists x,x0.
    rewrite <-H3.
    split;auto.
    apply (inAppS'InAppS x0 s);auto.
Qed.

Lemma cmpRunAppInsS': forall (s s' : System) (sValid : validstate s) (sameEnv : environment s = environment s') (sameRun : running (state s) = running (state s')) , cmpRunAppIns s'.
Proof.
    intros.
    unfold cmpRunAppIns.
    rewrite <- sameRun.
    intros.
    destructVS sValid.
    unfold cmpRunAppIns in cmpRunAppInsVS.
    specialize (cmpRunAppInsVS ic c H).
    destruct cmpRunAppInsVS.
    exists x.
    apply (inAppS'InAppS x s);auto.
Qed.

Lemma resContAppInstS' : forall (s s':System) (sValid:validstate s) (sameApps: apps (state s) = apps (state s')) (sameEnv :environment s = environment s') (sameResCont : resCont (state s) = resCont (state s')) , resContAppInst s'.
Proof.
    unfold resContAppInst.
    intros.
    rewrite <-sameResCont in H.
    assert (isAppInstalled a s).
    apply NNPP;unfold not;intros.
    absurd (is_Value (map_apply rescontdomeq (resCont (state s)) (a,r))).
    apply notInstalledNoResCont;auto.
    unfold is_Value.
    rewrite H;auto.
    apply (appInstalledSAppInstalledS' a s s');auto.
Qed.


Lemma notDupPermS': forall (s s' : System) (sValid : validstate s) (sameEnv : environment s = environment s'), notDupPerm s'.
Proof.
    unfold notDupPerm.
    intros.
    assert (defPermsForApp s a l).
    apply (defPermsAppSdefPermsAppS' a s');auto.
    assert (defPermsForApp s a' l').
    apply (defPermsAppSdefPermsAppS' a' s');auto.
    apply (notDupPermVS s sValid a a' p p' l l');auto.
Qed.


Lemma grantedPermsExistS' : forall (s s':System) (sValid:validstate s) (sameEnv :environment s = environment s') (samePerms: perms (state s) = perms (state s')), grantedPermsExist s'.
Proof.
    unfold grantedPermsExist.
    intros.
    apply (permExistsSpermExistsS' s);auto.
    rewrite <-samePerms in H.
    apply (grantedPermsExistVS s sValid a p l);auto.
Qed.

Lemma consistencyUnchanged : forall (s s':System) (sValid: validstate s) (sameEnv : environment s = environment s') (sameApps : apps (state s) = apps (state s')) (samePermGroups : grantedPermGroups (state s) = grantedPermGroups (state s')) (samePerms : perms (state s) = perms (state s')), statesConsistency s'.
Proof.
    intros.
    unfold statesConsistency.
    rewrite <-sameEnv, <- sameApps, <- samePermGroups, <- samePerms.
    destructVS sValid.
    intros.
    destructSC statesConsistencyVS a.
    auto.
Qed.

Lemma individualInstanceOfGroupedPermS' :
    forall (s s': System) (sValid: validstate s) (sameEnv: environment s = environment s')
        (samePerms: perms (state s) = perms (state s'))
            (sameGroups: grantedPermGroups (state s) = grantedPermGroups (state s')),
                individualInstanceOfGroupedPerm s'.
Proof.
intros.
unfold individualInstanceOfGroupedPerm; intros.
rewrite <- sameGroups in H.
destructVS sValid.
apply individualInstanceOfGroupedPermVS in H.
rewrite <- samePerms. auto.
Qed.


End SameEnvLemmas.
