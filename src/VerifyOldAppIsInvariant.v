Require Export Estado.
Require Export DefBasicas.
Require Export Semantica.
Require Import Tacticas.
Require Import ValidStateLemmas.
Require Import SameEnvLemmas.

Require Import Classical.

Lemma VerifyOldAppIsInvariant : forall (s s':System) (sValid:validstate s) (a:idApp),
  pre_verifyOldApp a s -> post_verifyOldApp a s s' -> validstate s'.
Proof.
  intros.
  unfold validstate.
  unfold pre_verifyOldApp in H.
  unfold post_verifyOldApp in H0.
  destruct_conj H.
  destruct_conj H0.
  split.

  unfold allCmpDifferent.
  intros.
  apply (inAppS'InAppS a1 s) in H11;auto.
  apply (inAppS'InAppS a2 s) in H13;auto.
  apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
  split.

  unfold notRepeatedCmps.
  intros.
  apply (inAppS'InAppS a1 s) in H11;auto.
  apply (inAppS'InAppS a2 s) in H13;auto.
  apply (inAppSameCmp s sValid c a1 a2);auto.
  split.

  unfold notCPrunning.
  rewrite <-H7.
  destructVS sValid.
  auto. split.

  apply (delTmpRunS' s);auto. split.

  apply (cmpRunAppInsS' s);auto. split.

  apply (resContAppInstS' s);auto. split.

  unfold statesConsistency.
  rewrite <- H5, <- H6.
  assert (sv2 := sValid). destructVS sValid.
  intros.
  destructSC statesConsistencyVS a0.
  repeat (split;intros; auto).

- apply permsSC in H11.
  destruct H11 as [lPerm H11].
  destruct H2 as [H2 H13]; destruct_conj H13.
  apply H14 in H11.
  destruct H11 as [lPerm' [H11 H17]].
  exists lPerm'; auto.
- destruct H11 as [lPerm' H11]. destruct H2.
  apply H2 in H11.
  destruct H11 as [lPerm [H11 _]].
  apply <- permsSC . exists lPerm;auto.
- apply grantedPermGroupsSC in H11.
  destruct H11 as [lGroup H11].
  destruct H0 as [H0 H13]; destruct_conj H13.
  apply H14 in H11.
  destruct H11 as [lGroup' [H11 _]].
  exists lGroup'; auto.
- destruct H11 as [lGroup' H11].
  destruct H0 as [H0 H13]; destruct_conj H13.
  apply H0 in H11.
  destruct H11 as [lGroup [H11 _]].
  apply <- grantedPermGroupsSC.
  exists lGroup; auto.
- assert (sv2 := sValid). destructVS sValid. split.
  unfold notDupApp.
  rewrite <- H5, <- H6.
  intros. auto. split.

  unfold notDupSysApp.
  rewrite <- H5.
  intros; auto. split.

  unfold notDupPerm.
  apply (notDupPermS' s);auto.
  split.

  unfold allMapsCorrect in *.
  destruct H2 as [H2 H13]; destruct_conj H13.
  destruct H0 as [H0 H16]; destruct_conj H16.
  rewrite <-H5, <-H7, <-H8, <-H9, <- H10.
  destruct_conj allMapsCorrectVS.
  repeat (split;auto). split.

  unfold grantedPermsExist.
  intros. destruct H2 as [H2 [H14 H15]].
  apply H2 in H11.
  destruct H11 as [lPerm [H11 H16]].
  apply (permExistsSpermExistsS' s);auto.
  apply H16 in H13.
  apply (grantedPermsExistVS a0 p lPerm); auto.

  unfold noDupSentIntents.
  rewrite <- H12.
  auto.
Qed.