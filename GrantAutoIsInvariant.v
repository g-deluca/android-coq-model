Require Export Estado.
Require Export DefBasicas.
Require Export Semantica.
Require Import Tacticas.
Require Import ValidStateLemmas.
Require Import SameEnvLemmas.

Require Import Classical.

Lemma GrantAutoIsInvariant : forall (s s':System) (sValid:validstate s) (p:Perm) (a:idApp) ,pre_grantAuto p a s -> post_grantAuto p a s s' -> validstate s'.
Proof.
  intros.
  unfold validstate.
  unfold pre_grantAuto in H.
  unfold post_grantAuto in H0.
  destruct_conj H.
  destruct_conj H0.
  split.

  unfold allCmpDifferent.
  intros.
  apply (inAppS'InAppS a1 s) in H12;auto.
  apply (inAppS'InAppS a2 s) in H14;auto.
  apply (inAppSameCmpId s sValid c1 c2 a1 a2);auto.
  split.

  unfold notRepeatedCmps.
  intros.
  apply (inAppS'InAppS a1 s) in H12;auto.
  apply (inAppS'InAppS a2 s) in H14;auto.
  apply (inAppSameCmp s sValid c a1 a2);auto.
  split.

  unfold notCPrunning.
  rewrite <-H8.
  destructVS sValid.
  auto. split.

  apply (delTmpRunS' s);auto. split.

  apply (cmpRunAppInsS' s);auto. split.

  apply (resContAppInstS' s);auto. split.

  unfold statesConsistency.
  rewrite <- H0.
  rewrite <- H6.
  intros.
  assert (sv2:=sValid).
  destructVS sValid.
  destructSC statesConsistencyVS a0.
  repeat (split;intros; auto).
- destruct H4.
  apply permsSC in H12.
  destruct H12.
  apply H4 in H12.
  destruct H12. destruct H12.
  exists x0;auto.
- destruct H4 as [H4 [H14 H15]].
  destruct H12.
  apply H14 in H12.
  destruct H12 as [lPerm [H12 H16]].
  apply (ifPermsThenInApp s sv2 a0 lPerm);auto.
- rewrite <- H7.
  apply grantedPermGroupsSC in H12; auto.
- rewrite <- H7 in H12.
  destruct H12 as [lGroup H12].
  apply (ifGroupedPermsThenInApp s sv2 a0 lGroup). auto.
- assert (sv2 := sValid). destructVS sValid. split.

  unfold notDupApp.
  rewrite <- H0, <- H6.
  intros. auto. split.

  unfold notDupSysApp.
  rewrite <- H0.
  intros; auto. split.

  unfold notDupPerm.
  apply (notDupPermS' s);auto.
  split.

  unfold allMapsCorrect.
  rewrite <-H0, <-H7, <-H8, <-H9, <- H10, <- H11.
  unfold allMapsCorrect in allMapsCorrectVS.
  destruct_conj allMapsCorrectVS.
  repeat (split;auto; try mapcorrect sValid).
  unfold grantPerm in H4. destruct_conj H4. auto.
  split.

  unfold grantedPermsExist.
  intros. destruct H4 as [H4 [H15 H16]].
  apply H15 in H12.
  destruct H12 as [lPerm [H12 H17]].
  elim (classic (In p0 lPerm));intros.
+ apply (permExistsSpermExistsS' s); auto.
  apply (grantedPermsExistVS a0 p0 lPerm); auto.
+ specialize (H17 p0 H14 H18). destruct H17.
  rewrite <- H19.
  apply (permExistsSpermExistsS' s);auto.
+ unfold noDupSentIntents.
  rewrite <- H13.
  auto.
Qed.