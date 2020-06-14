(* En este archivo se demuestra la corrección de la acción receiveIntent *)
Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Export ListAuxFuns.
Require Import Classical.
Require Import Estado.
Require Import DefBasicas.
Require Import Semantica.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.
Require Import ValidStateLemmas.
Require Export Coq.Arith.PeanoNat.
Import PeanoNat.Nat.

Section VerifyOldApp.

Lemma verifyOldAppCorrect : forall (s:System) (a:idApp) (sValid: validstate s),
    (pre (verifyOldApp a) s) -> post_verifyOldApp a s (verifyOldApp_post a s).
Proof.
    simpl.
    unfold pre_verifyOldApp, post_verifyOldApp.
    intros.
    destruct_conj H.
    unfold verifyOldApp_post.
    repeat split; auto; simpl.
  - intros a' lPerm' H3.
    elim (classic (a=a')); intros.
    rewrite H1 in H3.
    rewrite <- addAndApply in H3.
    inversion H3.
    destructVS sValid.
    destructSC statesConsistencyVS a'.
    clear certSC defPermsSC grantedPermGroupsSC.

    assert (In a' (apps (state s)) \/
          (exists sysapp : SysImgApp,
             In sysapp (systemImage (environment s)) /\ idSI sysapp = a')).
    rewrite <- H1. auto.
    apply permsSC in H4.
    destruct H4 as [lPerm H4].
    exists lPerm. split; auto.
    intros. inversion H6.

    rewrite overrideNotEq in H3; auto.
    exists lPerm'. auto.
  - intros a' lPerm H3.
    elim (classic (a=a')); intros.
    exists nil. rewrite H1.
    split. rewrite <- addAndApply. auto.
    intros; auto.

    exists lPerm.
    rewrite overrideNotEq.
    split. auto.
    intros. contradiction. auto.

  - rewrite <- addAndApply. auto.

  - apply addPreservesCorrectness.
    apply permsCorrect;auto.

  - intros a' lGroup' H3.
    elim (classic (a=a')); intros.
    rewrite H1 in H3.
    rewrite <- addAndApply in H3.
    inversion H3.
    destructVS sValid.
    destructSC statesConsistencyVS a'.
    clear mfstSC certSC defPermsSC permsSC.

    assert (In a' (apps (state s)) \/
          (exists sysapp : SysImgApp,
             In sysapp (systemImage (environment s)) /\ idSI sysapp = a')).
    rewrite <- H1. auto.
    apply grantedPermGroupsSC in H4.
    destruct H4 as [lPerm H4].
    exists lPerm. split; auto.
    intros. inversion H6.

    rewrite overrideNotEq in H3; auto.
    exists lGroup'. auto.

  - intros a' lGroup H3.
    elim (classic (a=a')); intros.
    exists nil. rewrite H1.
    split. rewrite <- addAndApply. auto.
    intros; auto. 

    exists lGroup.
    rewrite overrideNotEq.
    split. auto.
    intros. contradiction. auto.

  - rewrite <- addAndApply. auto.

  - apply addPreservesCorrectness.
    apply grantedPermGroupsCorrect;auto.

  - intros a' H1. right. auto.

  - intros. destruct H1; auto.

  - auto.
Qed.

Lemma notPreVerifyThenError : forall (s : System) (a : idApp),
  ~ pre (verifyOldApp a) s -> validstate s ->
    exists ec : ErrorCode,
      response (step s (verifyOldApp a)) = error ec /\
      ErrorMsg s (verifyOldApp a) ec /\ s = system (step s (verifyOldApp a)).
Proof.
    intros. simpl in H.
    simpl. unfold verifyOldApp_safe, verifyOldApp_pre.
    case_eq (negb (isAppInstalledBool a s)); intros; simpl.

    exists no_such_app.
    split; auto. split; auto.
    unfold not. intros.
    rewrite negb_true_iff in H1.
    apply isAppInstalled_iff in H2.
    rewrite H1 in H2. inversion H2.

    case_eq (InBool idApp idApp_eq a (alreadyRun (state s))); intros; simpl.

    exists already_verified.
    repeat split;auto.
    unfold InBool in H2.
    rewrite existsb_exists in H2.
    destruct H2 as [a' [H2 H3]].
    destruct (idApp_eq a a').
    rewrite e. auto.
    inversion H3.

    case_eq (negb (isOldAppBool a s)); intros; simpl.

    exists no_verification_needed.
    repeat split;auto.
    unfold not. intros.
    rewrite negb_true_iff in H3.
    apply isOld_isOldBool in H4.
    rewrite H3 in H4. inversion H4.
    auto.

    destruct H.
    unfold pre_verifyOldApp.
    rewrite negb_false_iff in H1.
    split.
  - rewrite isAppInstalled_iff. auto.
  - split.
 -- unfold not. intros.
    apply (In_InBool idApp idApp_eq) in H.
    rewrite H2 in H. inversion H.
 -- rewrite negb_false_iff in H3.
    apply isOldBool_isOld.
    auto. auto.
Qed.

Lemma verifyOldAppIsSound : forall (s:System) (a:idApp),
        validstate s -> exec s (verifyOldApp a) (system (step s (verifyOldApp a))) (response (step s (verifyOldApp a))).
Proof.
    intros s a vs.
    unfold exec.
    split; auto.
    elim (classic (pre (verifyOldApp a) s));intro.
  - left. assert (verifyOldApp_pre a s = None).
    unfold verifyOldApp_pre.
    destruct H. destruct H0.
    rewrite isAppInstalled_iff in H.
    rewrite <- negb_false_iff in H.
    rewrite H.
    case_eq (InBool idApp idApp_eq a (alreadyRun (state s))); intros.
    unfold InBool in H2.
    apply existsb_exists in H2. destruct H2 as [a' [H2 H3]].
    destruct (idApp_eq a a').
    rewrite <- e in H2. contradiction.
    inversion H3.
    clear H2.
    apply isOld_isOldBool in H1.
    rewrite <- negb_false_iff in H1.
    rewrite H1. auto. auto.

    simpl.
    unfold verifyOldApp_safe;simpl.
    rewrite H0. simpl.
    split; auto.
    split; auto.
    apply verifyOldAppCorrect;auto.
  - right. apply notPreVerifyThenError; auto.
Qed.

End VerifyOldApp.