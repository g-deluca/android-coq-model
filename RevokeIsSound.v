(* En este archivo se demuestra la corrección de la acción revoke *)
Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Export ListAuxFuns.
Require Import Classical.
Require Import Estado.
Require Import DefBasicas.
Require Import EqTheorems.
Require Import Semantica.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.
Require Import ValidStateLemmas.

Section Revoke.

Lemma postRevokeCorrect : forall (s:System) (a:idApp) (p:Perm), (pre (revoke p a) s) -> validstate s -> post_revoke p a s (revoke_post p a s).
Proof.
    intros.
    unfold post_revoke.
    simpl in H.
    unfold pre_revoke in H;simpl in H.
    destruct H.
    destruct H as [lPerm H2].
    destruct H2.

    split.
    unfold revokePerm.
    unfold revoke_post;unfold revokePermission;simpl.
    rewrite H.
    split;intros.
    elim (classic (a=a'));intros.
    exists lPerm.
    
    split.
    rewrite <- H4.
    auto.
    intros.
    rewrite <- H4 in H3.
    rewrite <-(addAndApply idApp_eq a (remove Perm_eq p lPerm) (perms (state s))) in H3.
    inversion H3.
    rewrite <- H7 in H5.
    apply removeSthElse in H5.
    destruct H5;auto.

    exists lPerm'.
    split.
    rewrite overrideNotEq in H3; auto.
    intros;auto.

    split;intros.
    elim (classic (a=a'));intros.
    exists (remove Perm_eq p lPerm).
    split.
    rewrite H4.
    symmetry.
    apply addAndApply.
    intros.
    split;auto.
    symmetry.
    apply (notInRemove Perm lPerm p' p Perm_eq ).
    rewrite H4 in H.
    rewrite H in H3.
    inversion H3.
    auto.
    auto.

    exists lPerm0.
    split.
    rewrite overrideNotEq.
    auto.
    auto.
    intros.
    contradiction.
    split.
    exists (remove Perm_eq p lPerm).
    split.
    symmetry.
    apply addAndApply.
    rewrite <-removeSthElse.
    unfold not;intros.
    destruct H3.
    apply H3;auto.
    apply addPreservesCorrectness.
    apply permsCorrect;auto.
    repeat (split;auto).
Qed.

Lemma notPreRevokeThenError : forall (s:System) (a:idApp) (p:Perm), ~(pre (revoke p a) s) -> validstate s -> exists ec : ErrorCode, response (step s (revoke p a)) = error ec /\ ErrorMsg s (revoke p a) ec /\ s = system (step s (revoke p a)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold revoke_safe, revoke_pre.
    case_eq (negb (InBool Perm Perm_eq p (grantedPermsForApp a s))); intros.
    simpl. exists perm_wasnt_granted. auto.
    case_eq (isSomethingBool idGrp (maybeGrp p)); intros.
    simpl. exists perm_is_grouped. split; auto. split; auto.
    unfold isSomethingBool in H2.
    destruct (maybeGrp p).
    exists i; auto. inversion H2.

    destruct H.
    unfold pre_revoke.
    split.
    rewrite negb_false_iff in H1.
    unfold InBool in H1.
    rewrite existsb_exists in H1.
    destruct H1 as [p' [H1 H3]].
    unfold grantedPermsForApp in H1.
    case_eq (map_apply idApp_eq (perms (state s)) a); intros.
    rewrite H in H1. exists l.
    destruct (Perm_eq p p'). rewrite e. auto.
    inversion H3.
    rewrite H in H1. inversion H1.
    unfold isSomethingBool in H2.
    destruct (maybeGrp p).
    inversion H2. auto.
Qed.

Lemma revokeIsSound : forall (s:System) (a:idApp) (p:Perm),
        validstate s -> exec s (revoke p a) (system (step s (revoke p a))) (response (step s (revoke p a))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (revoke p a) s));intro.
    left.
    assert(revoke_pre p a s = None).
    unfold revoke_pre.
    destruct H0.
    destruct H0.
    
    assert (InBool Perm Perm_eq p (grantedPermsForApp a s) = true).
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    split.
    destruct H0.
    unfold grantedPermsForApp.
    rewrite H0.
    auto.
    destruct Perm_eq; auto.
    rewrite H1.
    rewrite H2. simpl.
    auto.

    unfold step;simpl.
    unfold revoke_safe;simpl.
    rewrite H1;simpl.
    split;auto.
    split;auto.
    apply postRevokeCorrect;auto.
    right.
    apply notPreRevokeThenError;auto.
    
Qed.
End Revoke.
