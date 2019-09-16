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
    
    split.
    destruct H.
    unfold revokePerm.
    unfold revoke_post;unfold revokePermission;simpl.
    rewrite H.
    split;intros.
    elim (classic (a=a'));intros.
    exists x.
    
    split.
    rewrite<- H3.
    auto.
    intros.
    rewrite<- H3 in H2.
    rewrite <-(addAndApply idApp_eq a (remove Perm_eq p x) (perms (state s))) in H2.
    inversion H2.
    rewrite<- H6 in H4.
    assert (p'<>p /\ In p' x).
    apply removeSthElse in H4.
    auto.
    destruct H5;auto.
    
    exists lPerm'.
    split.
    rewrite overrideNotEq in H2.
    auto.
    auto.
    intros.
    auto.
    
    
    split;intros.
    elim (classic (a=a'));intros.
    exists (remove Perm_eq p x).
    split.
    rewrite H3.
    symmetry.
    apply addAndApply.
    intros.
    split;auto.
    symmetry.
    apply (notInRemove Perm x p' p Perm_eq ).
    rewrite H3 in H.
    rewrite H in H2.
    inversion H2.
    auto.
    auto.
    
    
    exists lPerm.
    split.
    rewrite overrideNotEq.
    auto.
    auto.
    intros.
    contradiction.
    split.
    exists (remove Perm_eq p x).
    split.
    symmetry.
    apply addAndApply.
    rewrite <-removeSthElse.
    unfold not;intros.
    destruct H2.
    apply H2;auto.
    apply addPreservesCorrectness.
    apply permsCorrect;auto.
    
    repeat (split;auto).
Qed.

Lemma notPreRevokeThenError : forall (s:System) (a:idApp) (p:Perm), ~(pre (revoke p a) s) -> validstate s -> exists ec : ErrorCode, response (step s (revoke p a)) = error ec /\ ErrorMsg s (revoke p a) ec /\ s = system (step s (revoke p a)).
Proof.
    intros.
    simpl.
    simpl in H.
    exists perm_wasnt_granted.
    assert (revoke_pre p a s=Some perm_wasnt_granted).
    unfold revoke_pre.
    assert (negb (InBool Perm Perm_eq p (grantedPermsForApp a s))=true).
    rewrite negb_true_iff.
    rewrite<- not_true_iff_false.
    unfold not;intros.
    apply H.
    unfold InBool in H1.
    rewrite existsb_exists in H1.
    destruct H1.
    destruct H1.
    unfold grantedPermsForApp in H1.
    destruct Perm_eq in H2.
    case_eq (map_apply idApp_eq (perms (state s)) a);intros;rewrite H3 in H1.
    exists l.
    rewrite e.
    auto.
    inversion H1.
    discriminate H2.
    rewrite H1;auto.
    unfold revoke_safe.
    rewrite H1.
    simpl.
    auto.
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
    
    assert (InBool Perm Perm_eq p (grantedPermsForApp a s) = true).
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    split.
    destruct H0.
    unfold grantedPermsForApp.
    rewrite H0.
    auto.
    destruct Perm_eq.
    auto.
    auto.
    rewrite H1.
    assert (negb true=false).
    rewrite negb_false_iff;auto.
    rewrite H2.
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
